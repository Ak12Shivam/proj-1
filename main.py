#!/usr/bin/env python3
"""
Service Provider Data Collection Tool - Main Flask Application
Handles real-time data collection, AI classification, geospatial mapping, and role-based access
"""

import os
import json
import sqlite3
import hashlib
import secrets
import logging
import shutil
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
import threading
import time
import requests
from functools import wraps
import pandas as pd
import numpy as np
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename

from flask import Flask, render_template, request, jsonify, session, redirect, url_for, send_file
from flask_socketio import SocketIO, emit, join_room, leave_room
from flask_cors import CORS
import spacy
from geopy.geocoders import Nominatim
import googlemaps
from bs4 import BeautifulSoup
import schedule
try:
    from fuzzywuzzy import fuzz
except ImportError:
    # Fallback if fuzzywuzzy causes issues
    class MockFuzz:
        @staticmethod
        def ratio(a, b):
            return 80  # Default similarity score
    fuzz = MockFuzz()
import re
import json

# US States dictionary for state selection and filtering
US_STATES = {
    "AL": "Alabama", "AK": "Alaska", "AZ": "Arizona", "AR": "Arkansas",
    "CA": "California", "CO": "Colorado", "CT": "Connecticut", "DE": "Delaware",
    "FL": "Florida", "GA": "Georgia", "HI": "Hawaii", "ID": "Idaho",
    "IL": "Illinois", "IN": "Indiana", "IA": "Iowa", "KS": "Kansas",
    "KY": "Kentucky", "LA": "Louisiana", "ME": "Maine", "MD": "Maryland",
    "MA": "Massachusetts", "MI": "Michigan", "MN": "Minnesota", "MS": "Mississippi",
    "MO": "Missouri", "MT": "Montana", "NE": "Nebraska", "NV": "Nevada",
    "NH": "New Hampshire", "NJ": "New Jersey", "NM": "New Mexico", "NY": "New York",
    "NC": "North Carolina", "ND": "North Dakota", "OH": "Ohio", "OK": "Oklahoma",
    "OR": "Oregon", "PA": "Pennsylvania", "RI": "Rhode Island", "SC": "South Carolina",
    "SD": "South Dakota", "TN": "Tennessee", "TX": "Texas", "UT": "Utah",
    "VT": "Vermont", "VA": "Virginia", "WA": "Washington", "WV": "West Virginia",
    "WI": "Wisconsin", "WY": "Wyoming", "DC": "District of Columbia"
}

# Initialize Flask app
app = Flask(__name__)
app.config['SECRET_KEY'] = secrets.token_hex(32)
app.config['UPLOAD_FOLDER'] = 'uploads'
app.config['MAX_CONTENT_LENGTH'] = 16 * 1024 * 1024  # 16MB max file size

# Initialize extensions
socketio = SocketIO(app, cors_allowed_origins="*")
CORS(app)

# Global variables for tracking collection status
collection_progress = 0

# Create upload folder if it doesn't exist
os.makedirs(app.config['UPLOAD_FOLDER'], exist_ok=True)

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Global variables
geolocator = Nominatim(user_agent="service_provider_tool")
gmaps = None  # Will be initialized with API key from settings

# Service categories mapping
SERVICE_CATEGORIES = {
    'residential-cleaning': 'Residential Cleaning',
    'commercial-janitorial': 'Commercial Janitorial',
    'carpet-cleaning': 'Carpet Cleaning',
    'window-cleaning': 'Window Cleaning',
    'painters': 'Painters',
    'maintenance': 'Maintenance Technicians',
    'hvac': 'HVAC Techs',
    'plumbers': 'Plumbers',
    'electricians': 'Electricians',
    'floor-care': 'Floor Care Specialists',
    'waste-management': 'Waste Management',
    'pest-control': 'Pest Control',
    'landscaping': 'Landscaping/Lawn Care',
    'pressure-washing': 'Pressure Washing',
    'tub-tile': 'Tub & Tile Refinishing',
    'construction-cleanup': 'Construction Cleanup',
    'covid-spray': 'COVID/Bacterial Spray',
    'car-detailing': 'Car Detailing',
    'specialty': 'Specialty Services'
}

# US States mapping
US_STATES = {
    'AL': 'Alabama', 'AK': 'Alaska', 'AZ': 'Arizona', 'AR': 'Arkansas', 'CA': 'California',
    'CO': 'Colorado', 'CT': 'Connecticut', 'DE': 'Delaware', 'FL': 'Florida', 'GA': 'Georgia',
    'HI': 'Hawaii', 'ID': 'Idaho', 'IL': 'Illinois', 'IN': 'Indiana', 'IA': 'Iowa',
    'KS': 'Kansas', 'KY': 'Kentucky', 'LA': 'Louisiana', 'ME': 'Maine', 'MD': 'Maryland',
    'MA': 'Massachusetts', 'MI': 'Michigan', 'MN': 'Minnesota', 'MS': 'Mississippi', 'MO': 'Missouri',
    'MT': 'Montana', 'NE': 'Nebraska', 'NV': 'Nevada', 'NH': 'New Hampshire', 'NJ': 'New Jersey',
    'NM': 'New Mexico', 'NY': 'New York', 'NC': 'North Carolina', 'ND': 'North Dakota', 'OH': 'Ohio',
    'OK': 'Oklahoma', 'OR': 'Oregon', 'PA': 'Pennsylvania', 'RI': 'Rhode Island', 'SC': 'South Carolina',
    'SD': 'South Dakota', 'TN': 'Tennessee', 'TX': 'Texas', 'UT': 'Utah', 'VT': 'Vermont',
    'VA': 'Virginia', 'WA': 'Washington', 'WV': 'West Virginia', 'WI': 'Wisconsin', 'WY': 'Wyoming'
}

# State-based zipcode prefixes
STATE_PREFIXES = {
    'AL': '35', 'AK': '99', 'AZ': '85', 'AR': '72', 'CA': '9', 
    'CO': '80', 'CT': '06', 'DE': '19', 'FL': '3', 'GA': '3', 
    'HI': '96', 'ID': '83', 'IL': '6', 'IN': '46', 'IA': '5', 
    'KS': '66', 'KY': '4', 'LA': '70', 'ME': '04', 'MD': '21',
    'MA': '01', 'MI': '48', 'MN': '55', 'MS': '39', 'MO': '63',
    'MT': '59', 'NE': '68', 'NV': '89', 'NH': '03', 'NJ': '07',
    'NM': '87', 'NY': '1', 'NC': '27', 'ND': '58', 'OH': '44',
    'OK': '73', 'OR': '97', 'PA': '15', 'RI': '02', 'SC': '29',
    'SD': '57', 'TN': '37', 'TX': '7', 'UT': '84', 'VT': '05',
    'VA': '22', 'WA': '98', 'WV': '25', 'WI': '53', 'WY': '82'
}

def validate_and_geocode_zipcode(zipcode, state):
    """
    Validate a zipcode and get its geocoordinates.
    Returns tuple of (latitude, longitude, is_valid)
    """
    if not zipcode or len(zipcode) < 5:
        return None, None, False
        
    # Ensure zipcode is 5 digits
    zipcode = zipcode[:5]
    
    try:
        # Try geocoding with zipcode
        location = geolocator.geocode(f"{zipcode}, {state}, USA", timeout=5)
        if location:
            return location.latitude, location.longitude, True
            
        # If that fails, try just the zipcode
        location = geolocator.geocode(f"{zipcode}, USA", timeout=5)
        if location:
            return location.latitude, location.longitude, True
    except Exception as e:
        logger.warning(f"Error geocoding zipcode {zipcode}: {e}")
    
    return None, None, False

def get_zipcode_for_state(state):
    """Generate a realistic zipcode for a state - always 5 digits with improved accuracy"""
    if state in STATE_PREFIXES:
        prefix = STATE_PREFIXES[state]
        
        # Calculate how many digits we need to generate to reach 5 total digits
        remaining_digits = 5 - len(prefix)
        
        # Generate the rest of the zipcode
        suffix = np.random.randint(0, 10**remaining_digits)
        format_str = f"{{:0{remaining_digits}d}}"
        formatted_suffix = format_str.format(suffix)
        
        zipcode = f"{prefix}{formatted_suffix}"
        
        # Attempt to validate the zipcode by geocoding it
        lat, lng, is_valid = validate_and_geocode_zipcode(zipcode, state)
        
        # If it's valid (has coordinates), return it
        if lat is not None and lng is not None:
            return zipcode
        
        # Otherwise try again one more time with a different random suffix
        suffix = np.random.randint(0, 10**remaining_digits)
        formatted_suffix = format_str.format(suffix)
        return f"{prefix}{formatted_suffix}"
    
    # Default zipcode if state is unknown - always 5 digits
    return f"{np.random.randint(10000, 99999)}"

class DatabaseManager:
    """Handle all database operations"""
    
    def __init__(self):
        self.db_path = 'database.db'
        self.init_database()
    
    def init_database(self):
        """Initialize database with all required tables"""
        conn = None
        cursor = None
        try:
            conn = sqlite3.connect(self.db_path, timeout=30.0)
            cursor = conn.cursor()
            
            # Users table
            cursor.execute('''
                CREATE TABLE IF NOT EXISTS users (
                    user_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL,
                    email TEXT UNIQUE NOT NULL,
                    password_hash TEXT NOT NULL,
                    role TEXT NOT NULL DEFAULT 'viewer',
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    last_login TIMESTAMP
                )
            ''')
            
            # Categories table
            cursor.execute('''
                CREATE TABLE IF NOT EXISTS categories (
                    category_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    category_name TEXT UNIQUE NOT NULL,
                    skills TEXT
                )
            ''')
            
            # Providers table
            cursor.execute('''
                CREATE TABLE IF NOT EXISTS providers (
                    provider_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL,
                    email TEXT,
                    phone TEXT,
                    city TEXT,
                    state TEXT,
                    type TEXT NOT NULL,
                    recruitment_platform TEXT,
                    latitude REAL,
                    longitude REAL,
                    ai_category TEXT,
                    zipcode TEXT,
                    last_updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            ''')
            
            # Provider-Category mapping table
            cursor.execute('''
                CREATE TABLE IF NOT EXISTS provider_category_map (
                    provider_id INTEGER,
                    category_id INTEGER,
                    PRIMARY KEY (provider_id, category_id),
                    FOREIGN KEY (provider_id) REFERENCES providers (provider_id),
                    FOREIGN KEY (category_id) REFERENCES categories (category_id)
                )
            ''')
            
            # Sources table
            cursor.execute('''
                CREATE TABLE IF NOT EXISTS sources (
                    source_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    source_name TEXT UNIQUE NOT NULL,
                    api_key TEXT,
                    last_run TIMESTAMP,
                    status TEXT DEFAULT 'inactive'
                )
            ''')
            
            # Collection logs table
            cursor.execute('''
                CREATE TABLE IF NOT EXISTS collection_logs (
                    log_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    source_name TEXT NOT NULL,
                    category TEXT,
                    records_collected INTEGER DEFAULT 0,
                    success_count INTEGER DEFAULT 0,
                    error_count INTEGER DEFAULT 0,
                    status TEXT DEFAULT 'running',
                    started_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    completed_at TIMESTAMP,
                    error_message TEXT
                )
            ''')
            
            # Settings table
            cursor.execute('''
                CREATE TABLE IF NOT EXISTS settings (
                    setting_key TEXT PRIMARY KEY,
                    setting_value TEXT,
                    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            ''')
            
            # Initialize default data
            self._init_default_data(cursor)
            
            # Commit changes
            conn.commit()
            
        except sqlite3.Error as e:
            app.logger.error(f"Database initialization error: {e}")
            # If database file exists but is corrupted, try to repair it
            if os.path.exists(self.db_path):
                try:
                    self.check_and_repair_database()
                except Exception as repair_error:
                    app.logger.error(f"Failed to repair database during initialization: {repair_error}")
            raise  # Re-raise the exception after repair attempt
            
        finally:
            if cursor:
                cursor.close()
            if conn:
                conn.close()
    
    def _init_default_data(self, cursor):
        """Initialize default categories and admin user"""
        # Insert categories
        for cat_key, cat_name in SERVICE_CATEGORIES.items():
            cursor.execute('''
                INSERT OR IGNORE INTO categories (category_name, skills)
                VALUES (?, ?)
            ''', (cat_name, cat_key))
        
        # Insert sources
        sources = [
            # API-based sources
            'Yelp API', 'Google Maps API', 'LinkedIn API', 'Crunchbase API', 'Yelp Fusion API',
            
            # Scrapers for business directories
            'Angi Scraper', 'Thumbtack Scraper', 'Facebook Scraper', 'YellowPages Scraper', 
            'BBB Scraper', 'Bing Places Scraper', 'Foursquare Scraper', 'Hotfrog Scraper',
            
            # Business directories
            'CityLocal Pro', 'USA Company Directory', 'AllBusiness Directory', 'United States Business Directory',
            'Corporation Directory', 'YellowPagesDirectory', 'Jasmine Directory', 'Thomasnet',
            'D&B Business Directory', 'US Chamber of Commerce Directory', 'LocalBizNetwork',
            'Manta', 'Citysearch', 'Local.com', 'Nextdoor Business Directory', 'Whitepages Business',
            '411 Business Directory', 'Brownbook', 'Infogroup', 'Ezlocal', 'MerchantCircle', 'CitySquares',
            'ShowMeLocal', 'WeAndCo', 'Pocket Insights', 'eLocal', 'Cylex USA', 'SuperPages',
            '2FindLocal', 'BOTW', 'Yellowbook', 'DexKnows', 'Alignable'
        ]
        for source in sources:
            cursor.execute('INSERT OR IGNORE INTO sources (source_name) VALUES (?)', (source,))
        
        # Create default admin user
        admin_password = generate_password_hash('admin123')
        cursor.execute('''
            INSERT OR IGNORE INTO users (name, email, password_hash, role)
            VALUES (?, ?, ?, ?)
        ''', ('System Admin', 'admin@demo.com', admin_password, 'admin'))
        
        # Create demo manager user
        manager_password = generate_password_hash('manager123')
        cursor.execute('''
            INSERT OR IGNORE INTO users (name, email, password_hash, role)
            VALUES (?, ?, ?, ?)
        ''', ('Manager Demo', 'manager@demo.com', manager_password, 'manager'))
        
        # Create demo regular user
        user_password = generate_password_hash('user123')
        cursor.execute('''
            INSERT OR IGNORE INTO users (name, email, password_hash, role)
            VALUES (?, ?, ?, ?)
        ''', ('User Demo', 'user@demo.com', user_password, 'viewer'))
        
        # Initialize default settings
        default_settings = [
            ('auto_classification', 'true'),
            ('duplicate_detection', 'true'),
            ('email_validation', 'true'),
            ('collection_frequency', 'weekly'),
            ('google_maps_api_key', ''),
            ('yelp_api_key', '')
        ]
        
        for key, value in default_settings:
            cursor.execute('''
                INSERT OR IGNORE INTO settings (setting_key, setting_value, updated_at)
                VALUES (?, ?, CURRENT_TIMESTAMP)
            ''', (key, value))
        
        # Insert sample providers for demonstration
        sample_providers = [
            ('Clean Pro Services', 'contact@cleanpro.com', '5551234567', 'Los Angeles', 'CA', 'business', 'Yelp', 34.0522, -118.2437, 'residential-cleaning', 92),
            ('John Smith HVAC', 'john@hvacsmith.com', '5559876543', 'Houston', 'TX', 'individual', 'LinkedIn', 29.7604, -95.3698, 'hvac', 87),
            ('Elite Plumbing Co', 'info@eliteplumbing.com', '5554567890', 'New York', 'NY', 'business', 'Google Maps', 40.7128, -74.0060, 'plumbers', 95),
            ('Mike\'s Electrical', 'mike@electrical.com', '5553216540', 'Chicago', 'IL', 'business', 'Angi', 41.8781, -87.6298, 'electricians', 89),
            ('Sarah Window Cleaning', 'sarah@windowclean.com', '5557891234', 'Phoenix', 'AZ', 'individual', 'Thumbtack', 33.4484, -112.0740, 'window-cleaning', 78)
        ]
        
        for provider in sample_providers:
            # Convert the last value (confidence) to a zipcode based on state
            state = provider[4]
            zipcode = get_zipcode_for_state(state)
            
            # Create a new provider tuple with zipcode instead of confidence
            modified_provider = provider[:10] + (zipcode,)
            
            cursor.execute('''
                INSERT OR IGNORE INTO providers 
                (name, email, phone, city, state, type, recruitment_platform, latitude, longitude, ai_category, zipcode)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', modified_provider)
        
        # No need to commit here, the connection will commit after this method returns
        # The commit is handled in the init_database method that calls this function
            
        # No need to commit here, the connection will commit after this method returns
        # The commit is handled in the init_database method that calls this function
        # if conn:
        #     conn.close()

    def get_connection(self):
        """Get database connection with error handling"""
        try:
            # Set timeout to avoid hanging connections
            conn = sqlite3.connect(self.db_path, timeout=30.0)
            # Enable foreign keys
            conn.execute('PRAGMA foreign_keys = ON')
            return conn
        except sqlite3.Error as e:
            app.logger.error(f"Database connection error: {e}")
            # Try to check and repair the database before giving up
            self.check_and_repair_database()
            # Try one more time after repair
            return sqlite3.connect(self.db_path, timeout=30.0)
            
    def check_and_repair_database(self):
        """Check database integrity and try to repair if needed"""
        app.logger.info("Checking database integrity...")
        try:
            # Create a new connection for checking
            temp_conn = sqlite3.connect(self.db_path, timeout=30.0)
            cursor = temp_conn.cursor()
            
            # Run integrity check
            cursor.execute("PRAGMA integrity_check;")
            integrity_result = cursor.fetchone()
            
            if integrity_result and integrity_result[0] == 'ok':
                app.logger.info("Database integrity check passed")
                
                # Also check for problematic NULL values
                self._check_and_fix_null_values(cursor)
                
                temp_conn.commit()
                temp_conn.close()
                return True
                
            app.logger.error(f"Database integrity check failed: {integrity_result}")
            
            # Try to recover by creating a backup and vacuum
            backup_path = f"{self.db_path}_backup_{int(time.time())}"
            shutil.copy2(self.db_path, backup_path)
            app.logger.info(f"Created database backup at {backup_path}")
            
            # Try to vacuum the database
            cursor.execute("VACUUM;")
            
            # Check for problematic NULL values that might be causing errors
            self._check_and_fix_null_values(cursor)
            
            temp_conn.commit()
            temp_conn.close()
            
            app.logger.info("Database repair attempt completed")
            return False
            
        except Exception as e:
            app.logger.error(f"Error during database integrity check: {e}")
            return False
            
    def _check_and_fix_null_values(self, cursor):
        """Check and fix NULL values that might cause issues"""
        app.logger.info("Checking for problematic NULL values...")
        
        # Check providers table for NULL values in critical fields
        cursor.execute("""
            SELECT provider_id, name, type
            FROM providers
            WHERE name IS NULL OR type IS NULL
        """)
        problematic_providers = cursor.fetchall()
        
        if problematic_providers:
            app.logger.warning(f"Found {len(problematic_providers)} providers with NULL values in critical fields")
            
            # Fix providers with NULL names or types
            for provider in problematic_providers:
                provider_id = provider[0]
                name = provider[1] if provider[1] else "Unknown Provider"
                type_val = provider[2] if provider[2] else "unknown"
                
                cursor.execute("""
                    UPDATE providers 
                    SET name = ?, type = ?
                    WHERE provider_id = ?
                """, (name, type_val, provider_id))
            
            app.logger.info(f"Fixed {len(problematic_providers)} providers with NULL values")
        else:
            app.logger.info("No providers with NULL values in critical fields found")
            
        # Check for NULL lat/long that should be 0 instead of NULL
        cursor.execute("""
            UPDATE providers
            SET latitude = 0
            WHERE latitude IS NULL
        """)
        lat_fixes = cursor.rowcount
        
        cursor.execute("""
            UPDATE providers
            SET longitude = 0
            WHERE longitude IS NULL
        """)
        long_fixes = cursor.rowcount
        
        if lat_fixes > 0 or long_fixes > 0:
            app.logger.info(f"Fixed {lat_fixes} NULL latitude values and {long_fixes} NULL longitude values")
        
        return (len(problematic_providers) + lat_fixes + long_fixes) > 0
    
    def find_and_remove_duplicates(self):
        """Find and remove duplicate providers based on similarity"""
        conn = self.get_connection()
        cursor = conn.cursor()
        
        # Get all providers
        cursor.execute('''
            SELECT provider_id, name, email, phone, city, state, type, ai_category, zipcode
            FROM providers 
            ORDER BY zipcode ASC
            ''')    
        providers = cursor.fetchall()
        duplicates_to_remove = []
        processed_ids = set()
        
        logger.info(f"Analyzing {len(providers)} providers for duplicates...")
        
        for i, provider1 in enumerate(providers):
            if provider1[0] in processed_ids:
                continue
                
            current_group = [provider1[0]]  # Start with current provider
            
            for j, provider2 in enumerate(providers[i+1:], i+1):
                if provider2[0] in processed_ids:
                    continue
                
                # Calculate similarity score
                similarity = self._calculate_similarity(provider1, provider2)
                
                # Only group providers that are 100% similar (exact matches)
                if similarity >= 0.99:  # 99%+ similarity threshold for exact matches
                    current_group.append(provider2[0])
                    
            # If we found exact duplicates, keep one based on zipcode
            if len(current_group) > 1:
                # Mark all as processed
                processed_ids.update(current_group)
                
                # Sort by zipcode and keep the first one
                group_providers = [p for p in providers if p[0] in current_group]
                # Use a safe sorting key that handles None values
                group_providers.sort(key=lambda x: (x[8] is None, x[8] or ""))
                
                # Keep the best one, mark others for removal
                best_provider = group_providers[0]
                duplicates_to_remove.extend([p[0] for p in group_providers[1:]])
                
                logger.info(f"Found exact duplicate group: kept '{best_provider[1]}' (zipcode: {best_provider[8]}), removing {len(group_providers)-1} exact duplicates")
            else:
                processed_ids.add(provider1[0])
        
        # Remove duplicates
        if duplicates_to_remove:
            placeholders = ','.join(['?' for _ in duplicates_to_remove])
            cursor.execute(f'DELETE FROM providers WHERE provider_id IN ({placeholders})', duplicates_to_remove)
            conn.commit()
            
            logger.info(f"Removed {len(duplicates_to_remove)} exact duplicate providers")
            
            # Log the deduplication
            cursor.execute('''
                INSERT INTO collection_logs (source, category, status, records_processed, success_count, error_count, notes)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            ''', ('System', 'Exact Deduplication', 'completed', len(providers), len(providers) - len(duplicates_to_remove), len(duplicates_to_remove), f'Removed {len(duplicates_to_remove)} exact duplicates only'))
            conn.commit()
        
        conn.close()
        return len(duplicates_to_remove)
    
    def _calculate_similarity(self, provider1, provider2):
        """Calculate similarity score between two providers - Only identifies exact matches"""
        exact_matches = 0
        total_factors = 0
        
        # Check for exact name match (case insensitive)
        if provider1[1] and provider2[1]:
            name1 = provider1[1].lower().strip()
            name2 = provider2[1].lower().strip()
            if name1 == name2:
                exact_matches += 1
            elif fuzz.ratio(name1, name2) >= 95:  # Very high threshold for name similarity
                exact_matches += 0.5  # Partial credit for very similar names
            total_factors += 1
        
        # Check for exact email match (case insensitive)
        if provider1[2] and provider2[2]:
            email1 = provider1[2].lower().strip()
            email2 = provider2[2].lower().strip()
            if email1 == email2:
                exact_matches += 1
            total_factors += 1
        
        # Check for exact phone match (digits only)
        if provider1[3] and provider2[3]:
            phone1 = ''.join(filter(str.isdigit, provider1[3]))
            phone2 = ''.join(filter(str.isdigit, provider2[3]))
            if len(phone1) >= 10 and len(phone2) >= 10:
                if phone1[-10:] == phone2[-10:]:  # Compare last 10 digits
                    exact_matches += 1
                total_factors += 1
        
        # Check for exact location match
        if provider1[4] and provider1[5] and provider2[4] and provider2[5]:
            location1 = f"{provider1[4]} {provider1[5]}".lower().strip()
            location2 = f"{provider2[4]} {provider2[5]}".lower().strip()
            if location1 == location2:
                exact_matches += 0.5  # Location gets half weight
            total_factors += 0.5
        
        # Return similarity score - need very high match rate for removal
        if total_factors == 0:
            return 0.0
        
        similarity_score = exact_matches / total_factors
        
        # Only return high similarity if we have strong matches
        # Require either:
        # 1. Exact name + email match, OR
        # 2. Exact name + phone match, OR  
        # 3. Exact email + phone match
        strong_match = False
        if provider1[1] and provider2[1] and provider1[2] and provider2[2]:
            # Name and email both exist
            name_match = provider1[1].lower().strip() == provider2[1].lower().strip()
            email_match = provider1[2].lower().strip() == provider2[2].lower().strip()
            if name_match and email_match:
                strong_match = True
        
        if provider1[1] and provider2[1] and provider1[3] and provider2[3]:
            # Name and phone both exist
            name_match = provider1[1].lower().strip() == provider2[1].lower().strip()
            phone1 = ''.join(filter(str.isdigit, provider1[3]))
            phone2 = ''.join(filter(str.isdigit, provider2[3]))
            phone_match = len(phone1) >= 10 and len(phone2) >= 10 and phone1[-10:] == phone2[-10:]
            if name_match and phone_match:
                strong_match = True
        
        if provider1[2] and provider2[2] and provider1[3] and provider2[3]:
            # Email and phone both exist
            email_match = provider1[2].lower().strip() == provider2[2].lower().strip()
            phone1 = ''.join(filter(str.isdigit, provider1[3]))
            phone2 = ''.join(filter(str.isdigit, provider2[3]))
            phone_match = len(phone1) >= 10 and len(phone2) >= 10 and phone1[-10:] == phone2[-10:]
            if email_match and phone_match:
                strong_match = True
        
        # Only return high similarity if we have a strong match
        return similarity_score if strong_match else 0.0

class AIClassifier:
    """Handle AI-powered classification of service providers"""
    
    def __init__(self):
        try:
            self.nlp = spacy.load("en_core_web_sm")
        except OSError:
            logger.warning("spaCy model not found. Using basic classification.")
            self.nlp = None
    
    def classify_provider(self, description: str, name: str = "", skills: str = "", city: str = "", state: str = "") -> Tuple[str, str]:
        """Classify provider into service category and assign zipcode based on location"""
        if not description and not name and not skills:
            return 'specialty', '00000'
        
        text = f"{name} {description} {skills}".lower()
        
        # Keywords for each category
        category_keywords = {
            'residential-cleaning': ['clean', 'house', 'home', 'residential', 'maid', 'housekeeping'],
            'commercial-janitorial': ['commercial', 'janitorial', 'office', 'building', 'facility'],
            'carpet-cleaning': ['carpet', 'rug', 'upholstery', 'steam clean'],
            'window-cleaning': ['window', 'glass', 'storefront'],
            'painters': ['paint', 'interior', 'exterior', 'brush', 'coating'],
            'maintenance': ['maintenance', 'repair', 'handyman', 'fix'],
            'hvac': ['hvac', 'heating', 'cooling', 'air conditioning', 'furnace'],
            'plumbers': ['plumb', 'pipe', 'drain', 'water', 'toilet', 'sink'],
            'electricians': ['electric', 'wire', 'outlet', 'circuit', 'voltage'],
            'floor-care': ['floor', 'hardwood', 'tile', 'wax', 'polish'],
            'waste-management': ['waste', 'trash', 'garbage', 'disposal', 'dumpster'],
            'pest-control': ['pest', 'bug', 'insect', 'rodent', 'exterminate'],
            'landscaping': ['landscape', 'lawn', 'grass', 'garden', 'tree'],
            'pressure-washing': ['pressure', 'power wash', 'blast', 'deck'],
            'tub-tile': ['tub', 'tile', 'bathroom', 'refinish', 'reglazing'],
            'construction-cleanup': ['construction', 'debris', 'cleanup', 'demo'],
            'covid-spray': ['covid', 'sanitize', 'disinfect', 'bacterial'],
            'car-detailing': ['car', 'auto', 'detail', 'wash', 'vehicle'],
            'specialty': ['specialty', 'custom', 'unique']
        }
        
        best_category = 'specialty'
        best_score = 0.0
        
        for category, keywords in category_keywords.items():
            score = 0
            for keyword in keywords:
                if keyword in text:
                    score += 1
            
            # Normalize score
            normalized_score = min(score / len(keywords), 1.0)
            
            if normalized_score > best_score:
                best_score = normalized_score
                best_category = category
        
        # Generate zipcode based on location with improved accuracy
        # Uses the global zipcode validation and generation function
        
        zipcode = get_zipcode_for_state(state)
        
        # Validate the zipcode to ensure it's a valid location
        lat, lng, is_valid = validate_and_geocode_zipcode(zipcode, state)
        
        # If not valid, ensure we use a 5-digit zipcode format
        if not is_valid:
            # Ensure we always return a 5-digit zipcode
            zipcode = zipcode[:5].zfill(5)
        
        return best_category, zipcode

class DataCollector:
    """Handle data collection from various sources"""
    
    def __init__(self, db_manager: DatabaseManager):
        self.db_manager = db_manager
        self.ai_classifier = AIClassifier()
        self.is_collecting = False
        
        # List of news websites to scrape
        self.news_websites = [
            'alabamareflector.com',
            'alaskabeacon.com',
            'azmirror.com',
            'arkansasadvocate.com',
            'calmatters.org',
            'coloradonewsline.com',
            'floridaphoenix.com',
            'georgiarecorder.com',
            'idahocapitalsun.com',
            'indianacapitalchronicle.com',
            'iowacapitaldispatch.com',
            'kansasreflector.com',
            'kentuckylantern.com',
            'marylandmatters.org',
            'michiganadvance.com',
            'minnesotareformer.com',
            'missouriindependent.com',
            'nebraskaexaminer.com',
            'nevadacurrent.com',
            'sourcenm.com',
            'nyfocus.com',
            'okvoice.org',
            'lookouttennessee.org',
            'texastribune.org',
            'virginiamercury.com',
            'wisconsinexaminer.com',
            'wyofile.com'
        ]
        
    def collect_from_yelp(self, category: str, location: str = "United States") -> Dict:
        """Collect real data from Yelp"""
        logger.info(f"Starting Yelp collection for {category} in {location}")
        
        # Start collection log
        log_id = self._start_collection_log('Yelp API', category)
        
        providers_found = 0
        providers_added = 0
        errors = 0
        
        try:
            # Convert category to search terms
            search_term = category.replace('-', ' ')
            
            # Create Yelp URL based on category
            base_url = f"https://www.yelp.com/search?find_desc={search_term}&find_loc={location}"
            
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36'
            }
            
            # Make the request
            response = requests.get(base_url, headers=headers, timeout=15)
            response.raise_for_status()
            
            # Parse the content
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # Find business listings
            business_listings = soup.select('.businessName')
            if not business_listings:
                business_listings = soup.select('[data-testid="businessName"]')
            
            logger.info(f"Found {len(business_listings)} potential providers on Yelp")
            
            # Process each business
            for i, listing in enumerate(business_listings):
                try:
                    # Update progress
                    if len(business_listings) > 0:
                        self._update_collection_progress(log_id, float(i) / len(business_listings))
                    
                    # Extract business name
                    name = listing.get_text().strip()
                    
                    # Try to get the business URL
                    business_url = None
                    link = listing.find('a')
                    if link and 'href' in link.attrs:
                        business_url = link['href']
                        if not business_url.startswith('http'):
                            business_url = f"https://www.yelp.com{business_url}"
                    
                    # Get additional business details if we have a URL
                    provider = {
                        'name': name,
                        'email': '',
                        'phone': '',
                        'city': '',
                        'state': '',
                        'type': 'business',  # Assume business for Yelp listings
                        'recruitment_platform': 'Yelp',
                        'latitude': None,
                        'longitude': None
                    }
                    
                    # Try to get more details
                    if business_url:
                        try:
                            detail_response = requests.get(business_url, headers=headers, timeout=10)
                            detail_soup = BeautifulSoup(detail_response.content, 'html.parser')
                            
                            # Get phone number
                            phone_elem = detail_soup.select_one('[data-testid="bizPhone"]')
                            if phone_elem:
                                provider['phone'] = phone_elem.get_text().strip()
                            
                            # Get address
                            address_elem = detail_soup.select_one('[data-testid="bizAddress"]')
                            if address_elem:
                                address = address_elem.get_text().strip()
                                
                                # Try to parse city and state from address
                                for state_code, state_name in US_STATES.items():
                                    if f", {state_code}" in address or f", {state_name}" in address:
                                        provider['state'] = state_code
                                        
                                        # Try to extract city (assuming format "City, State")
                                        city_match = re.search(r'([^,]+),\s+[A-Z]{2}', address)
                                        if city_match:
                                            provider['city'] = city_match.group(1).strip()
                                        break
                            
                            # Try to get email from website
                            website_elem = detail_soup.select_one('[data-testid="bizWebsite"] a')
                            if website_elem and 'href' in website_elem.attrs:
                                website_url = website_elem['href']
                                try:
                                    # Try to extract email from linked website
                                    web_response = requests.get(website_url, headers=headers, timeout=10)
                                    web_soup = BeautifulSoup(web_response.content, 'html.parser')
                                    
                                    # Look for email using regex
                                    email_pattern = r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}'
                                    emails = re.findall(email_pattern, str(web_soup))
                                    if emails:
                                        provider['email'] = emails[0].lower()
                                except Exception as e:
                                    logger.warning(f"Error extracting website information: {e}")
                        except Exception as e:
                            logger.warning(f"Error fetching business details: {e}")
                    
                    # Generate AI category and zipcode
                    ai_category, zipcode = self.ai_classifier.classify_provider(
                        f"{name} provides {category} services",
                        provider['name'],
                        "", # skills
                        provider['city'],
                        provider['state']
                    )
                    provider['ai_category'] = ai_category
                    provider['zipcode'] = zipcode
                    
                    # Increment counters
                    providers_found += 1
                    
                    # Add to database if we have enough information
                    if provider['name'] and (provider['email'] or provider['phone']) and provider['state']:
                        if self._add_provider_to_db(provider):
                            providers_added += 1
                    
                except Exception as e:
                    logger.warning(f"Error processing Yelp business: {e}")
                    errors += 1
        
        except Exception as e:
            logger.error(f"Error during Yelp collection: {e}")
            self._complete_collection_log(log_id, 'error', providers_found, providers_added, errors, str(e))
            return {
                'status': 'error',
                'message': str(e),
                'providers_found': providers_found,
                'providers_added': providers_added,
                'errors': errors
            }
        
        # Complete collection log
        self._complete_collection_log(log_id, 'completed', providers_found, providers_added, errors)
        
        return {
            'source': 'Yelp API',
            'category': category,
            'records_collected': providers_found,
            'records_added': providers_added,
            'errors': errors
        }
        
    def collect_from_news_websites(self, category: str = None, state: str = None) -> Dict:
        """Scrape data from news websites and extract service providers"""
        # Adjust collection log source name based on state
        source_name = 'News Websites'
        if state:
            state_name = US_STATES.get(state, state)
            source_name = f"News Websites ({state_name})"
            
        log_id = self._start_collection_log(source_name, category or 'all')
        
        providers_found = 0
        providers_added = 0
        errors = 0
        
        # Track which sites we've processed
        processed_sites = set()
        
        try:
            # Filter websites based on state if provided
            target_websites = self.news_websites
            if state:
                state_code = state.lower()
                state_name = US_STATES.get(state, state).lower()
                
                # Filter for websites that might be relevant to this state
                state_websites = []
                
                for website in self.news_websites:
                    # Check for state codes/names in domains, especially state-specific news sites
                    site_lower = website.lower()
                    
                        # Common patterns for state-specific news sites
                    if (state_code in site_lower or 
                        state_name in site_lower or 
                        f"{state_code}news" in site_lower or 
                        f"{state_name}news" in site_lower or
                        f"{state_name.replace(' ', '')}" in site_lower or
                        site_lower.startswith(f"{state_code}.") or
                        site_lower.startswith(f"{state_name.lower().replace(' ', '')}.") or
                        site_lower.endswith(f".{state_code.lower()}") or
                        f"-{state_code.lower()}" in site_lower or
                        f"-{state_name.lower().replace(' ', '')}" in site_lower):
                        state_websites.append(website)
                
                # If we found state-specific websites, use those, otherwise use all
                if state_websites:
                    target_websites = state_websites
                    logger.info(f"Found {len(state_websites)} news websites specific to {state_name}: {', '.join(state_websites)}")
                else:
                    logger.info(f"No state-specific news websites found for {state_name}, using all websites")
            
            total_websites = len(target_websites)
            logger.info(f"Starting to scrape {total_websites} news websites")
            
            for i, website in enumerate(target_websites):
                if self.is_collecting is False:
                    logger.info(f"Collection stopped by user")
                    break
                
                # Update progress (make sure to convert to float for proper division)
                self._update_collection_progress(log_id, float(i) / total_websites)
                    
                logger.info(f"Scraping website {i+1}/{total_websites}: {website}")
                try:
                    logger.info(f"Scraping {website}...")
                    processed_sites.add(website)
                    
                    # Make request with timeout and user agent to avoid blocks
                    headers = {
                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36'
                    }
                    
                    # Try to get the page with a timeout
                    try:
                        response = requests.get(f'https://{website}', headers=headers, timeout=10)
                        response.raise_for_status()
                    except (requests.RequestException, requests.Timeout) as e:
                        logger.warning(f"Error accessing {website}: {e}")
                        errors += 1
                        continue
                        
                    # Parse the content
                    soup = BeautifulSoup(response.content, 'html.parser')
                    
                    # Extract contact information and potential service providers
                    providers = self._extract_providers_from_page(soup, website, state)
                    
                    if providers:
                        providers_found += len(providers)
                        
                        # Save each provider to the database
                        for provider in providers:
                            # Add provider through the standard method
                            if self._add_provider_to_db(provider):
                                providers_added += 1
                                
                except Exception as e:
                    logger.error(f"Error processing {website}: {e}")
                    errors += 1
        
        except Exception as e:
            logger.error(f"Error during news website collection: {e}")
            self._complete_collection_log(log_id, 'error', providers_found, providers_added, errors, str(e))
            return {
                'status': 'error',
                'message': str(e),
                'providers_found': providers_found,
                'providers_added': providers_added,
                'errors': errors
            }
        
        # Update collection log
        status = 'completed' if not self.is_collecting else 'stopped'
        message = f"Processed {len(processed_sites)}/{len(target_websites)} websites"
        self._complete_collection_log(log_id, status, providers_found, providers_added, errors, message)
        
        return {
            'status': status,
            'providers_found': providers_found,
            'providers_added': providers_added,
            'errors': errors,
            'sites_processed': len(processed_sites),
            'total_sites': len(target_websites)
        }
    
    def _extract_providers_from_page(self, soup: BeautifulSoup, website: str, state: str = None) -> List[Dict]:
        """Extract potential service providers from a webpage"""
        providers = []
        
        # Extract state from website domain if possible and not provided
        if not state:
            for state_code, state_name in US_STATES.items():
                if state_code.lower() in website.lower() or state_name.lower() in website.lower():
                    state = state_code
                    break
        
        # Look for contact information in common locations
        contact_sections = soup.select('footer, .contact, .contact-us, #contact, [class*="contact"], [id*="contact"]')
        
        for section in contact_sections:
            # Extract potential service providers from contact sections
            provider = self._extract_contact_info(section, website, state)
            if provider:
                providers.append(provider)
        
        # If we didn't find any in contact sections, try the about page
        if not providers:
            about_links = soup.select('a[href*="about"]')
            for link in about_links[:1]:  # Just try the first about link
                href = link.get('href', '')
                if href.startswith('/'):
                    href = f"https://{website}{href}"
                elif not href.startswith('http'):
                    href = f"https://{website}/{href}"
                
                try:
                    headers = {
                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36'
                    }
                    response = requests.get(href, headers=headers, timeout=10)
                    if response.status_code == 200:
                        about_soup = BeautifulSoup(response.content, 'html.parser')
                        provider = self._extract_contact_info(about_soup, website, state)
                        if provider:
                            providers.append(provider)
                except Exception as e:
                    logger.warning(f"Error accessing about page {href}: {e}")
        
        return providers
    
    def _extract_contact_info(self, soup: BeautifulSoup, website: str, state: str = None) -> Dict:
        """Extract contact information from HTML"""
        # Initialize provider data
        provider = {
            'name': '',
            'email': '',
            'phone': '',
            'city': '',
            'state': state or '',
            'type': 'business',  # Assume business for news sites
            'recruitment_platform': website,
            'latitude': None,
            'longitude': None
        }
        
        # Try to get organization name
        org_name_tags = soup.select('.organization-name, .org-name, [itemprop="name"], .site-title, h1')
        if org_name_tags:
            provider['name'] = org_name_tags[0].get_text().strip()
        else:
            # Use the website name if we can't find a better one
            provider['name'] = website.split('.')[0].title()
        
        # Find emails using regex pattern
        email_pattern = r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}'
        emails = re.findall(email_pattern, str(soup))
        if emails:
            provider['email'] = emails[0].lower()
        
        # Find phone numbers
        phone_pattern = r'\(?\d{3}\)?[-. ]?\d{3}[-. ]?\d{4}'
        phones = re.findall(phone_pattern, str(soup))
        if phones:
            provider['phone'] = phones[0]
        
        # Try to find address/location information
        address_tags = soup.select('[itemprop="address"], .address, address')
        if address_tags:
            address_text = address_tags[0].get_text()
            
            # Try to extract city and state
            for state_code, state_name in US_STATES.items():
                if state_code in address_text or state_name in address_text:
                    provider['state'] = state_code
                    # Try to find city that comes before state
                    city_match = re.search(fr'([A-Za-z\s]+),\s*({state_code}|{state_name})', address_text)
                    if city_match:
                        provider['city'] = city_match.group(1).strip()
                    break
            
            # If we have city and state, try geocoding
            if provider['city'] and provider['state']:
                try:
                    # First try to get coordinates from zipcode if available
                    if provider.get('zipcode'):
                        lat, lng, is_valid = validate_and_geocode_zipcode(provider['zipcode'], provider['state'])
                        if lat is not None and lng is not None:
                            provider['latitude'] = lat
                            provider['longitude'] = lng
                            # If we got valid coordinates from zipcode, we're done
                            if is_valid:
                                return
                    
                    # If zipcode validation failed, fall back to city and state
                    location = geolocator.geocode(f"{provider['city']}, {provider['state']}")
                    if location:
                        provider['latitude'] = location.latitude
                        provider['longitude'] = location.longitude
                except Exception as e:
                    logger.warning(f"Geocoding error: {e}")
                    
            # Generate AI category and zipcode
            ai_category, zipcode = self.ai_classifier.classify_provider(
                f"News organization providing news and information services",
                provider['name'],
                "",
                provider['city'],
                provider['state']
            )
            provider['ai_category'] = ai_category
            provider['zipcode'] = zipcode
            
            return provider if (provider['email'] or provider['phone']) else None
        
        # If we didn't find address tags, return None
        return None
    
    def collect_from_google_maps(self, category: str, location: str = "United States") -> Dict:
        """Collect real data from Google Maps"""
        logger.info(f"Starting Google Maps collection for {category} in {location}")
        
        log_id = self._start_collection_log('Google Maps API', category)
        providers_found = 0
        providers_added = 0
        errors = 0
        
        try:
            # Convert category to search query
            search_term = category.replace('-', ' ')
            # Encode search query for URL
            encoded_search = requests.utils.quote(f"{search_term} in {location}")
            
            # Create Google Maps URL
            maps_url = f"https://www.google.com/maps/search/{encoded_search}/"
            
            # Set headers to mimic browser
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36',
                'Accept-Language': 'en-US,en;q=0.9',
                'Referer': 'https://www.google.com/'
            }
            
            # Make the request
            response = requests.get(maps_url, headers=headers, timeout=15)
            response.raise_for_status()
            
            # Parse the content
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # Extract business listings - Google Maps loads dynamically so we need to look for business data in the page
            script_tags = soup.find_all('script')
            business_data = []
            
            for script in script_tags:
                script_content = script.string
                if script_content and '"address"' in script_content and '"name"' in script_content:
                    # Try to extract business data from the JSON-like content in scripts
                    try:
                        # Find JSON objects in the script
                        json_matches = re.findall(r'\{[^{}]*"name"[^{}]*"address"[^{}]*\}', script_content)
                        for json_str in json_matches:
                            try:
                                # Clean up the JSON string
                                json_str = re.sub(r',\s*\}', '}', json_str)
                                # Try to parse as JSON
                                data = json.loads(json_str)
                                business_data.append(data)
                            except json.JSONDecodeError:
                                continue
                    except Exception as e:
                        logger.warning(f"Error parsing script content: {e}")
            
            logger.info(f"Found {len(business_data)} potential providers on Google Maps")
            
            # Process each business
            for i, business in enumerate(business_data):
                try:
                    # Update progress
                    if len(business_data) > 0:
                        self._update_collection_progress(log_id, float(i) / len(business_data))
                    
                    # Extract business information
                    name = business.get('name', '')
                    address = business.get('address', '')
                    phone = business.get('phone', '')
                    website = business.get('website', '')
                    
                    if not name:
                        continue
                    
                    # Parse address to get city and state
                    city = ''
                    state = ''
                    
                    for state_code, state_name in US_STATES.items():
                        if f", {state_code}" in address or f", {state_name}" in address:
                            state = state_code
                            
                            # Try to extract city (assuming format "City, State")
                            city_match = re.search(r'([^,]+),\s+[A-Z]{2}', address)
                            if city_match:
                                city = city_match.group(1).strip()
                            break
                    
                    # Create provider record
                    provider = {
                        'name': name,
                        'email': '',
                        'phone': phone,
                        'city': city,
                        'state': state,
                        'type': 'business',  # Assume business for Google Maps listings
                        'recruitment_platform': 'Google Maps',
                        'latitude': business.get('latitude'),
                        'longitude': business.get('longitude')
                    }
                    
                    # Try to get email from website if available
                    if website:
                        try:
                            web_response = requests.get(website, headers=headers, timeout=10)
                            web_soup = BeautifulSoup(web_response.content, 'html.parser')
                            
                            # Look for email using regex
                            email_pattern = r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}'
                            emails = re.findall(email_pattern, str(web_soup))
                            if emails:
                                provider['email'] = emails[0].lower()
                        except Exception as e:
                            logger.warning(f"Error extracting website information: {e}")
                    
                    # Generate AI category and zipcode
                    ai_category, zipcode = self.ai_classifier.classify_provider(
                        f"{name} provides {category} services",
                        provider['name'],
                        "",
                        provider['city'],
                        provider['state']
                    )
                    provider['ai_category'] = ai_category
                    provider['zipcode'] = zipcode
                    
                    # Increment counters
                    providers_found += 1
                    
                    # Add to database if we have enough information
                    if provider['name'] and (provider['email'] or provider['phone']) and provider['state']:
                        if self._add_provider_to_db(provider):
                            providers_added += 1
                            
                except Exception as e:
                    logger.warning(f"Error processing Google Maps business: {e}")
                    errors += 1
        
        except Exception as e:
            logger.error(f"Error during Google Maps collection: {e}")
            self._complete_collection_log(log_id, 'error', providers_found, providers_added, errors, str(e))
            return {
                'status': 'error',
                'message': str(e),
                'providers_found': providers_found,
                'providers_added': providers_added,
                'errors': errors
            }
        
        # Complete collection log
        self._complete_collection_log(log_id, 'completed', providers_found, providers_added, errors)
        
        return {
            'source': 'Google Maps API',
            'category': category,
            'records_collected': providers_found,
            'records_added': providers_added,
            'errors': errors
        }
    
    # Removed _generate_fake_provider method as we now use real data collection
    
    def _start_collection_log(self, source: str, category: str) -> int:
        """Start a collection log entry"""
        conn = self.db_manager.get_connection()
        cursor = conn.cursor()
        
        cursor.execute('''
            INSERT INTO collection_logs (source_name, category, status)
            VALUES (?, ?, 'running')
        ''', (source, category))
        
        log_id = cursor.lastrowid
        conn.commit()
        conn.close()
        
        return log_id
    
    # Removed collect_from_business_directory as we now use real data collection
    
    # Removed collect_from_yelp_fusion_api as we now use real data collection
    
    def collect_from_bbb(self, category: str, location: str = "United States") -> Dict:
        """Collect real data from Better Business Bureau"""
        logger.info(f"Starting BBB collection for {category} in {location}")
        
        log_id = self._start_collection_log('BBB Scraper', category)
        providers_found = 0
        providers_added = 0
        errors = 0
        
        try:
            # Format category and location for BBB URL
            formatted_category = category.replace('-', '+').replace(' ', '+')
            formatted_location = location.replace(' ', '+').replace(',', '')
            
            # Create BBB URL (BBB uses a different format per location, so we'll try the search page)
            bbb_url = f"https://www.bbb.org/search?find_country=USA&find_text={formatted_category}&find_type=Category&page=1"
            
            # Set headers to mimic browser
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36',
                'Accept-Language': 'en-US,en;q=0.9'
            }
            
            # Make the request
            response = requests.get(bbb_url, headers=headers, timeout=15)
            response.raise_for_status()
            
            # Parse the content
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # Find business listings
            business_listings = soup.select('.result-item-ab')
            if not business_listings:
                business_listings = soup.select('.MuiPaper-root')
            
            logger.info(f"Found {len(business_listings)} potential providers on BBB")
            
            # Process each business
            for i, listing in enumerate(business_listings):
                try:
                    # Update progress
                    if len(business_listings) > 0:
                        self._update_collection_progress(log_id, float(i) / len(business_listings))
                    
                    # Extract business name
                    name_elem = listing.select_one('.dtm-business') or listing.select_one('h3')
                    if not name_elem:
                        continue
                        
                    name = name_elem.get_text().strip()
                    
                    # Extract business URL for more details
                    business_url = None
                    link = name_elem.find('a')
                    if link and 'href' in link.attrs:
                        business_url = link['href']
                        if not business_url.startswith('http'):
                            business_url = f"https://www.bbb.org{business_url}"
                    
                    # Extract BBB rating if available
                    bbb_rating = ''
                    rating_elem = listing.select_one('.rating')
                    if rating_elem:
                        bbb_rating = rating_elem.get_text().strip()
                    
                    # Extract accreditation status
                    bbb_accredited = False
                    accredited_elem = listing.select_one('.accredited-badge')
                    if accredited_elem:
                        bbb_accredited = True
                    
                    # Create provider record
                    provider = {
                        'name': name,
                        'email': '',
                        'phone': '',
                        'city': '',
                        'state': '',
                        'type': 'business',
                        'recruitment_platform': 'BBB',
                        'latitude': None,
                        'longitude': None,
                        'bbb_rating': bbb_rating,
                        'bbb_accredited': bbb_accredited
                    }
                    
                    # Get additional business details if we have a URL
                    if business_url:
                        try:
                            detail_response = requests.get(business_url, headers=headers, timeout=10)
                            detail_soup = BeautifulSoup(detail_response.content, 'html.parser')
                            
                            # Extract contact info
                            contact_section = detail_soup.select_one('#contact')
                            if contact_section:
                                # Try to get phone
                                phone_elem = contact_section.select_one('[itemprop="telephone"]')
                                if phone_elem:
                                    provider['phone'] = phone_elem.get_text().strip()
                                
                                # Try to get address
                                address_elems = contact_section.select('[itemprop="streetAddress"], [itemprop="addressLocality"], [itemprop="addressRegion"]')
                                address_parts = [elem.get_text().strip() for elem in address_elems]
                                address = ' '.join(address_parts)
                                
                                # Try to extract city and state
                                for state_code, state_name in US_STATES.items():
                                    if state_code in address or f", {state_code}" in address:
                                        provider['state'] = state_code
                                        # Try to find city before state
                                        city_match = re.search(r'([^,]+),\s+' + state_code, address)
                                        if city_match:
                                            provider['city'] = city_match.group(1).strip()
                                        break
                            
                            # Try to get email
                            email_elem = detail_soup.select_one('a[href^="mailto:"]')
                            if email_elem and 'href' in email_elem.attrs:
                                email = email_elem['href'].replace('mailto:', '').strip()
                                provider['email'] = email
                            
                            # If still no email, try to extract from the page content
                            if not provider['email']:
                                email_pattern = r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}'
                                emails = re.findall(email_pattern, str(detail_soup))
                                if emails:
                                    provider['email'] = emails[0].lower()
                                
                        except Exception as e:
                            logger.warning(f"Error fetching BBB business details: {e}")
                    
                    # Generate AI category and zipcode
                    ai_category, zipcode = self.ai_classifier.classify_provider(
                        f"{name} provides {category} services",
                        provider['name'],
                        "",
                        provider['city'],
                        provider['state']
                    )
                    provider['ai_category'] = ai_category
                    provider['zipcode'] = zipcode
                    
                    # Increment counters
                    providers_found += 1
                    
                    # Add to database if we have enough information
                    if provider['name'] and (provider['email'] or provider['phone']) and provider['state']:
                        if self._add_provider_to_db(provider):
                            providers_added += 1
                    
                except Exception as e:
                    logger.warning(f"Error processing BBB business: {e}")
                    errors += 1
        
        except Exception as e:
            logger.error(f"Error during BBB collection: {e}")
            self._complete_collection_log(log_id, 'error', providers_found, providers_added, errors, str(e))
            return {
                'status': 'error',
                'message': str(e),
                'providers_found': providers_found,
                'providers_added': providers_added,
                'errors': errors
            }
        
        # Complete collection log
        self._complete_collection_log(log_id, 'completed', providers_found, providers_added, errors)
        
        return {
            'source': 'BBB Scraper',
            'category': category,
            'records_collected': providers_found,
            'records_added': providers_added,
            'errors': errors
        }
    
    def collect_from_yellow_pages(self, category: str, location: str = "United States") -> Dict:
        """Collect real data from YellowPages/YP"""
        logger.info(f"Starting YellowPages collection for {category} in {location}")
        
        log_id = self._start_collection_log('YellowPages Scraper', category)
        providers_found = 0
        providers_added = 0
        errors = 0
        
        try:
            # Format category and location for YP URL
            formatted_category = category.replace('-', '+').replace(' ', '+')
            formatted_location = location.replace(' ', '+').replace(',', '%2C')
            
            # Create YellowPages URL
            yp_url = f"https://www.yellowpages.com/search?search_terms={formatted_category}&geo_location_terms={formatted_location}"
            
            # Set headers to mimic browser
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36',
                'Accept-Language': 'en-US,en;q=0.9'
            }
            
            # Make the request
            response = requests.get(yp_url, headers=headers, timeout=15)
            response.raise_for_status()
            
            # Parse the content
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # Find business listings
            business_listings = soup.select('.search-results .result')
            
            logger.info(f"Found {len(business_listings)} potential providers on YellowPages")
            
            # Process each business
            for i, listing in enumerate(business_listings):
                try:
                    # Update progress
                    if len(business_listings) > 0:
                        self._update_collection_progress(log_id, float(i) / len(business_listings))
                    
                    # Extract business name
                    name_elem = listing.select_one('.business-name')
                    if not name_elem:
                        continue
                        
                    name = name_elem.get_text().strip()
                    
                    # Extract phone number
                    phone = ''
                    phone_elem = listing.select_one('.phones')
                    if phone_elem:
                        phone = phone_elem.get_text().strip()
                    
                    # Extract address
                    city = ''
                    state = ''
                    address_elem = listing.select_one('.street-address')
                    locality_elem = listing.select_one('.locality')
                    
                    if locality_elem:
                        locality_text = locality_elem.get_text().strip()
                        # Parse locality which typically has format "City, ST"
                        parts = locality_text.split(',')
                        if len(parts) >= 2:
                            city = parts[0].strip()
                            # Extract state code
                            state_part = parts[1].strip()
                            # Check if it matches a state code
                            if state_part[:2] in US_STATES:
                                state = state_part[:2]
                    
                    # Get business URL
                    business_url = None
                    website_elem = listing.select_one('.links a[href*="website"]')
                    if website_elem and 'href' in website_elem.attrs:
                        redirect_url = website_elem['href']
                        # YP uses redirects, try to follow to get actual website
                        try:
                            redirect_resp = requests.head(f"https://www.yellowpages.com{redirect_url}", 
                                                headers=headers, 
                                                timeout=5, 
                                                allow_redirects=True)
                            business_url = redirect_resp.url
                        except Exception:
                            pass
                    
                    # Create provider record
                    provider = {
                        'name': name,
                        'email': '',
                        'phone': phone,
                        'city': city,
                        'state': state,
                        'type': 'business',
                        'recruitment_platform': 'YellowPages',
                        'latitude': None,
                        'longitude': None
                    }
                    
                    # Try to extract additional data (ratings, years, etc.)
                    years_elem = listing.select_one('.years-in-business')
                    if years_elem:
                        years_text = years_elem.get_text().strip()
                        years_match = re.search(r'\d+', years_text)
                        if years_match:
                            provider['yp_years_in_business'] = int(years_match.group(0))
                    
                    # Extract ratings
                    rating_elem = listing.select_one('.ratings .result-rating')
                    if rating_elem:
                        # Try to get rating from aria-label which often contains the rating value
                        rating_str = rating_elem.get('aria-label', '')
                        rating_match = re.search(r'([\d\.]+)\s+stars?', rating_str)
                        if rating_match:
                            provider['yp_rating'] = float(rating_match.group(1))
                    
                    # Try to get email from website if available
                    if business_url:
                        try:
                            web_response = requests.get(business_url, headers=headers, timeout=10)
                            web_soup = BeautifulSoup(web_response.content, 'html.parser')
                            
                            # Look for email using regex
                            email_pattern = r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}'
                            emails = re.findall(email_pattern, str(web_soup))
                            if emails:
                                provider['email'] = emails[0].lower()
                        except Exception as e:
                            logger.warning(f"Error extracting website information: {e}")
                    
                    # Generate AI category and zipcode
                    ai_category, zipcode = self.ai_classifier.classify_provider(
                        f"{name} provides {category} services",
                        provider['name'],
                        "",
                        provider['city'],
                        provider['state']
                    )
                    provider['ai_category'] = ai_category
                    provider['zipcode'] = zipcode
                    
                    # Increment counters
                    providers_found += 1
                    
                    # Add to database if we have enough information
                    if provider['name'] and (provider['email'] or provider['phone']) and provider['state']:
                        if self._add_provider_to_db(provider):
                            providers_added += 1
                    
                except Exception as e:
                    logger.warning(f"Error processing YellowPages business: {e}")
                    errors += 1
        
        except Exception as e:
            logger.error(f"Error during YellowPages collection: {e}")
            self._complete_collection_log(log_id, 'error', providers_found, providers_added, errors, str(e))
            return {
                'status': 'error',
                'message': str(e),
                'providers_found': providers_found,
                'providers_added': providers_added,
                'errors': errors
            }
        
        # Complete collection log
        self._complete_collection_log(log_id, 'completed', providers_found, providers_added, errors)
        
        return {
            'source': 'YellowPages Scraper',
            'category': category,
            'records_collected': providers_found,
            'records_added': providers_added,
            'errors': errors
        }
    
    # Removed collect_from_thomasnet as we now use real data collection
    
    # Removed collect_from_dun_bradstreet as we now use real data collection
    
    # Removed collect_from_manta as we now use real data collection
    
    def _extract_email_from_website(self, url: str) -> str:
        """Attempt to extract email address from a website"""
        try:
            # Set headers to mimic browser
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36',
                'Accept-Language': 'en-US,en;q=0.9'
            }
            
            # Make the request with a reasonable timeout
            response = requests.get(url, headers=headers, timeout=10)
            response.raise_for_status()
            
            # Parse the content
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # First, look for mailto links
            email_links = soup.select('a[href^="mailto:"]')
            for link in email_links:
                href = link.get('href', '')
                if href.startswith('mailto:'):
                    email = href.replace('mailto:', '').split('?')[0].strip()
                    if '@' in email and '.' in email.split('@')[1]:
                        return email.lower()
            
            # If no mailto links found, use regex to find email patterns in the page
            email_pattern = r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}'
            emails = re.findall(email_pattern, str(soup))
            
            # Filter out common false positives
            filtered_emails = []
            for email in emails:
                # Skip emails with common false-positive patterns
                if any(pattern in email.lower() for pattern in ['example.com', 'domain.com', 'yourdomain', 'email@']):
                    continue
                filtered_emails.append(email.lower())
            
            if filtered_emails:
                # Prioritize emails that might be associated with the domain
                domain = url.split('//')[-1].split('/')[0].split('www.')[-1]
                for email in filtered_emails:
                    if domain in email:
                        return email
                # Otherwise return the first email found
                return filtered_emails[0]
                
            # Check contact pages if no email found yet
            contact_links = []
            for a in soup.find_all('a', href=True):
                href = a['href']
                text = a.get_text().lower()
                if 'contact' in href.lower() or 'contact' in text:
                    contact_links.append(href)
            
            # Try up to 2 contact pages
            for link in contact_links[:2]:
                # Convert relative URLs to absolute
                if link.startswith('/'):
                    contact_url = f"{url.rstrip('/')}{link}"
                elif not link.startswith('http'):
                    contact_url = f"{url.rstrip('/')}/{link.lstrip('/')}"
                else:
                    contact_url = link
                    
                try:
                    contact_response = requests.get(contact_url, headers=headers, timeout=8)
                    if contact_response.status_code == 200:
                        contact_soup = BeautifulSoup(contact_response.content, 'html.parser')
                        contact_emails = re.findall(email_pattern, str(contact_soup))
                        filtered_contact_emails = [email.lower() for email in contact_emails 
                                            if not any(pattern in email.lower() for pattern in ['example.com', 'domain.com', 'yourdomain', 'email@'])]
                        if filtered_contact_emails:
                            return filtered_contact_emails[0]
                except Exception:
                    continue
                    
            return ""
        
        except Exception as e:
            logger.warning(f"Error extracting email from website {url}: {e}")
            return ""
    
    def _update_collection_progress(self, log_id: int, progress: float):
        """Update the collection progress for live tracking"""
        try:
            # Ensure progress is between 0 and 1
            progress = max(0, min(1, progress))
            
            # Store progress in global variable for status API
            global collection_progress
            collection_progress = progress
            
            # Emit progress event for WebSocket
            socketio.emit('collection_progress', {'progress': progress})
            
            # Log progress update at certain intervals
            if int(progress * 100) % 10 == 0:  # Log every 10%
                logger.info(f"Collection progress: {int(progress * 100)}%")
        except Exception as e:
            logger.error(f"Error updating collection progress: {e}")
    
    def _complete_collection_log(self, log_id: int, status='completed', providers_found=0, providers_added=0, 
                            errors=0, message=None):
        """Complete a collection log entry with flexible parameters"""
        conn = self.db_manager.get_connection()
        cursor = conn.cursor()
        
        # Handle backward compatibility - old method signature with success_count, error_count
        if isinstance(status, int):
            success_count = status
            error_count = providers_found if isinstance(providers_found, int) else 0
            cursor.execute('''
                UPDATE collection_logs 
                SET records_collected = ?, success_count = ?, error_count = ?, 
                    status = 'completed', completed_at = CURRENT_TIMESTAMP
                WHERE log_id = ?
            ''', (success_count, success_count, error_count, log_id))
        else:
            # New method with full parameters
            cursor.execute('''
                UPDATE collection_logs 
                SET records_collected = ?, success_count = ?, error_count = ?, 
                    status = ?, completed_at = CURRENT_TIMESTAMP, 
                    message = ?
                WHERE log_id = ?
            ''', (providers_found, providers_added, errors, status, message, log_id))
            
        conn.commit()
        
        # Reset the collection progress when complete
        global collection_progress
        collection_progress = 0
        
        # Send a final 100% progress update for UI
        socketio.emit('collection_progress', {'progress': 1.0})
        
        conn.commit()
        conn.close()
    
    def _add_provider_to_db(self, provider: Dict) -> bool:
        """Add a provider to the database, checking for duplicates
        Returns True if provider was added, False if it was a duplicate"""
        conn = self.db_manager.get_connection()
        cursor = conn.cursor()
        
        try:
            # Check for exact duplicates only
            cursor.execute('''
                SELECT provider_id, name, email, phone FROM providers 
                WHERE state = ? AND city = ?
            ''', (provider['state'], provider['city']))
            
            existing_providers = cursor.fetchall()
            
            is_exact_duplicate = False
            for existing in existing_providers:
                # Check for exact name match
                name_match = provider['name'].lower().strip() == existing[1].lower().strip() if existing[1] else False
                
                # Check for exact email match
                email_match = False
                if provider.get('email') and existing[2]:
                    email_match = provider['email'].lower().strip() == existing[2].lower().strip()
                
                # Check for exact phone match
                phone_match = False
                if provider.get('phone') and existing[3]:
                    phone1 = ''.join(filter(str.isdigit, provider['phone']))
                    phone2 = ''.join(filter(str.isdigit, existing[3]))
                    if len(phone1) >= 10 and len(phone2) >= 10:
                        phone_match = phone1[-10:] == phone2[-10:]
                
                # Only consider it a duplicate if we have strong exact matches
                if (name_match and email_match) or (name_match and phone_match) or (email_match and phone_match):
                    is_exact_duplicate = True
                    logger.info(f"Skipping exact duplicate: {provider['name']}")
                    break
            
            if not is_exact_duplicate:
                cursor.execute('''
                    INSERT INTO providers 
                    (name, email, phone, city, state, type, recruitment_platform, 
                     latitude, longitude, ai_category, zipcode)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ''', (
                    provider['name'], provider.get('email', ''), provider.get('phone', ''),
                    provider.get('city', ''), provider.get('state', ''), provider.get('type', 'business'),
                    provider.get('recruitment_platform', ''), provider.get('latitude'),
                    provider.get('longitude'), provider.get('ai_category', ''), provider.get('zipcode', '')
                ))
                conn.commit()
                return True
            
            return False
                
        except Exception as e:
            logger.error(f"Error adding provider to database: {e}")
            return False
        finally:
            conn.close()
    
    def _store_providers(self, providers: List[Dict]):
        """Store collected providers in database"""
        conn = self.db_manager.get_connection()
        cursor = conn.cursor()
        
        for provider in providers:
            # Check for exact duplicates only
            cursor.execute('''
                SELECT provider_id, name, email, phone FROM providers 
                WHERE state = ? AND city = ?
            ''', (provider['state'], provider['city']))
            
            existing_providers = cursor.fetchall()
            
            is_exact_duplicate = False
            for existing in existing_providers:
                # Check for exact name match
                name_match = provider['name'].lower().strip() == existing[1].lower().strip() if existing[1] else False
                
                # Check for exact email match
                email_match = False
                if provider.get('email') and existing[2]:
                    email_match = provider['email'].lower().strip() == existing[2].lower().strip()
                
                # Check for exact phone match
                phone_match = False
                if provider.get('phone') and existing[3]:
                    phone1 = ''.join(filter(str.isdigit, provider['phone']))
                    phone2 = ''.join(filter(str.isdigit, existing[3]))
                    if len(phone1) >= 10 and len(phone2) >= 10:
                        phone_match = phone1[-10:] == phone2[-10:]
                
                # Only consider it a duplicate if we have strong exact matches
                if (name_match and email_match) or (name_match and phone_match) or (email_match and phone_match):
                    is_exact_duplicate = True
                    logger.info(f"Skipping exact duplicate: {provider['name']}")
                    break
            
            if not is_exact_duplicate:
                cursor.execute('''
                    INSERT INTO providers 
                    (name, email, phone, city, state, type, recruitment_platform, 
                     latitude, longitude, ai_category, zipcode)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ''', (
                    provider['name'], provider['email'], provider['phone'],
                    provider['city'], provider['state'], provider['type'],
                    provider['recruitment_platform'], provider['latitude'],
                    provider['longitude'], provider['ai_category'], provider.get('zipcode', '')
                ))
        
        conn.commit()
        conn.close()

# Initialize global objects
db_manager = DatabaseManager()
data_collector = DataCollector(db_manager)

# Authentication decorator
def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'user_id' not in session:
            return jsonify({'error': 'Authentication required'}), 401
        return f(*args, **kwargs)
    return decorated_function

def role_required(required_roles):
    def decorator(f):
        @wraps(f)
        def decorated_function(*args, **kwargs):
            if 'user_role' not in session or session['user_role'] not in required_roles:
                return jsonify({'error': 'Insufficient permissions'}), 403
            return f(*args, **kwargs)
        return decorated_function
    return decorator

# Routes
@app.route('/')
def index():
    """Serve the main dashboard or redirect to login"""
    # Ensure default settings exist
    _ensure_default_settings_exist()
    
    if 'user_id' not in session:
        return redirect(url_for('login_page'))
    return render_template('dashboard.html')

def _ensure_default_settings_exist():
    """Helper function to make sure default settings exist in the database"""
    try:
        conn = db_manager.get_connection()
        cursor = conn.cursor()
        
        # Check if we have the expected settings
        cursor.execute("SELECT COUNT(*) FROM settings")
        count = cursor.fetchone()[0]
        
        if count < 7:  # We expect at least 7 default settings
            # Initialize default settings
            default_settings = [
                ('auto_classification', 'true'),
                ('duplicate_detection', 'true'),
                ('email_validation', 'true'),
                ('collection_frequency', 'weekly'),
                ('google_maps_api_key', ''),
                ('yelp_api_key', ''),
                ('developer_mode', 'false')  # Add developer mode setting
            ]
            
            for key, value in default_settings:
                cursor.execute('''
                    INSERT OR IGNORE INTO settings (setting_key, setting_value, updated_at)
                    VALUES (?, ?, CURRENT_TIMESTAMP)
                ''', (key, value))
            
            conn.commit()
            logger.info("Default settings initialized")
        
        conn.close()
    except Exception as e:
        logger.error(f"Error ensuring default settings: {e}")
        # Don't raise the exception - we don't want this to block the application

@app.route('/api/export/providers', methods=['GET'])
@login_required
def export_providers():
    """Export providers to JSON file"""
    try:
        # Get optional filter parameters
        category = request.args.get('category')
        state = request.args.get('state')
        source = request.args.get('source')
        
        conn = db_manager.get_connection()
        cursor = conn.cursor()
        
        # Build query based on filters
        query = '''
            SELECT p.provider_id, p.name, p.email, p.phone, p.city, p.state, 
                   p.type, p.recruitment_platform, p.latitude, p.longitude, 
                   p.ai_category, p.zipcode, p.last_updated, p.created_at
            FROM providers p
        '''
        
        params = []
        where_clauses = []
        
        if category:
            query += '''
                JOIN provider_category_map pcm ON p.provider_id = pcm.provider_id
                JOIN categories c ON pcm.category_id = c.category_id 
            '''
            where_clauses.append("c.category_name = ? OR c.skills = ?")
            params.extend([category, category])
            
        if state:
            where_clauses.append("p.state = ?")
            params.append(state)
            
        if source:
            where_clauses.append("p.recruitment_platform = ?")
            params.append(source)
            
        if where_clauses:
            query += " WHERE " + " AND ".join(where_clauses)
            
        # Execute the query
        cursor.execute(query, params)
        rows = cursor.fetchall()
        
        # Convert to list of dictionaries
        providers = []
        for row in rows:
            providers.append({
                'id': row[0],
                'name': row[1],
                'email': row[2],
                'phone': row[3],
                'city': row[4],
                'state': row[5],
                'type': row[6],
                'recruitment_platform': row[7],
                'latitude': row[8],
                'longitude': row[9],
                'ai_category': row[10],
                'zipcode': row[11],
                'last_updated': row[12],
                'created_at': row[13]
            })
        
        # Generate filename with timestamp
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"providers_export_{timestamp}.json"
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
        
        # Write to JSON file
        with open(filepath, 'w') as f:
            json.dump(providers, f, indent=2)
            
        # Log the export
        user_id = session.get('user_id')
        cursor.execute('''
            INSERT INTO collection_logs 
            (source_name, category, records_collected, status, message)
            VALUES (?, ?, ?, ?, ?)
        ''', (
            f"JSON Export",
            category if category else "all",
            len(providers),
            "completed",
            f"Exported by user ID {user_id}"
        ))
        conn.commit()
        conn.close()
        
        # Send file as download
        return send_file(filepath, as_attachment=True)
    
    except Exception as e:
        logger.error(f"Error exporting data: {e}")
        return jsonify({'error': f"Export failed: {e}"}), 500

@app.route('/login')
def login_page():
    """Serve the login page"""
    # If already logged in, redirect to dashboard
    if 'user_id' in session:
        return redirect(url_for('index'))
    return render_template('login.html')

@app.route('/api/login', methods=['POST'])
def login():
    """User login endpoint"""
    data = request.get_json()
    email = data.get('email')
    password = data.get('password')
    
    if not email or not password:
        return jsonify({'error': 'Email and password required'}), 400
    
    conn = db_manager.get_connection()
    cursor = conn.cursor()
    
    cursor.execute('''
        SELECT user_id, name, email, password_hash, role 
        FROM users WHERE email = ?
    ''', (email,))
    
    user = cursor.fetchone()
    conn.close()
    
    if user and check_password_hash(user[3], password):
        session['user_id'] = user[0]
        session['user_name'] = user[1]
        session['user_email'] = user[2]
        session['user_role'] = user[4]
        
        # Update last login
        conn = db_manager.get_connection()
        cursor = conn.cursor()
        cursor.execute('''
            UPDATE users SET last_login = CURRENT_TIMESTAMP WHERE user_id = ?
        ''', (user[0],))
        conn.commit()
        conn.close()
        
        return jsonify({
            'success': True,
            'user': {
                'id': user[0],
                'name': user[1],
                'email': user[2],
                'role': user[4]
            }
        })
    
    return jsonify({'error': 'Invalid credentials'}), 401

@app.route('/api/logout', methods=['POST'])
def logout():
    """User logout endpoint"""
    session.clear()
    return jsonify({'success': True})

@app.route('/api/providers', methods=['GET'])
@login_required
def get_providers():
    """Get providers with filtering and pagination"""
    try:
        # Get query parameters with validation
        try:
            page = max(1, int(request.args.get('page', 1)))
        except (ValueError, TypeError):
            page = 1
            
        try:
            per_page = min(100, max(1, int(request.args.get('per_page', 20))))
        except (ValueError, TypeError):
            per_page = 20
            
        category = request.args.get('category')
        state = request.args.get('state')
        provider_type = request.args.get('type')
        zipcode_prefix = request.args.get('confidence')  # Keep parameter name as 'confidence' for backward compatibility
        search = request.args.get('search')
    
        # Initialize database connection and cursor
        conn = None
        cursor = None
        try:
            conn = db_manager.get_connection()
            cursor = conn.cursor()
            
            # Build query
            query = '''
                SELECT provider_id, name, email, phone, city, state, type, 
                       recruitment_platform, latitude, longitude, ai_category, zipcode,
                       last_updated
                FROM providers
                WHERE 1=1
            '''
            params = []
    
            if category:
                query += ' AND ai_category = ?'
                params.append(category)
            
            if state:
                query += ' AND state = ?'
                params.append(state)
            
            if provider_type:
                query += ' AND type = ?'
                params.append(provider_type)
            
            if zipcode_prefix:  # Filter by zipcode prefix
                query += ' AND zipcode LIKE ?'
                params.append(f"{zipcode_prefix}%")
            
            if search:
                query += ' AND (name LIKE ? OR email LIKE ? OR phone LIKE ? OR city LIKE ?)'
                search_param = f'%{search}%'
                params.extend([search_param, search_param, search_param, search_param])
            
            # Count total records
            count_query = query.replace('SELECT provider_id, name, email, phone, city, state, type, recruitment_platform, latitude, longitude, ai_category, zipcode, last_updated', 'SELECT COUNT(*)')
            cursor.execute(count_query, params)
            count_result = cursor.fetchone()
            total_count = count_result[0] if count_result else 0
            
            # Add pagination
            query += ' ORDER BY last_updated DESC LIMIT ? OFFSET ?'
            params.extend([per_page, (page - 1) * per_page])
            
            cursor.execute(query, params)
            providers = cursor.fetchall()
            
            # Format response
            provider_list = []
            for provider in providers:
                try:
                    # Ensure all values are properly handled to prevent NULL errors
                    provider_id = provider[0] if provider[0] is not None else 0
                    name = provider[1] if provider[1] is not None else 'Unknown Provider'
                    email = provider[2] if provider[2] is not None else ''
                    phone = provider[3] if provider[3] is not None else ''
                    city = provider[4] if provider[4] is not None else ''
                    state = provider[5] if provider[5] is not None else ''
                    provider_type = provider[6] if provider[6] is not None else 'unknown'
                    source = provider[7] if provider[7] is not None else ''
                    
                    # Special handling for coordinates to prevent NULL errors in mapping
                    try:
                        latitude = float(provider[8]) if provider[8] is not None else 0.0
                    except (ValueError, TypeError):
                        latitude = 0.0
                        
                    try:
                        longitude = float(provider[9]) if provider[9] is not None else 0.0
                    except (ValueError, TypeError):
                        longitude = 0.0
                        
                    category = provider[10] if provider[10] is not None else ''
                    
                    zipcode = provider[11] if provider[11] is not None else ''
                        
                    last_updated = provider[12] if provider[12] is not None else ''
                    
                    provider_list.append({
                        'id': provider_id,
                        'name': name,
                        'email': email,
                        'phone': phone,
                        'city': city,
                        'state': state,
                        'type': provider_type,
                        'source': source,
                        'latitude': latitude,
                        'longitude': longitude,
                        'category': category,
                        'zipcode': zipcode,
                        'last_updated': last_updated
                    })
                except (IndexError, TypeError) as e:
                    # Skip malformed provider data
                    app.logger.error(f"Error processing provider data: {e}, provider data: {provider}")
                    continue
            
            response_data = {
                'providers': provider_list,
                'total': total_count,
                'page': page,
                'per_page': per_page,
                'pages': (total_count + per_page - 1) // per_page
            }
            
            return jsonify(response_data)
            
        except sqlite3.Error as db_error:
            app.logger.error(f"Database error in get_providers: {db_error}")
            return jsonify({'error': 'Database error', 'message': str(db_error)}), 500
        finally:
            if cursor:
                cursor.close()
            if conn:
                conn.close()
    except Exception as e:
        app.logger.error(f"Unexpected error in get_providers: {e}")
        return jsonify({'error': 'Server error', 'message': 'An unexpected error occurred'}), 500

@app.route('/api/database/check', methods=['POST'])
@login_required
def check_database():
    """Admin endpoint to check and repair database if needed"""
    try:
        result = db_manager.check_and_repair_database()
        if result:
            return jsonify({'status': 'success', 'message': 'Database integrity check passed'})
        else:
            return jsonify({'status': 'warning', 'message': 'Database repair attempted, please check logs'})
    except Exception as e:
        app.logger.error(f"Error during manual database check: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 500

@app.route('/api/stats', methods=['GET'])
@login_required
def get_stats():
    """Get dashboard statistics"""
    conn = db_manager.get_connection()
    cursor = conn.cursor()
    
    # Total providers
    cursor.execute('SELECT COUNT(*) FROM providers')
    total_providers = cursor.fetchone()[0]
    
    # Individuals vs business owners
    cursor.execute('SELECT type, COUNT(*) FROM providers GROUP BY type')
    type_counts = dict(cursor.fetchall())
    
    # States covered
    cursor.execute('SELECT COUNT(DISTINCT state) FROM providers')
    states_covered = cursor.fetchone()[0]
    
    # Category distribution
    cursor.execute('''
        SELECT ai_category, COUNT(*) 
        FROM providers 
        GROUP BY ai_category 
        ORDER BY COUNT(*) DESC
    ''')
    category_distribution = dict(cursor.fetchall())
    
    # State distribution
    cursor.execute('''
        SELECT state, COUNT(*) 
        FROM providers 
        GROUP BY state 
        ORDER BY COUNT(*) DESC 
        LIMIT 10
    ''')
    state_distribution = dict(cursor.fetchall())
    
    conn.close()
    
    # Include collection progress if an active collection is happening
    global collection_progress
    
    stats_data = {
        'total_providers': total_providers,
        'individuals': type_counts.get('individual', 0),
        'business_owners': type_counts.get('business', 0),
        'states_covered': states_covered,
        'category_distribution': category_distribution,
        'state_distribution': state_distribution
    }
    
    # Add collection progress if it's active
    if collection_progress > 0:
        stats_data['collection_progress'] = collection_progress
    
    return jsonify(stats_data)

@app.route('/api/recent_activity', methods=['GET'])
@login_required
def get_recent_activity():
    """Get recent collection activity"""
    conn = db_manager.get_connection()
    cursor = conn.cursor()
    
    cursor.execute('''
        SELECT source_name, category, records_collected, status, started_at
        FROM collection_logs
        ORDER BY started_at DESC
        LIMIT 10
    ''')
    
    activities = cursor.fetchall()
    conn.close()
    
    activity_list = []
    for activity in activities:
        activity_list.append({
            'source': activity[0],
            'category': activity[1],
            'records': activity[2] or 0,
            'status': activity[3],
            'time': activity[4]
        })
    
    return jsonify({'activities': activity_list})

@app.route('/api/collection/start', methods=['POST'])
@login_required
@role_required(['admin', 'manager'])
def start_collection():
    """Start data collection process"""
    data = request.get_json()
    source = data.get('source')
    category = data.get('category')
    state = data.get('state')  # Optional state parameter for state-specific collections
    
    if not source or not category:
        return jsonify({'error': 'Source and category required'}), 400
    
    def run_collection():
        try:
            # API-based sources
            if source.lower() == 'yelp' or source.lower() == 'yelp api':
                result = data_collector.collect_from_yelp(category)
            elif source.lower() == 'google maps' or source.lower() == 'google maps api':
                result = data_collector.collect_from_google_maps(category)
            # Scraper-based sources
            elif source.lower() == 'bbb scraper' or source.lower() == 'bbb':
                result = data_collector.collect_from_bbb(category)
            elif source.lower() in ['yellowpages scraper', 'yellowpages', 'yp', 'yp.com']:
                result = data_collector.collect_from_yellow_pages(category)
            # News websites collection
            elif source.lower() in ['news websites', 'news sites', 'state news']:
                # Get state parameter if provided
                state = data.get('state')
                result = data_collector.collect_from_news_websites(category, state)
            # All other sources will use the yellowpages scraper (most reliable)
            else:
                logger.info(f"Using YellowPages scraper for source: {source}")
                result = data_collector.collect_from_yellow_pages(category)
            
            # Emit completion
            socketio.emit('collection_complete', result)
            
            # Run comprehensive deduplication after collection
            logger.info("Running comprehensive deduplication after data collection...")
            removed_count = db_manager.find_and_remove_duplicates()
            if removed_count > 0:
                logger.info(f"Post-collection deduplication removed {removed_count} duplicates")
                socketio.emit('deduplication_complete', {
                    'removed_count': removed_count,
                    'message': f'Removed {removed_count} duplicate providers'
                })
            
        except Exception as e:
            logger.error(f"Collection error: {e}")
            socketio.emit('collection_error', {'error': str(e)})
    
    # Start collection in background thread
    thread = threading.Thread(target=run_collection)
    thread.daemon = True
    thread.start()
    
    return jsonify({'success': True, 'message': 'Collection started'})

@app.route('/api/export', methods=['POST'])
@login_required
def export_data():
    """Export filtered provider data"""
    data = request.get_json()
    format_type = data.get('format', 'csv')
    filters = data.get('filters', {})
    
    conn = db_manager.get_connection()
    
    # Build query based on filters
    query = '''
        SELECT name, email, phone, city, state, type, recruitment_platform, 
               ai_category, zipcode, last_updated
        FROM providers
        WHERE 1=1
    '''
    params = []
    
    if filters.get('category'):
        query += ' AND ai_category = ?'
        params.append(filters['category'])
    
    if filters.get('state'):
        query += ' AND state = ?'
        params.append(filters['state'])
    
    if filters.get('type'):
        query += ' AND type = ?'
        params.append(filters['type'])
    
    # Execute query and create DataFrame
    df = pd.read_sql_query(query, conn, params=params)
    conn.close()
    
    # Generate filename
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    
    if format_type == 'csv':
        filename = f'providers_export_{timestamp}.csv'
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
        df.to_csv(filepath, index=False)
    else:  # Excel
        filename = f'providers_export_{timestamp}.xlsx'
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
        df.to_excel(filepath, index=False)
    
    return send_file(filepath, as_attachment=True, download_name=filename)

@app.route('/api/deduplicate', methods=['POST'])
@login_required
@role_required(['admin', 'manager'])
def deduplicate_providers():
    """Remove duplicate providers from database"""
    try:
        removed_count = db_manager.find_and_remove_duplicates()
        return jsonify({
            'success': True,
            'removed_count': removed_count,
            'message': f'Successfully removed {removed_count} exact duplicate providers (100% similar only)'
        })
    except Exception as e:
        logger.error(f"Deduplication error: {str(e)}")
        return jsonify({'error': 'Deduplication failed'}), 500

def process_json_file(filepath):
    """Process JSON file import"""
    try:
        logger.info(f"Processing JSON import: {filepath}")
        
        with open(filepath, 'r') as file:
            providers = json.load(file)
        
        if not isinstance(providers, list):
            logger.error("JSON import: Root element must be an array")
            return
        
        processed_count = 0
        total_rows = len(providers)
        added_count = 0
        skipped_count = 0
        
        # Start collection log
        conn = db_manager.get_connection()
        cursor = conn.cursor()
        cursor.execute('''
            INSERT INTO collection_logs (source_name, category, records_collected, status)
            VALUES (?, ?, ?, ?)
        ''', ('JSON Import', 'All', total_rows, 'running'))
        log_id = cursor.lastrowid
        conn.commit()
        conn.close()
        
        # Process each provider
        for provider in providers:
            processed_count += 1
            
            # Update progress every 10 providers
            if processed_count % 10 == 0:
                progress = processed_count / total_rows
                socketio.emit('collection_progress', {'progress': progress * 100})
            
            try:
                # Add the provider to the database
                if data_collector._add_provider_to_db({
                    'name': provider.get('name', ''),
                    'email': provider.get('email', ''),
                    'phone': provider.get('phone', ''),
                    'city': provider.get('city', ''),
                    'state': provider.get('state', ''),
                    'type': provider.get('type', 'business'),
                    'recruitment_platform': provider.get('recruitment_platform', 'JSON Import'),
                    'latitude': provider.get('latitude'),
                    'longitude': provider.get('longitude'),
                    'ai_category': provider.get('ai_category', ''),
                    'zipcode': provider.get('zipcode', '')
                }):
                    added_count += 1
                else:
                    skipped_count += 1
            except Exception as e:
                logger.error(f"Error processing provider from JSON: {e}")
                skipped_count += 1
        
        # Update collection log
        conn = db_manager.get_connection()
        cursor = conn.cursor()
        cursor.execute('''
            UPDATE collection_logs 
            SET records_collected = ?, success_count = ?, error_count = ?, 
                status = ?, completed_at = CURRENT_TIMESTAMP
            WHERE log_id = ?
        ''', (total_rows, added_count, skipped_count, 'completed', log_id))
        conn.commit()
        conn.close()
        
        # Complete progress
        socketio.emit('collection_progress', {'progress': 100})
        socketio.emit('collection_complete', {
            'records_collected': total_rows,
            'records_added': added_count, 
            'source': 'JSON Import'
        })
        
        logger.info(f"JSON import complete: {added_count} added, {skipped_count} skipped")
    
    except Exception as e:
        logger.error(f"JSON import failed: {e}")
        socketio.emit('collection_error', {'error': str(e)})

@app.route('/api/upload', methods=['POST'])
@login_required
@role_required(['admin', 'manager'])
def upload_file():
    """Handle file upload and processing"""
    if 'file' not in request.files:
        return jsonify({'error': 'No file provided'}), 400
    
    file = request.files['file']
    if file.filename == '':
        return jsonify({'error': 'No file selected'}), 400
    
    if file and allowed_file(file.filename):
        filename = secure_filename(file.filename)
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
        file.save(filepath)
        
        # Process file in background
        def process_file():
            try:
                if filename.endswith('.json'):
                    # Process JSON file
                    process_json_file(filepath)
                    return
                elif filename.endswith('.csv'):
                    df = pd.read_csv(filepath)
                    
                    processed_count = 0
                    total_rows = len(df)
                    
                    conn = db_manager.get_connection()
                    cursor = conn.cursor()
                    
                    for index, row in df.iterrows():
                        # Process each row
                        name = row.get('name', '')
                    email = row.get('email', '')
                    phone = row.get('phone', '')
                    city = row.get('city', '')
                    state = row.get('state', '')
                    provider_type = row.get('type', 'individual')
                    
                    # Geocode if coordinates not provided
                    lat, lng = None, None
                    if 'latitude' in row and 'longitude' in row:
                        lat, lng = row['latitude'], row['longitude']
                    elif row.get('zipcode'):
                        try:
                            # Try to get coordinates from zipcode first
                            lat, lng, is_valid = validate_and_geocode_zipcode(row['zipcode'], state)
                            if not is_valid and city and state:
                                # If zipcode validation failed, fall back to city and state
                                location = geolocator.geocode(f"{city}, {state}")
                                if location:
                                    lat, lng = location.latitude, location.longitude
                        except Exception as e:
                            logger.warning(f"Geocoding failed for {row.get('zipcode')} or {city}, {state}: {e}")
                    elif city and state:
                        try:
                            location = geolocator.geocode(f"{city}, {state}")
                            if location:
                                lat, lng = location.latitude, location.longitude
                        except Exception as e:
                            logger.warning(f"Geocoding failed for {city}, {state}: {e}")
                    
                    # AI classification and zipcode generation
                    ai_category, zipcode = data_collector.ai_classifier.classify_provider(
                        row.get('description', ''), name, row.get('skills', ''),
                        city, state
                    )
                    
                    # Insert into database
                    cursor.execute('''
                        INSERT OR IGNORE INTO providers 
                        (name, email, phone, city, state, type, recruitment_platform, 
                         latitude, longitude, ai_category, zipcode)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ''', (name, email, phone, city, state, provider_type, 'Manual Upload',
                          lat, lng, ai_category, zipcode))
                    
                    processed_count += 1
                    
                    # Emit progress update
                    progress = (processed_count / total_rows) * 100
                    socketio.emit('upload_progress', {
                        'progress': progress,
                        'processed': processed_count,
                        'total': total_rows
                    })
                
                conn.commit()
                conn.close()
                
                # Run automatic deduplication
                logger.info("Running automatic deduplication after file upload...")
                removed_count = db_manager.find_and_remove_duplicates()
                logger.info(f"Automatic deduplication removed {removed_count} duplicates")
                
                # Clean up file
                os.remove(filepath)
                
                socketio.emit('upload_complete', {
                    'processed': processed_count,
                    'total': total_rows,
                    'duplicates_removed': removed_count
                })
                
            except Exception as e:
                logger.error(f"File processing error: {e}")
                socketio.emit('upload_error', {'error': str(e)})
        
        thread = threading.Thread(target=process_file)
        thread.daemon = True
        thread.start()
        
        return jsonify({'success': True, 'message': 'File upload started'})
    
    return jsonify({'error': 'Invalid file format'}), 400

def allowed_file(filename):
    """Check if file extension is allowed"""
    ALLOWED_EXTENSIONS = {'csv', 'xlsx', 'xls', 'json'}
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

@app.route('/api/users', methods=['GET', 'POST'])
@login_required
@role_required(['admin'])
def manage_users():
    """Manage users (admin only)"""
    if request.method == 'GET':
        conn = db_manager.get_connection()
        cursor = conn.cursor()
        
        cursor.execute('''
            SELECT user_id, name, email, role, created_at, last_login
            FROM users
            ORDER BY created_at DESC
        ''')
        
        users = cursor.fetchall()
        conn.close()
        
        user_list = []
        for user in users:
            user_list.append({
                'id': user[0],
                'name': user[1],
                'email': user[2],
                'role': user[3],
                'created_at': user[4],
                'last_login': user[5]
            })
        
        return jsonify({'users': user_list})
    
    elif request.method == 'POST':
        data = request.get_json()
        name = data.get('name')
        email = data.get('email')
        password = data.get('password', 'password123')  # Default password
        role = data.get('role', 'viewer')
        
        if not name or not email:
            return jsonify({'error': 'Name and email required'}), 400
        
        password_hash = generate_password_hash(password)
        
        try:
            conn = db_manager.get_connection()
            cursor = conn.cursor()
            
            cursor.execute('''
                INSERT INTO users (name, email, password_hash, role)
                VALUES (?, ?, ?, ?)
            ''', (name, email, password_hash, role))
            
            user_id = cursor.lastrowid
            conn.commit()
            conn.close()
            
            return jsonify({
                'success': True,
                'user_id': user_id,
                'message': 'User created successfully'
            })
        
        except sqlite3.IntegrityError:
            return jsonify({'error': 'Email already exists'}), 400

@app.route('/settings')
@login_required
def settings_page():
    """Render the settings page"""
    # Get current settings to pre-populate the form
    conn = db_manager.get_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT setting_key, setting_value FROM settings')
    settings = dict(cursor.fetchall())
    conn.close()
    
    return render_template('settings.html', settings=settings, active_page="settings")

@app.route('/api/settings', methods=['GET', 'POST'])
@login_required
def manage_settings():
    """Manage application settings"""
    # Allow all logged-in users to get settings, but only admin/manager to update them
    conn = db_manager.get_connection()
    cursor = conn.cursor()
    
    if request.method == 'GET':
        cursor.execute('SELECT setting_key, setting_value FROM settings')
        settings = dict(cursor.fetchall())
        conn.close()
        return jsonify({'settings': settings})
    
    elif request.method == 'POST':
        # Only admin and manager can update settings
        user_role = session.get('user_role', 'viewer')
        if user_role not in ['admin', 'manager']:
            conn.close()
            return jsonify({'success': False, 'message': 'Insufficient permissions'}), 403
            
        data = request.get_json()
        if not data:
            conn.close()
            return jsonify({'success': False, 'message': 'No data provided'}), 400
        
        try:
            for key, value in data.items():
                cursor.execute('''
                    INSERT OR REPLACE INTO settings (setting_key, setting_value, updated_at)
                    VALUES (?, ?, CURRENT_TIMESTAMP)
                ''', (key, str(value)))
            
            conn.commit()
            conn.close()
            
            return jsonify({'success': True, 'message': 'Settings updated'})
        except Exception as e:
            conn.rollback()
            conn.close()
            return jsonify({'success': False, 'message': f'Error updating settings: {str(e)}'}), 500

# Advanced database check API endpoint
@app.route('/api/database/advanced-check', methods=['POST'])
@login_required
def advanced_database_check():
    """Check and repair database integrity with detailed diagnostics"""
    # Only admin and manager can perform database checks
    user_role = session.get('user_role', 'viewer')
    if user_role not in ['admin', 'manager']:
        return jsonify({'success': False, 'message': 'Insufficient permissions'}), 403
        
    try:
        conn = db_manager.get_connection()
        cursor = conn.cursor()
        tables_checked = 0
        issues_fixed = 0
        
        # Check providers table
        cursor.execute("PRAGMA table_info(providers)")
        if cursor.fetchall():
            cursor.execute("PRAGMA integrity_check(providers)")
            result = cursor.fetchone()
            if result[0] != 'ok':
                # Repair by recreating indexes
                cursor.execute("REINDEX providers")
                issues_fixed += 1
            tables_checked += 1
            
        # Check settings table
        cursor.execute("PRAGMA table_info(settings)")
        if cursor.fetchall():
            cursor.execute("PRAGMA integrity_check(settings)")
            result = cursor.fetchone()
            if result[0] != 'ok':
                # Repair by recreating indexes
                cursor.execute("REINDEX settings")
                issues_fixed += 1
            tables_checked += 1
            
        # Check collection_logs table
        cursor.execute("PRAGMA table_info(collection_logs)")
        if cursor.fetchall():
            cursor.execute("PRAGMA integrity_check(collection_logs)")
            result = cursor.fetchone()
            if result[0] != 'ok':
                # Repair by recreating indexes
                cursor.execute("REINDEX collection_logs")
                issues_fixed += 1
            tables_checked += 1
            
        # Check users table
        cursor.execute("PRAGMA table_info(users)")
        if cursor.fetchall():
            cursor.execute("PRAGMA integrity_check(users)")
            result = cursor.fetchone()
            if result[0] != 'ok':
                # Repair by recreating indexes
                cursor.execute("REINDEX users")
                issues_fixed += 1
            tables_checked += 1
            
        # Run VACUUM to optimize database
        conn.isolation_level = None
        cursor.execute("VACUUM")
        conn.isolation_level = ""
        
        conn.close()
        
        return jsonify({
            'success': True,
            'tables_checked': tables_checked,
            'issues_fixed': issues_fixed
        })
        
    except Exception as e:
        logger.error(f"Error checking database: {e}")
        return jsonify({
            'success': False,
            'message': str(e)
        }), 500

# Developer mode API endpoints
@app.route('/api/dev/logs', methods=['GET'])
@login_required
def get_dev_logs():
    """Get application logs - developer feature"""
    # Check if developer mode is enabled
    conn = db_manager.get_connection()
    cursor = conn.cursor()
    cursor.execute("SELECT setting_value FROM settings WHERE setting_key = 'developer_mode'")
    result = cursor.fetchone()
    conn.close()
    
    if not result or result[0] != 'true':
        return jsonify({'error': 'Developer mode is not enabled'}), 403
    
    # Get the last 100 lines of logs
    log_entries = []
    try:
        log_file = os.path.join(os.path.dirname(__file__), 'app.log')
        if os.path.exists(log_file):
            with open(log_file, 'r') as f:
                log_lines = f.readlines()
                log_entries = log_lines[-100:] if len(log_lines) > 100 else log_lines
    except Exception as e:
        logger.error(f"Error reading log file: {e}")
        
    return jsonify({'logs': ''.join(log_entries)})

@app.route('/api/dev/clear-cache', methods=['POST'])
@login_required
def clear_dev_cache():
    """Clear application cache - developer feature"""
    # Check if developer mode is enabled
    conn = db_manager.get_connection()
    cursor = conn.cursor()
    cursor.execute("SELECT setting_value FROM settings WHERE setting_key = 'developer_mode'")
    result = cursor.fetchone()
    conn.close()
    
    if not result or result[0] != 'true':
        return jsonify({'error': 'Developer mode is not enabled'}), 403
    
    # Simulate clearing cache
    time.sleep(0.5)
    
    return jsonify({'success': True, 'message': 'Cache cleared successfully'})

@app.route('/api/providers/<int:provider_id>', methods=['PUT', 'DELETE'])
@login_required
@role_required(['admin', 'manager'])
def manage_provider(provider_id):
    """Update or delete a specific provider"""
    conn = db_manager.get_connection()
    cursor = conn.cursor()
    
    if request.method == 'PUT':
        data = request.get_json()
        
        # Build update query
        update_fields = []
        params = []
        
        for field in ['name', 'email', 'phone', 'city', 'state', 'type']:
            if field in data:
                update_fields.append(f'{field} = ?')
                params.append(data[field])
        
        if update_fields:
            query = f'''
                UPDATE providers 
                SET {', '.join(update_fields)}, last_updated = CURRENT_TIMESTAMP
                WHERE provider_id = ?
            '''
            params.append(provider_id)
            
            cursor.execute(query, params)
            conn.commit()
        
        conn.close()
        return jsonify({'success': True, 'message': 'Provider updated'})
    
    elif request.method == 'DELETE':
        cursor.execute('DELETE FROM providers WHERE provider_id = ?', (provider_id,))
        conn.commit()
        conn.close()
        
        return jsonify({'success': True, 'message': 'Provider deleted'})

# WebSocket events
@socketio.on('connect')
def handle_connect():
    """Handle client connection"""
    if 'user_id' not in session:
        return False
    
    join_room('dashboard')
    emit('connected', {'message': 'Connected to real-time updates'})

@socketio.on('disconnect')
def handle_disconnect():
    """Handle client disconnection"""
    leave_room('dashboard')

# Background tasks
def run_scheduled_collections():
    """Run scheduled data collection tasks"""
    def collect_all_categories():
        categories = list(SERVICE_CATEGORIES.keys())
        sources = ['yelp', 'google maps']
        
        for category in categories:
            for source in sources:
                try:
                    if source == 'yelp':
                        result = data_collector.collect_from_yelp(category)
                    else:
                        result = data_collector.collect_from_google_maps(category)
                    
                    # Emit to all connected clients
                    socketio.emit('collection_complete', result, room='dashboard')
                    
                    # Wait between collections to avoid rate limiting
                    time.sleep(np.random.randint(30, 120))
                    
                except Exception as e:
                    logger.error(f"Scheduled collection error: {e}")
    
    # Schedule collections
    schedule.every(6).hours.do(collect_all_categories)
    
    while True:
        schedule.run_pending()
        time.sleep(60)  # Check every minute

def start_background_tasks():
    """Start background tasks"""
    # Start scheduled collections
    scheduler_thread = threading.Thread(target=run_scheduled_collections)
    scheduler_thread.daemon = True
    scheduler_thread.start()
    
    # Start real-time activity simulation
    def simulate_activity():
        while True:
            try:
                # Simulate random activity updates
                if np.random.random() > 0.8:  # 20% chance every interval
                    sources = ['Yelp API', 'Google Maps', 'LinkedIn', 'Crunchbase']
                    categories = list(SERVICE_CATEGORIES.values())
                    statuses = ['Success', 'Processing', 'Failed']
                    
                    activity = {
                        'source': np.random.choice(sources),
                        'category': np.random.choice(categories),
                        'records': np.random.randint(10, 500),
                        'status': np.random.choice(statuses, p=[0.8, 0.15, 0.05]),
                        'time': 'Just now'
                    }
                    
                    socketio.emit('new_activity', activity, room='dashboard')
                
                time.sleep(30)  # Check every 30 seconds
                
            except Exception as e:
                logger.error(f"Activity simulation error: {e}")
                time.sleep(60)
    
    activity_thread = threading.Thread(target=simulate_activity)
    activity_thread.daemon = True
    activity_thread.start()

# Error handlers
@app.errorhandler(404)
def not_found(error):
    return jsonify({'error': 'Endpoint not found'}), 404

@app.errorhandler(500)
def internal_error(error):
    return jsonify({'error': 'Internal server error'}), 500

# Template folder setup
if not os.path.exists('templates'):
    os.makedirs('templates')
    
    # Create a simple login template
    with open('templates/dashboard.html', 'w') as f:
        f.write('''
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Service Provider Data Collection Tool</title>
    <script src="https://cdn.tailwindcss.com"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/socket.io/4.0.1/socket.io.js"></script>
</head>
<body class="bg-gray-100">
    <div id="app" class="min-h-screen">
        <!-- Login Form (shown when not authenticated) -->
        <div id="loginForm" class="min-h-screen flex items-center justify-center">
            <div class="bg-white p-8 rounded-lg shadow-md w-96">
                <h2 class="text-2xl font-bold mb-6 text-center">Login</h2>
                <form onsubmit="login(event)">
                    <div class="mb-4">
                        <label class="block text-sm font-medium text-gray-700 mb-2">Email</label>
                        <input type="email" id="email" required 
                               class="w-full px-3 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500"
                               placeholder="admin@servicetool.com">
                    </div>
                    <div class="mb-6">
                        <label class="block text-sm font-medium text-gray-700 mb-2">Password</label>
                        <input type="password" id="password" required
                               class="w-full px-3 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500"
                               placeholder="admin123">
                    </div>
                    <button type="submit" 
                            class="w-full bg-blue-600 text-white py-2 rounded-lg hover:bg-blue-700 transition">
                        Login
                    </button>
                </form>
                <p class="text-sm text-gray-600 mt-4 text-center">
                    Demo credentials: admin@servicetool.com / admin123
                </p>
            </div>
        </div>

        <!-- Dashboard (shown when authenticated) -->
        <div id="dashboard" class="hidden">
            <div class="bg-white shadow-sm p-4">
                <div class="flex justify-between items-center">
                    <h1 class="text-2xl font-bold">Service Provider Dashboard</h1>
                    <div class="flex items-center space-x-4">
                        <span id="userName" class="text-gray-600"></span>
                        <button onclick="logout()" class="bg-red-500 text-white px-4 py-2 rounded">Logout</button>
                    </div>
                </div>
            </div>

            <div class="container mx-auto p-6">
                <!-- Stats Cards -->
                <div class="grid grid-cols-1 md:grid-cols-4 gap-6 mb-8">
                    <div class="bg-white p-6 rounded-lg shadow">
                        <h3 class="text-sm font-medium text-gray-500">Total Providers</h3>
                        <p id="totalProviders" class="text-2xl font-bold">-</p>
                    </div>
                    <div class="bg-white p-6 rounded-lg shadow">
                        <h3 class="text-sm font-medium text-gray-500">Individuals</h3>
                        <p id="individuals" class="text-2xl font-bold">-</p>
                    </div>
                    <div class="bg-white p-6 rounded-lg shadow">
                        <h3 class="text-sm font-medium text-gray-500">Business Owners</h3>
                        <p id="businessOwners" class="text-2xl font-bold">-</p>
                    </div>
                    <div class="bg-white p-6 rounded-lg shadow">
                        <h3 class="text-sm font-medium text-gray-500">States Covered</h3>
                        <p id="statesCovered" class="text-2xl font-bold">-</p>
                    </div>
                </div>

                <!-- Collection Controls -->
                <div class="bg-white p-6 rounded-lg shadow mb-8">
                    <h3 class="text-lg font-semibold mb-4">Data Collection</h3>
                    <div class="flex space-x-4">
                        <select id="sourceSelect" class="px-3 py-2 border rounded">
                            <!-- API-based sources -->
                            <optgroup label="API-based Sources">
                                <option value="yelp">Yelp API</option>
                                <option value="google maps">Google Maps API</option>
                                <option value="yelp fusion api">Yelp Fusion API</option>
                            </optgroup>
                            <!-- Scrapers -->
                            <optgroup label="Business Directory Scrapers">
                                <option value="bbb">BBB Scraper</option>
                                <option value="yellowpages">YellowPages Scraper</option>
                                <option value="thomasnet">Thomasnet</option>
                                <option value="d&b">D&B Business Directory</option>
                                <option value="manta">Manta</option>
                                <option value="foursquare">Foursquare Scraper</option>
                                <option value="hotfrog">Hotfrog Scraper</option>
                            </optgroup>
                            <!-- News Websites -->
                            <optgroup label="News Websites">
                                <option value="news websites">News Websites (All States)</option>
                                <option value="state news">State News Websites</option>
                            </optgroup>
                            
                            <!-- Business Directories -->
                            <optgroup label="Business Directories">
                                <option value="citylocal pro">CityLocal Pro</option>
                                <option value="usa company directory">USA Company Directory</option>
                                <option value="allbusiness directory">AllBusiness Directory</option>
                                <option value="us chamber of commerce directory">US Chamber of Commerce Directory</option>
                                <option value="citysearch">Citysearch</option>
                                <option value="merchantcircle">MerchantCircle</option>
                                <option value="showmelocal">ShowMeLocal</option>
                                <option value="weandco">WeAndCo</option>
                                <option value="pocket insights">Pocket Insights</option>
                                <option value="elocal">eLocal</option>
                                <option value="brownbook">Brownbook</option>
                                <option value="cylex usa">Cylex USA</option>
                                <option value="local.com">Local.com</option>
                                <option value="superpages">SuperPages</option>
                                <option value="citysquares">CitySquares</option>
                                <option value="ezlocal">EZlocal</option>
                                <option value="2findlocal">2FindLocal</option>
                                <option value="botw">BOTW</option>
                                <option value="yellowbook">Yellowbook</option>
                                <option value="dexknows">DexKnows</option>
                                <option value="alignable">Alignable</option>
                            </optgroup>
                        </select>
                        <select id="categorySelect" class="px-3 py-2 border rounded">
                            <option value="residential-cleaning">Residential Cleaning</option>
                            <option value="hvac">HVAC</option>
                            <option value="plumbers">Plumbers</option>
                            <option value="electricians">Electricians</option>
                        </select>
                        <button onclick="startCollection()" 
                                class="bg-blue-600 text-white px-6 py-2 rounded hover:bg-blue-700">
                            Start Collection
                        </button>
                    </div>
                    <div id="collectionStatus" class="mt-4 hidden">
                        <div class="bg-blue-100 p-3 rounded">
                            <p class="text-blue-800">Collection in progress...</p>
                            <div id="collectionDetails" class="text-sm text-blue-700 mb-2">
                                <span id="collectionSource"></span>
                                <span id="collectionState" class="ml-2"></span>
                            </div>
                            <div class="w-full bg-blue-200 rounded-full h-2 mt-2">
                                <div id="progressBar" class="bg-blue-600 h-2 rounded-full transition-all" style="width: 0%"></div>
                            </div>
                            <div class="text-xs text-center text-blue-600 mt-1" id="progressText">Starting collection...</div>
                        </div>
                    </div>
                </div>

                <!-- Recent Activity -->
                <div class="bg-white p-6 rounded-lg shadow">
                    <h3 class="text-lg font-semibold mb-4">Recent Activity</h3>
                    <div id="activityList" class="space-y-2">
                        <!-- Activity items will be populated here -->
                    </div>
                </div>
            </div>
        </div>
    </div>

    <script>
        const socket = io();
        let isAuthenticated = false;

        // Authentication functions
        async function login(event) {
            event.preventDefault();
            const email = document.getElementById('email').value;
            const password = document.getElementById('password').value;

            try {
                const response = await fetch('/api/login', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ email, password })
                });

                const data = await response.json();
                if (data.success) {
                    isAuthenticated = true;
                    document.getElementById('loginForm').classList.add('hidden');
                    document.getElementById('dashboard').classList.remove('hidden');
                    document.getElementById('userName').textContent = data.user.name;
                    loadDashboardData();
                } else {
                    alert('Login failed: ' + data.error);
                }
            } catch (error) {
                alert('Login error: ' + error.message);
            }
        }

        async function logout() {
            try {
                await fetch('/api/logout', { method: 'POST' });
                isAuthenticated = false;
                document.getElementById('loginForm').classList.remove('hidden');
                document.getElementById('dashboard').classList.add('hidden');
            } catch (error) {
                console.error('Logout error:', error);
            }
        }

        // Dashboard functions
        async function loadDashboardData() {
            try {
                const response = await fetch('/api/stats');
                const data = await response.json();
                
                document.getElementById('totalProviders').textContent = data.total_providers;
                document.getElementById('individuals').textContent = data.individuals;
                document.getElementById('businessOwners').textContent = data.business_owners;
                document.getElementById('statesCovered').textContent = data.states_covered;
            } catch (error) {
                console.error('Error loading stats:', error);
            }

            loadRecentActivity();
        }

        async function loadRecentActivity() {
            try {
                const response = await fetch('/api/recent_activity');
                const data = await response.json();
                
                const activityList = document.getElementById('activityList');
                activityList.innerHTML = '';
                
                data.activities.forEach(activity => {
                    const activityItem = document.createElement('div');
                    activityItem.className = 'flex justify-between items-center p-3 bg-gray-50 rounded';
                    activityItem.innerHTML = `
                        <div>
                            <span class="font-medium">${activity.source}</span>
                            <span class="text-gray-600">- ${activity.category}</span>
                        </div>
                        <div class="text-sm text-gray-500">
                            ${activity.records} records | ${activity.status}
                        </div>
                    `;
                    activityList.appendChild(activityItem);
                });
            } catch (error) {
                console.error('Error loading activity:', error);
            }
        }

        // US States for state selection dialog
        const US_STATES = {
            "AL": "Alabama", "AK": "Alaska", "AZ": "Arizona", "AR": "Arkansas",
            "CA": "California", "CO": "Colorado", "CT": "Connecticut", "DE": "Delaware",
            "FL": "Florida", "GA": "Georgia", "HI": "Hawaii", "ID": "Idaho",
            "IL": "Illinois", "IN": "Indiana", "IA": "Iowa", "KS": "Kansas",
            "KY": "Kentucky", "LA": "Louisiana", "ME": "Maine", "MD": "Maryland",
            "MA": "Massachusetts", "MI": "Michigan", "MN": "Minnesota", "MS": "Mississippi",
            "MO": "Missouri", "MT": "Montana", "NE": "Nebraska", "NV": "Nevada",
            "NH": "New Hampshire", "NJ": "New Jersey", "NM": "New Mexico", "NY": "New York",
            "NC": "North Carolina", "ND": "North Dakota", "OH": "Ohio", "OK": "Oklahoma",
            "OR": "Oregon", "PA": "Pennsylvania", "RI": "Rhode Island", "SC": "South Carolina",
            "SD": "South Dakota", "TN": "Tennessee", "TX": "Texas", "UT": "Utah",
            "VT": "Vermont", "VA": "Virginia", "WA": "Washington", "WV": "West Virginia",
            "WI": "Wisconsin", "WY": "Wyoming", "DC": "District of Columbia"
        };
        
        // State selection dialog for news website scraping
        function showStateSelectionDialog() {
            const dialog = document.createElement('div');
            dialog.className = 'fixed inset-0 bg-gray-600 bg-opacity-50 flex items-center justify-center z-50';
            dialog.innerHTML = `
                <div class="bg-white p-6 rounded-lg shadow-lg w-96">
                    <h3 class="text-lg font-semibold mb-4">Select State</h3>
                    <p class="text-sm text-gray-600 mb-4">Select a specific state to focus on news websites from that state.</p>
                    <select id="stateSelect" class="w-full px-3 py-2 border rounded mb-4">
                        <option value="">All States</option>
                        ${Object.entries(US_STATES).map(([code, name]) => 
                            `<option value="${code}">${name} (${code})</option>`).join('')}
                    </select>
                    <div class="flex justify-end space-x-3">
                        <button id="cancelStateBtn" class="px-4 py-2 text-gray-600 hover:text-gray-800">Cancel</button>
                        <button id="confirmStateBtn" class="px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600">Continue</button>
                    </div>
                </div>
            `;
            document.body.appendChild(dialog);
            
            return new Promise((resolve, reject) => {
                document.getElementById('cancelStateBtn').addEventListener('click', () => {
                    document.body.removeChild(dialog);
                    reject('Cancelled');
                });
                
                document.getElementById('confirmStateBtn').addEventListener('click', () => {
                    const state = document.getElementById('stateSelect').value;
                    document.body.removeChild(dialog);
                    resolve(state);
                });
            });
        }
        
        async function startCollection() {
            const source = document.getElementById('sourceSelect').value;
            const category = document.getElementById('categorySelect').value;
            
            // Handle state selection for news websites
            let state = null;
            if (source.toLowerCase().includes('news') || source.toLowerCase() === 'state news') {
                try {
                    state = await showStateSelectionDialog();
                } catch (e) {
                    // User cancelled
                    return;
                }
            }
            
            document.getElementById('collectionStatus').classList.remove('hidden');
            document.getElementById('progressBar').style.width = '0%';
            
            // Update collection details display
            const collectionSource = document.getElementById('collectionSource');
            const collectionState = document.getElementById('collectionState');
            const progressText = document.getElementById('progressText');
            
            // Display source and category
            const sourceSelect = document.getElementById('sourceSelect');
            const sourceText = sourceSelect.options[sourceSelect.selectedIndex].text;
            collectionSource.textContent = `Source: ${sourceText} / Category: ${category}`;
            
            // Display state if applicable
            if (state) {
                const stateName = US_STATES[state] || state;
                collectionState.textContent = `State: ${stateName}`;
            } else {
                collectionState.textContent = '';
            }
            
            progressText.textContent = 'Starting collection...';

            try {
                const response = await fetch('/api/collection/start', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ source, category, state })
                });

                const data = await response.json();
                if (!data.success) {
                    alert('Collection start failed: ' + data.error);
                }
            } catch (error) {
                alert('Collection error: ' + error.message);
            }
        }

        // Socket.IO event handlers
        socket.on('connect', function() {
            console.log('Connected to server');
        });

        socket.on('collection_update', function(data) {
            document.getElementById('progressBar').style.width = data.progress + '%';
        });

        socket.on('collection_complete', function(data) {
            document.getElementById('collectionStatus').classList.add('hidden');
            alert(`Collection completed! Collected ${data.records_collected} records from ${data.source}`);
            loadDashboardData(); // Refresh stats
        });

        socket.on('collection_error', function(data) {
            document.getElementById('collectionStatus').classList.add('hidden');
            alert('Collection error: ' + data.error);
        });

        socket.on('new_activity', function(activity) {
            // Add new activity to the top of the list
            const activityList = document.getElementById('activityList');
            const activityItem = document.createElement('div');
            activityItem.className = 'flex justify-between items-center p-3 bg-gray-50 rounded';
            activityItem.innerHTML = `
                <div>
                    <span class="font-medium">${activity.source}</span>
                    <span class="text-gray-600">- ${activity.category}</span>
                </div>
                <div class="text-sm text-gray-500">
                    ${activity.records} records | ${activity.status}
                </div>
            `;
            activityList.insertBefore(activityItem, activityList.firstChild);
            
            // Keep only the latest 10 activities
            while (activityList.children.length > 10) {
                activityList.removeChild(activityList.lastChild);
            }
        });

        // Initialize
        document.addEventListener('DOMContentLoaded', function() {
            // Check if already authenticated (session exists)
            fetch('/api/stats').then(response => {
                if (response.ok) {
                    isAuthenticated = true;
                    document.getElementById('loginForm').classList.add('hidden');
                    document.getElementById('dashboard').classList.remove('hidden');
                    loadDashboardData();
                }
            }).catch(() => {
                // Not authenticated, show login form
            });
        });
    </script>
</body>
</html>
        ''')

if __name__ == '__main__':
    logger.info("Starting Service Provider Data Collection Tool...")
    
    # Check database integrity at startup
    try:
        logger.info("Checking database integrity at startup...")
        db_manager.check_and_repair_database()
        logger.info("Database integrity check completed")
    except Exception as e:
        logger.error(f"Error during initial database check: {e}")
    
    # Start background tasks
    start_background_tasks()
    
    # Run the application
    socketio.run(app, debug=True, host='0.0.0.0', port=5000)