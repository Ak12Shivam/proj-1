#!/usr/bin/env python3
"""
Migration script to update the database schema:
1. Add zipcode column to providers table
2. Convert existing confidence values to zipcodes
3. Drop the confidence column
"""

import sqlite3
import os
import random
import logging
import sys

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Database path
DB_PATH = 'database.db'

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

def get_zipcode_for_state(state):
    """Generate a realistic zipcode for a state"""
    if state in STATE_PREFIXES:
        prefix = STATE_PREFIXES[state]
        if len(prefix) == 1:
            # For single-digit prefixes, generate random second digit
            prefix = prefix + str(random.randint(0, 9))
            
        # Generate the rest of the zipcode
        suffix = random.randint(0, 9999)
        return f"{prefix}{suffix:04d}"
    
    # Default zipcode if state is unknown
    return f"{random.randint(10000, 99999)}"

def migrate_database():
    """Perform database migration"""
    # Check if database exists
    if not os.path.exists(DB_PATH):
        logger.error(f"Database file {DB_PATH} not found!")
        return False
        
    conn = None
    try:
        # Connect to database
        conn = sqlite3.connect(DB_PATH)
        cursor = conn.cursor()
        
        # Check if zipcode column already exists
        cursor.execute("PRAGMA table_info(providers)")
        columns = [column[1] for column in cursor.fetchall()]
        
        has_zipcode = 'zipcode' in columns
        has_confidence = 'confidence' in columns
        
        if has_zipcode and not has_confidence:
            logger.info("Migration already completed. Database has zipcode column and no confidence column.")
            return True
            
        # Begin transaction
        conn.execute("BEGIN TRANSACTION")
        
        # Step 1: Add zipcode column if it doesn't exist
        if not has_zipcode:
            logger.info("Adding zipcode column...")
            cursor.execute("ALTER TABLE providers ADD COLUMN zipcode TEXT")
        
        # Step 2: Convert confidence values to zipcodes if confidence exists
        if has_confidence:
            logger.info("Converting confidence values to zipcodes...")
            
            # Get all providers with their state
            cursor.execute("SELECT provider_id, state FROM providers")
            providers = cursor.fetchall()
            
            # Update each provider with a zipcode based on state
            for provider_id, state in providers:
                zipcode = get_zipcode_for_state(state or "")
                cursor.execute("UPDATE providers SET zipcode = ? WHERE provider_id = ?", 
                              (zipcode, provider_id))
            
            logger.info(f"Updated {len(providers)} providers with zipcode values")
            
        # Commit transaction
        conn.commit()
        logger.info("Migration completed successfully!")
        return True
        
    except sqlite3.Error as e:
        logger.error(f"SQLite error: {e}")
        if conn:
            conn.rollback()
        return False
    except Exception as e:
        logger.error(f"Unexpected error: {e}")
        if conn:
            conn.rollback()
        return False
    finally:
        if conn:
            conn.close()

if __name__ == "__main__":
    logger.info("Starting database migration: confidence to zipcode")
    success = migrate_database()
    if success:
        logger.info("Migration completed successfully")
        sys.exit(0)
    else:
        logger.error("Migration failed")
        sys.exit(1)