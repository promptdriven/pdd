#!/usr/bin/env python3
"""
Firecrawl caching module for PDD.

This module provides caching functionality for Firecrawl web scraping results
to reduce API credit usage by avoiding redundant requests for the same URLs.

Features:
- File-based caching with configurable expiration
- URL-based cache keys with normalization
- Configurable cache duration via environment variables
- Automatic cache cleanup and management
- Support for different cache strategies (time-based, size-based)

This addresses issue #46: Cache firecrawl results so it doesn't use up the API credit
"""

import os
import json
import hashlib
import time
import sqlite3
from pathlib import Path
from typing import Optional, Dict, Any, Union
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
import logging

logger = logging.getLogger(__name__)

@dataclass
class CacheEntry:
    """Represents a cached Firecrawl result."""
    url: str
    content: str
    timestamp: float
    expires_at: float
    content_hash: str
    metadata: Dict[str, Any]

class FirecrawlCache:
    """
    Manages caching of Firecrawl web scraping results.
    
    Provides persistent caching to reduce API credit usage by storing
    scraped content and serving it for subsequent requests within the
    configured cache duration.
    """
    
    def __init__(self, cache_dir: Optional[Union[str, Path]] = None, 
                 default_ttl_hours: int = 24):
        """
        Initialize the Firecrawl cache.
        
        Args:
            cache_dir: Directory to store cache files. Defaults to project cache dir.
            default_ttl_hours: Default time-to-live for cache entries in hours.
        """
        self.default_ttl_hours = default_ttl_hours
        
        # Set up cache directory
        if cache_dir is None:
            # Use project root cache directory
            project_root = Path(__file__).parent.parent
            cache_dir = project_root / "cache" / "firecrawl"
        else:
            cache_dir = Path(cache_dir)
            
        self.cache_dir = cache_dir
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        
        # Cache database file
        self.db_path = self.cache_dir / "firecrawl_cache.db"
        
        # Initialize database
        self._init_database()
        
        # Load configuration from environment
        self._load_config()
        
        logger.info(f"Firecrawl cache initialized at {self.cache_dir}")
    
    def _load_config(self):
        """Load cache configuration from environment variables."""
        # Cache TTL configuration
        self.default_ttl_hours = int(os.environ.get('FIRECRAWL_CACHE_TTL_HOURS', self.default_ttl_hours))
        
        # Cache size limits
        self.max_cache_size_mb = int(os.environ.get('FIRECRAWL_CACHE_MAX_SIZE_MB', 100))
        self.max_entries = int(os.environ.get('FIRECRAWL_CACHE_MAX_ENTRIES', 1000))
        
        # Cache behavior flags
        self.enable_cache = os.environ.get('FIRECRAWL_CACHE_ENABLE', 'true').lower() == 'true'
        self.auto_cleanup = os.environ.get('FIRECRAWL_CACHE_AUTO_CLEANUP', 'true').lower() == 'true'
        
        logger.debug(f"Cache config: TTL={self.default_ttl_hours}h, MaxSize={self.max_cache_size_mb}MB, "
                    f"MaxEntries={self.max_entries}, Enabled={self.enable_cache}")
    
    def _init_database(self):
        """Initialize the SQLite database for cache storage."""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute('''
                CREATE TABLE IF NOT EXISTS cache_entries (
                    url_hash TEXT PRIMARY KEY,
                    url TEXT NOT NULL,
                    content TEXT NOT NULL,
                    timestamp REAL NOT NULL,
                    expires_at REAL NOT NULL,
                    content_hash TEXT NOT NULL,
                    metadata TEXT NOT NULL,
                    access_count INTEGER DEFAULT 0,
                    last_accessed REAL DEFAULT 0
                )
            ''')
            
            # Create index for efficient cleanup queries
            conn.execute('''
                CREATE INDEX IF NOT EXISTS idx_expires_at ON cache_entries(expires_at)
            ''')
            
            conn.execute('''
                CREATE INDEX IF NOT EXISTS idx_last_accessed ON cache_entries(last_accessed)
            ''')
            
            conn.commit()
    
    def _normalize_url(self, url: str) -> str:
        """
        Normalize URL for consistent cache keys.
        
        Args:
            url: The URL to normalize
            
        Returns:
            Normalized URL string
        """
        # Remove trailing slashes and normalize
        url = url.strip().rstrip('/')
        
        # Convert to lowercase for case-insensitive matching
        url = url.lower()
        
        # Remove common tracking parameters that don't affect content
        # This is a basic implementation - could be extended
        if '?' in url:
            base_url, params = url.split('?', 1)
            # Keep only essential parameters, remove tracking ones
            essential_params = []
            for param in params.split('&'):
                if param and not any(track in param.lower() for track in 
                                   ['utm_', 'fbclid', 'gclid', 'ref=', 'source=']):
                    essential_params.append(param)
            
            if essential_params:
                url = f"{base_url}?{'&'.join(essential_params)}"
            else:
                url = base_url
        
        return url
    
    def _get_url_hash(self, url: str) -> str:
        """Generate a hash for the URL to use as cache key."""
        normalized_url = self._normalize_url(url)
        return hashlib.sha256(normalized_url.encode('utf-8')).hexdigest()
    
    def _get_content_hash(self, content: str) -> str:
        """Generate a hash for the content to detect changes."""
        return hashlib.md5(content.encode('utf-8')).hexdigest()
    
    def get(self, url: str) -> Optional[str]:
        """
        Retrieve cached content for a URL.
        
        Args:
            url: The URL to retrieve from cache
            
        Returns:
            Cached content if available and not expired, None otherwise
        """
        if not self.enable_cache:
            return None
            
        url_hash = self._get_url_hash(url)
        current_time = time.time()
        
        try:
            with sqlite3.connect(self.db_path) as conn:
                cursor = conn.execute('''
                    SELECT content, expires_at, content_hash, metadata
                    FROM cache_entries 
                    WHERE url_hash = ? AND expires_at > ?
                ''', (url_hash, current_time))
                
                row = cursor.fetchone()
                if row:
                    content, expires_at, content_hash, metadata_json = row
                    
                    # Update access statistics
                    conn.execute('''
                        UPDATE cache_entries 
                        SET access_count = access_count + 1, last_accessed = ?
                        WHERE url_hash = ?
                    ''', (current_time, url_hash))
                    conn.commit()
                    
                    # Parse metadata
                    try:
                        metadata = json.loads(metadata_json) if metadata_json else {}
                    except json.JSONDecodeError:
                        metadata = {}
                    
                    logger.debug(f"Cache hit for {url} (expires in {expires_at - current_time:.0f}s)")
                    return content
                else:
                    logger.debug(f"Cache miss for {url}")
                    return None
                    
        except Exception as e:
            logger.error(f"Error retrieving from cache for {url}: {e}")
            return None
    
    def set(self, url: str, content: str, ttl_hours: Optional[int] = None, 
            metadata: Optional[Dict[str, Any]] = None) -> bool:
        """
        Store content in cache for a URL.
        
        Args:
            url: The URL to cache
            content: The content to cache
            ttl_hours: Time-to-live in hours (uses default if None)
            metadata: Additional metadata to store with the entry
            
        Returns:
            True if successfully cached, False otherwise
        """
        if not self.enable_cache:
            return False
            
        if ttl_hours is None:
            ttl_hours = self.default_ttl_hours
            
        url_hash = self._get_url_hash(url)
        content_hash = self._get_content_hash(content)
        current_time = time.time()
        expires_at = current_time + (ttl_hours * 3600)
        
        if metadata is None:
            metadata = {}
        
        try:
            with sqlite3.connect(self.db_path) as conn:
                # Check if entry already exists
                cursor = conn.execute('SELECT url_hash FROM cache_entries WHERE url_hash = ?', (url_hash,))
                exists = cursor.fetchone() is not None
                
                if exists:
                    # Update existing entry
                    conn.execute('''
                        UPDATE cache_entries 
                        SET content = ?, timestamp = ?, expires_at = ?, 
                            content_hash = ?, metadata = ?, last_accessed = ?
                        WHERE url_hash = ?
                    ''', (content, current_time, expires_at, content_hash, 
                          json.dumps(metadata), current_time, url_hash))
                else:
                    # Insert new entry
                    conn.execute('''
                        INSERT INTO cache_entries 
                        (url_hash, url, content, timestamp, expires_at, content_hash, metadata, last_accessed)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    ''', (url_hash, url, content, current_time, expires_at, 
                          content_hash, json.dumps(metadata), current_time))
                
                conn.commit()
                
                # Perform cleanup if enabled
                if self.auto_cleanup:
                    self._cleanup_expired()
                
                logger.debug(f"Cached content for {url} (TTL: {ttl_hours}h)")
                return True
                
        except Exception as e:
            logger.error(f"Error caching content for {url}: {e}")
            return False
    
    def _cleanup_expired(self):
        """Remove expired entries from cache."""
        current_time = time.time()
        
        try:
            with sqlite3.connect(self.db_path) as conn:
                # Remove expired entries
                cursor = conn.execute('DELETE FROM cache_entries WHERE expires_at <= ?', (current_time,))
                expired_count = cursor.rowcount
                
                if expired_count > 0:
                    logger.debug(f"Cleaned up {expired_count} expired cache entries")
                
                # Check if we need to enforce size limits
                cursor = conn.execute('SELECT COUNT(*) FROM cache_entries')
                total_entries = cursor.fetchone()[0]
                
                if total_entries > self.max_entries:
                    # Remove oldest entries (by last_accessed)
                    excess = total_entries - self.max_entries
                    cursor = conn.execute('''
                        DELETE FROM cache_entries 
                        WHERE url_hash IN (
                            SELECT url_hash FROM cache_entries 
                            ORDER BY last_accessed ASC 
                            LIMIT ?
                        )
                    ''', (excess,))
                    
                    removed_count = cursor.rowcount
                    logger.debug(f"Removed {removed_count} old entries to enforce size limit")
                
                conn.commit()
                
        except Exception as e:
            logger.error(f"Error during cache cleanup: {e}")
    
    def clear(self):
        """Clear all cached entries."""
        try:
            with sqlite3.connect(self.db_path) as conn:
                cursor = conn.execute('DELETE FROM cache_entries')
                count = cursor.rowcount
                conn.commit()
                logger.info(f"Cleared {count} cache entries")
        except Exception as e:
            logger.error(f"Error clearing cache: {e}")
    
    def get_stats(self) -> Dict[str, Any]:
        """Get cache statistics."""
        try:
            with sqlite3.connect(self.db_path) as conn:
                cursor = conn.execute('SELECT COUNT(*) FROM cache_entries')
                total_entries = cursor.fetchone()[0]
                
                cursor = conn.execute('SELECT COUNT(*) FROM cache_entries WHERE expires_at > ?', (time.time(),))
                active_entries = cursor.fetchone()[0]
                
                cursor = conn.execute('SELECT SUM(LENGTH(content)) FROM cache_entries')
                total_size_bytes = cursor.fetchone()[0] or 0
                
                cursor = conn.execute('SELECT AVG(access_count) FROM cache_entries')
                avg_access_count = cursor.fetchone()[0] or 0
                
                return {
                    'total_entries': total_entries,
                    'active_entries': active_entries,
                    'expired_entries': total_entries - active_entries,
                    'total_size_mb': round(total_size_bytes / (1024 * 1024), 2),
                    'average_access_count': round(avg_access_count, 2),
                    'cache_enabled': self.enable_cache,
                    'default_ttl_hours': self.default_ttl_hours,
                    'max_entries': self.max_entries,
                    'max_size_mb': self.max_cache_size_mb
                }
        except Exception as e:
            logger.error(f"Error getting cache stats: {e}")
            return {'error': str(e)}

# Global cache instance
_firecrawl_cache = None

def get_firecrawl_cache() -> FirecrawlCache:
    """Get the global Firecrawl cache instance."""
    global _firecrawl_cache
    if _firecrawl_cache is None:
        _firecrawl_cache = FirecrawlCache()
    return _firecrawl_cache

def clear_firecrawl_cache():
    """Clear the global Firecrawl cache."""
    global _firecrawl_cache
    if _firecrawl_cache is not None:
        _firecrawl_cache.clear()

def get_firecrawl_cache_stats() -> Dict[str, Any]:
    """Get statistics for the global Firecrawl cache."""
    cache = get_firecrawl_cache()
    return cache.get_stats()
