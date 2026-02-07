#!/usr/bin/env python3
"""
Firecrawl caching module for PDD.

Provides automatic caching of Firecrawl web scraping results to reduce API usage.
Cache is transparent and automatic - users don't need to manage it manually.

Features:
- Persistent SQLite-based storage
- Configurable TTL (time-to-live) per request or globally
- URL normalization (removes tracking parameters, case-insensitive)
- Automatic cleanup of expired entries
- Size management (configurable limits on cache size and entries)
- Access tracking (monitors cache usage and efficiency)

Cache location: PROJECT_ROOT/.pdd/cache/firecrawl.db
Control: Set FIRECRAWL_CACHE_ENABLE=false to disable caching

Environment Variables:
- FIRECRAWL_CACHE_ENABLE: Enable/disable caching (default: true)
- FIRECRAWL_CACHE_TTL_HOURS: Default cache TTL in hours (default: 24)
- FIRECRAWL_CACHE_MAX_SIZE_MB: Maximum cache size in MB (default: 100)
- FIRECRAWL_CACHE_MAX_ENTRIES: Maximum number of entries (default: 1000)
- FIRECRAWL_CACHE_AUTO_CLEANUP: Enable automatic cleanup (default: true)

This addresses issue #46: Cache firecrawl results so it doesn't use up the API credit
"""

import os
import hashlib
import time
import sqlite3
import json
from pathlib import Path
from typing import Optional, Dict, Any
import logging

logger = logging.getLogger(__name__)

# Singleton cache instance
_cache_instance: Optional['FirecrawlCache'] = None


class FirecrawlCache:
    """
    Automatic cache for Firecrawl web scraping results with advanced features.

    Features:
    - Persistent caching with configurable TTL
    - URL normalization for consistent cache keys
    - Access tracking and statistics
    - Automatic cleanup and size management
    - LRU eviction when cache limits are reached
    """

    def __init__(self, cache_path: Optional[Path] = None, default_ttl_hours: int = 24):
        """
        Initialize the Firecrawl cache.

        Args:
            cache_path: Path to cache database file
            default_ttl_hours: Default cache duration in hours
        """
        self.cache_path = cache_path
        self.default_ttl_hours = default_ttl_hours

        # Load configuration from environment
        self._load_config()

        if not self.enabled:
            logger.info("Firecrawl caching disabled via FIRECRAWL_CACHE_ENABLE=false")
            return

        # Create cache directory
        self.cache_path.parent.mkdir(parents=True, exist_ok=True)

        # Initialize database
        self._init_db()

        logger.info(f"Firecrawl cache enabled at {self.cache_path} (TTL: {self.default_ttl_hours}h)")

    def _load_config(self):
        """Load cache configuration from environment variables."""
        # Cache behavior flags
        self.enabled = os.environ.get('FIRECRAWL_CACHE_ENABLE', 'true').lower() == 'true'
        self.auto_cleanup = os.environ.get('FIRECRAWL_CACHE_AUTO_CLEANUP', 'true').lower() == 'true'

        # TTL configuration
        ttl_env = os.getenv("FIRECRAWL_CACHE_TTL_HOURS")
        if ttl_env:
            try:
                self.default_ttl_hours = int(ttl_env)
            except ValueError:
                logger.warning(f"Invalid FIRECRAWL_CACHE_TTL_HOURS: {ttl_env}, using default {self.default_ttl_hours}")

        # Size management configuration
        self.max_cache_size_mb = int(os.getenv("FIRECRAWL_CACHE_MAX_SIZE_MB", "100"))
        self.max_entries = int(os.getenv("FIRECRAWL_CACHE_MAX_ENTRIES", "1000"))

        logger.debug(
            f"Cache config: TTL={self.default_ttl_hours}h, MaxSize={self.max_cache_size_mb}MB, "
            f"MaxEntries={self.max_entries}, Enabled={self.enabled}"
        )

    def _init_db(self):
        """Initialize SQLite database with cache table."""
        if not self.enabled:
            return

        with sqlite3.connect(self.cache_path) as conn:
            conn.execute('''
                CREATE TABLE IF NOT EXISTS cache (
                    url_hash TEXT PRIMARY KEY,
                    url TEXT NOT NULL,
                    content TEXT NOT NULL,
                    timestamp REAL NOT NULL,
                    expires_at REAL NOT NULL,
                    content_hash TEXT NOT NULL,
                    metadata TEXT,
                    access_count INTEGER DEFAULT 0,
                    last_accessed REAL DEFAULT 0
                )
            ''')
            # Indices for efficient queries
            conn.execute('CREATE INDEX IF NOT EXISTS idx_expires ON cache(expires_at)')
            conn.execute('CREATE INDEX IF NOT EXISTS idx_last_accessed ON cache(last_accessed)')
            conn.commit()

    def _normalize_url(self, url: str) -> str:
        """
        Normalize URL for consistent cache keys.

        Removes tracking parameters and normalizes case/format.

        Args:
            url: The URL to normalize

        Returns:
            Normalized URL string
        """
        # Remove trailing slashes and normalize whitespace
        url = url.strip().rstrip('/')

        # Convert to lowercase for case-insensitive matching (only the scheme and host)
        from urllib.parse import urlparse, urlunparse
        parsed = urlparse(url)
        url = urlunparse(parsed._replace(scheme=parsed.scheme.lower(), netloc=parsed.netloc.lower()))

        # Remove common tracking parameters that don't affect content
        if '?' in url:
            base_url, params = url.split('?', 1)
            # Keep only essential parameters, remove tracking ones
            essential_params = []
            tracking_prefixes = {'utm_source', 'utm_medium', 'utm_campaign', 'utm_term', 'utm_content',
                               'fbclid', 'gclid', 'ref', 'source', '_ga', '_gid'}
            for param in params.split('&'):
                if param:
                    param_name = param.split('=')[0].lower()
                    if param_name not in tracking_prefixes:
                        essential_params.append(param)

            if essential_params:
                url = f"{base_url}?{'&'.join(essential_params)}"
            else:
                url = base_url

        return url

    def _url_hash(self, url: str) -> str:
        """Generate cache key from normalized URL."""
        normalized = self._normalize_url(url)
        return hashlib.sha256(normalized.encode()).hexdigest()

    def _content_hash(self, content: str) -> str:
        """Generate hash for content to detect changes."""
        return hashlib.md5(content.encode()).hexdigest()

    def get(self, url: str) -> Optional[str]:
        """
        Get cached content for URL.

        Updates access statistics on cache hit.
        Returns None if not cached or expired.
        """
        if not self.enabled:
            return None

        url_hash = self._url_hash(url)
        current_time = time.time()

        try:
            with sqlite3.connect(self.cache_path) as conn:
                cursor = conn.execute(
                    'SELECT content, expires_at FROM cache WHERE url_hash = ?',
                    (url_hash,)
                )
                row = cursor.fetchone()

                if row:
                    content, expires_at = row
                    if expires_at > current_time:
                        # Cache hit - update access statistics
                        conn.execute(
                            'UPDATE cache SET access_count = access_count + 1, last_accessed = ? WHERE url_hash = ?',
                            (current_time, url_hash)
                        )
                        conn.commit()
                        logger.debug(f"Cache hit for {url}")
                        return content
                    else:
                        # Expired - delete it
                        conn.execute('DELETE FROM cache WHERE url_hash = ?', (url_hash,))
                        conn.commit()
                        logger.debug(f"Cache expired for {url}")

                logger.debug(f"Cache miss for {url}")
                return None

        except Exception as e:
            logger.warning(f"Cache read error for {url}: {e}")
            return None

    def set(self, url: str, content: str, ttl_hours: Optional[int] = None,
            metadata: Optional[Dict[str, Any]] = None) -> bool:
        """
        Store content in cache.

        Args:
            url: URL to cache
            content: Content to store
            ttl_hours: Cache duration (uses default if None)
            metadata: Additional metadata to store

        Returns:
            True if cached successfully
        """
        if not self.enabled:
            return False

        ttl = ttl_hours if ttl_hours is not None else self.default_ttl_hours
        url_hash = self._url_hash(url)
        content_hash = self._content_hash(content)
        current_time = time.time()
        expires_at = current_time + (ttl * 3600)

        if metadata is None:
            metadata = {}

        try:
            with sqlite3.connect(self.cache_path) as conn:
                # Check if entry exists
                cursor = conn.execute('SELECT url_hash FROM cache WHERE url_hash = ?', (url_hash,))
                exists = cursor.fetchone() is not None

                if exists:
                    # Update existing entry
                    conn.execute(
                        '''UPDATE cache SET content = ?, timestamp = ?, expires_at = ?,
                           content_hash = ?, metadata = ?, last_accessed = ?
                           WHERE url_hash = ?''',
                        (content, current_time, expires_at, content_hash,
                         json.dumps(metadata), current_time, url_hash)
                    )
                else:
                    # Insert new entry
                    conn.execute(
                        '''INSERT INTO cache
                           (url_hash, url, content, timestamp, expires_at, content_hash, metadata, last_accessed)
                           VALUES (?, ?, ?, ?, ?, ?, ?, ?)''',
                        (url_hash, url, content, current_time, expires_at,
                         content_hash, json.dumps(metadata), current_time)
                    )

                conn.commit()

                # Perform automatic cleanup if enabled
                if self.auto_cleanup:
                    self._cleanup_expired()

                logger.debug(f"Cached {url} (TTL: {ttl}h)")
                return True

        except Exception as e:
            logger.warning(f"Cache write error for {url}: {e}")
            return False

    def _cleanup_expired(self):
        """
        Remove expired entries and enforce size limits.

        Performs:
        1. Remove expired entries
        2. Enforce max_entries limit using LRU eviction
        3. Enforce max_size_mb limit using LRU eviction
        """
        current_time = time.time()

        try:
            with sqlite3.connect(self.cache_path) as conn:
                # Remove expired entries
                cursor = conn.execute('DELETE FROM cache WHERE expires_at <= ?', (current_time,))
                expired_count = cursor.rowcount

                if expired_count > 0:
                    logger.debug(f"Cleaned up {expired_count} expired cache entries")

                # Check if we need to enforce entry limit
                cursor = conn.execute('SELECT COUNT(*) FROM cache')
                total_entries = cursor.fetchone()[0]

                if total_entries > self.max_entries:
                    # Remove oldest entries by last_accessed (LRU)
                    excess = total_entries - self.max_entries
                    delete_cursor = conn.execute(
                        '''DELETE FROM cache WHERE url_hash IN (
                            SELECT url_hash FROM cache
                            ORDER BY last_accessed ASC
                            LIMIT ?
                        )''',
                        (excess,)
                    )
                    removed_count = delete_cursor.rowcount
                    logger.debug(f"Removed {removed_count} old entries to enforce entry limit")

                # Check if we need to enforce size limit
                cursor = conn.execute('SELECT SUM(LENGTH(content)) FROM cache')
                total_size_bytes = cursor.fetchone()[0] or 0
                total_size_mb = total_size_bytes / (1024 * 1024)
                max_size_bytes = self.max_cache_size_mb * 1024 * 1024

                if total_size_mb > self.max_cache_size_mb:
                    space_to_free = total_size_bytes - max_size_bytes
                    urls_to_delete = []
                    freed = 0

                    # Get entries sorted by last_accessed (LRU)
                    cursor = conn.execute(
                        'SELECT url_hash, LENGTH(content) as size FROM cache ORDER BY last_accessed ASC'
                    )
                    for url_hash, size in cursor.fetchall():
                        if freed >= space_to_free:
                            break
                        urls_to_delete.append(url_hash)
                        freed += size

                    if urls_to_delete:
                        placeholders = ','.join('?' * len(urls_to_delete))
                        size_delete_cursor = conn.execute(f'DELETE FROM cache WHERE url_hash IN ({placeholders})', urls_to_delete)
                        new_size_mb = (total_size_bytes - freed) / (1024 * 1024)
                        removed_count = size_delete_cursor.rowcount
                        logger.debug(
                            f"Removed {removed_count} entries to enforce size limit "
                            f"({total_size_mb:.2f}MB -> {new_size_mb:.2f}MB)"
                        )

                conn.commit()

        except Exception as e:
            logger.error(f"Error during cache cleanup: {e}")

    def clear(self) -> int:
        """
        Clear all cached entries.

        Returns:
            Number of entries deleted
        """
        if not self.enabled:
            return 0

        try:
            with sqlite3.connect(self.cache_path) as conn:
                cursor = conn.execute('SELECT COUNT(*) FROM cache')
                count = cursor.fetchone()[0]
                conn.execute('DELETE FROM cache')
                conn.commit()
                logger.info(f"Cleared {count} cache entries")
                return count
        except Exception as e:
            logger.error(f"Cache clear error: {e}")
            return 0

    def get_stats(self) -> Dict[str, Any]:
        """
        Get comprehensive cache statistics.

        Returns:
            Dictionary with cache statistics including:
            - Entry counts (total, active, expired)
            - Cache size in MB
            - Access patterns (average access count)
            - Configuration settings
        """
        if not self.enabled:
            return {
                'enabled': False,
                'total_entries': 0,
                'expired_entries': 0
            }

        try:
            with sqlite3.connect(self.cache_path) as conn:
                # Total entries
                cursor = conn.execute('SELECT COUNT(*) FROM cache')
                total = cursor.fetchone()[0]

                # Active vs expired entries
                current_time = time.time()
                cursor = conn.execute('SELECT COUNT(*) FROM cache WHERE expires_at > ?', (current_time,))
                active = cursor.fetchone()[0]
                expired = total - active

                # Total cache size
                cursor = conn.execute('SELECT SUM(LENGTH(content)) FROM cache')
                total_size_bytes = cursor.fetchone()[0] or 0
                total_size_mb = round(total_size_bytes / (1024 * 1024), 2)

                # Access statistics
                cursor = conn.execute('SELECT AVG(access_count) FROM cache')
                avg_access_count = cursor.fetchone()[0] or 0

                # Cache efficiency (percentage of active entries)
                efficiency = (active / total * 100) if total > 0 else 0

                return {
                    'enabled': True,
                    'total_entries': total,
                    'active_entries': active,
                    'expired_entries': expired,
                    'total_size_mb': total_size_mb,
                    'average_access_count': round(avg_access_count, 2),
                    'cache_efficiency': round(efficiency, 1),
                    'cache_path': str(self.cache_path),
                    'ttl_hours': self.default_ttl_hours,
                    'max_entries': self.max_entries,
                    'max_size_mb': self.max_cache_size_mb,
                    'auto_cleanup': self.auto_cleanup
                }
        except Exception as e:
            logger.error(f"Stats error: {e}")
            return {'error': str(e)}


def get_firecrawl_cache() -> FirecrawlCache:
    """
    Get the global Firecrawl cache instance.

    Cache is automatically initialized with PROJECT_ROOT/.pdd/cache/firecrawl.db
    """
    global _cache_instance

    if _cache_instance is None:
        # Import here to avoid circular dependency
        from pdd.path_resolution import get_default_resolver

        resolver = get_default_resolver()
        project_root = resolver.resolve_project_root()
        cache_path = project_root / ".pdd" / "cache" / "firecrawl.db"

        _cache_instance = FirecrawlCache(cache_path=cache_path)

    return _cache_instance


def clear_firecrawl_cache() -> int:
    """Clear the Firecrawl cache. Returns number of entries deleted."""
    cache = get_firecrawl_cache()
    return cache.clear()


def get_firecrawl_cache_stats() -> dict:
    """Get Firecrawl cache statistics."""
    cache = get_firecrawl_cache()
    return cache.get_stats()
