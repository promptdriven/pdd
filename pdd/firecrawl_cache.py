#!/usr/bin/env python3
"""
Firecrawl caching module for PDD.

Provides automatic caching of Firecrawl web scraping results to reduce API usage.
Cache is transparent and automatic - users don't need to manage it manually.

Cache location: PROJECT_ROOT/.pdd/cache/firecrawl.db
Control: Set FIRECRAWL_CACHE_DISABLE=1 to disable caching

This addresses issue #46: Cache firecrawl results so it doesn't use up the API credit
"""

import os
import hashlib
import time
import sqlite3
from pathlib import Path
from typing import Optional
import logging

logger = logging.getLogger(__name__)

# Singleton cache instance
_cache_instance: Optional['FirecrawlCache'] = None


class FirecrawlCache:
    """
    Simple, automatic cache for Firecrawl web scraping results.

    Caches scraped content with configurable TTL. Expired entries are
    automatically skipped when accessed.
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
        self.enabled = os.getenv("FIRECRAWL_CACHE_DISABLE") != "1"

        if not self.enabled:
            logger.info("Firecrawl caching disabled via FIRECRAWL_CACHE_DISABLE=1")
            return

        # Load TTL from environment if set
        ttl_env = os.getenv("FIRECRAWL_CACHE_TTL_HOURS")
        if ttl_env:
            try:
                self.default_ttl_hours = int(ttl_env)
            except ValueError:
                logger.warning(f"Invalid FIRECRAWL_CACHE_TTL_HOURS value: {ttl_env}, using default {self.default_ttl_hours}")

        # Create cache directory
        self.cache_path.parent.mkdir(parents=True, exist_ok=True)

        # Initialize database
        self._init_db()

        logger.info(f"Firecrawl cache enabled at {self.cache_path} (TTL: {self.default_ttl_hours}h)")

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
                    expires_at REAL NOT NULL
                )
            ''')
            # Index for cleanup queries
            conn.execute('CREATE INDEX IF NOT EXISTS idx_expires ON cache(expires_at)')
            conn.commit()

    def _url_hash(self, url: str) -> str:
        """Generate cache key from URL."""
        # Normalize: lowercase, strip trailing slash
        normalized = url.strip().rstrip('/').lower()
        return hashlib.sha256(normalized.encode()).hexdigest()

    def get(self, url: str) -> Optional[str]:
        """
        Get cached content for URL.

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
                        logger.debug(f"Cache hit for {url}")
                        return content
                    else:
                        # Expired - delete it
                        conn.execute('DELETE FROM cache WHERE url_hash = ?', (url_hash,))
                        conn.commit()
                        logger.debug(f"Cache expired for {url}")

                return None

        except Exception as e:
            logger.warning(f"Cache read error for {url}: {e}")
            return None

    def set(self, url: str, content: str, ttl_hours: Optional[int] = None) -> bool:
        """
        Store content in cache.

        Args:
            url: URL to cache
            content: Content to store
            ttl_hours: Cache duration (uses default if None)

        Returns:
            True if cached successfully
        """
        if not self.enabled:
            return False

        ttl = ttl_hours if ttl_hours is not None else self.default_ttl_hours
        url_hash = self._url_hash(url)
        expires_at = time.time() + (ttl * 3600)

        try:
            with sqlite3.connect(self.cache_path) as conn:
                conn.execute(
                    'REPLACE INTO cache (url_hash, url, content, expires_at) VALUES (?, ?, ?, ?)',
                    (url_hash, url, content, expires_at)
                )
                conn.commit()
                logger.debug(f"Cached {url} (TTL: {ttl}h)")
                return True

        except Exception as e:
            logger.warning(f"Cache write error for {url}: {e}")
            return False

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

    def get_stats(self) -> dict:
        """Get basic cache statistics."""
        if not self.enabled:
            return {
                'enabled': False,
                'total_entries': 0,
                'expired_entries': 0
            }

        try:
            with sqlite3.connect(self.cache_path) as conn:
                cursor = conn.execute('SELECT COUNT(*) FROM cache')
                total = cursor.fetchone()[0]

                current_time = time.time()
                cursor = conn.execute('SELECT COUNT(*) FROM cache WHERE expires_at <= ?', (current_time,))
                expired = cursor.fetchone()[0]

                return {
                    'enabled': True,
                    'total_entries': total,
                    'expired_entries': expired,
                    'active_entries': total - expired,
                    'cache_path': str(self.cache_path),
                    'ttl_hours': self.default_ttl_hours
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
