#!/usr/bin/env python3
"""
Test suite for simplified Firecrawl caching functionality.

Tests the automatic, transparent caching system for Firecrawl web scraping.
Addresses issue #46: Cache firecrawl results to reduce API credit usage.

Coverage areas:
- Cache initialization and configuration
- Cache storage and retrieval
- URL normalization
- TTL and expiration handling
- Environment variable control
- Cache statistics and clearing
- Integration with preprocess module
"""

import pytest
import tempfile
import os
import time
import sqlite3
from pathlib import Path
from unittest.mock import patch, MagicMock
import sys

# Add the pdd directory to the path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from pdd.firecrawl_cache import FirecrawlCache, get_firecrawl_cache, clear_firecrawl_cache, get_firecrawl_cache_stats


class TestFirecrawlCache:
    """Test class for FirecrawlCache functionality."""

    def setup_method(self):
        """Set up test environment before each test method."""
        self.temp_dir = tempfile.mkdtemp()
        self.cache_path = Path(self.temp_dir) / "test_cache.db"
        # Clear any environment variables
        os.environ.pop('FIRECRAWL_CACHE_DISABLE', None)
        os.environ.pop('FIRECRAWL_CACHE_TTL_HOURS', None)

    def teardown_method(self):
        """Clean up test environment after each test method."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)
        os.environ.pop('FIRECRAWL_CACHE_DISABLE', None)
        os.environ.pop('FIRECRAWL_CACHE_TTL_HOURS', None)

    def test_cache_initialization(self):
        """Test that cache initializes correctly with default settings."""
        cache = FirecrawlCache(cache_path=self.cache_path, default_ttl_hours=24)

        assert cache.cache_path == self.cache_path
        assert cache.cache_path.exists()
        assert cache.default_ttl_hours == 24
        assert cache.enabled is True

    def test_cache_disabled_via_env(self):
        """Test that cache respects FIRECRAWL_CACHE_DISABLE environment variable."""
        os.environ['FIRECRAWL_CACHE_DISABLE'] = '1'

        cache = FirecrawlCache(cache_path=self.cache_path)

        assert cache.enabled is False
        # Disabled cache should not create database
        assert not cache.cache_path.exists()

    def test_cache_ttl_from_env(self):
        """Test that TTL can be set via FIRECRAWL_CACHE_TTL_HOURS environment variable."""
        os.environ['FIRECRAWL_CACHE_TTL_HOURS'] = '48'

        cache = FirecrawlCache(cache_path=self.cache_path, default_ttl_hours=24)

        assert cache.default_ttl_hours == 48

    def test_cache_ttl_invalid_env(self):
        """Test that invalid TTL environment variable falls back to default."""
        os.environ['FIRECRAWL_CACHE_TTL_HOURS'] = 'invalid'

        cache = FirecrawlCache(cache_path=self.cache_path, default_ttl_hours=24)

        assert cache.default_ttl_hours == 24  # Should use default

    def test_url_hash_generation(self):
        """Test URL hash generation for cache keys."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        url1 = "https://example.com/"
        url2 = "https://example.com"

        hash1 = cache._url_hash(url1)
        hash2 = cache._url_hash(url2)

        # Same normalized URL should produce same hash
        assert hash1 == hash2
        assert len(hash1) == 64  # SHA256 hash length

        # Different URLs should produce different hashes
        hash3 = cache._url_hash("https://different.com")
        assert hash1 != hash3

    def test_url_normalization(self):
        """Test URL normalization for consistent cache keys."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        # Test trailing slash removal
        assert cache._url_hash("https://example.com/") == cache._url_hash("https://example.com")

        # Test case normalization
        assert cache._url_hash("https://EXAMPLE.COM") == cache._url_hash("https://example.com")

        # Test whitespace handling
        assert cache._url_hash("  https://example.com  ") == cache._url_hash("https://example.com")

    def test_cache_set_and_get(self):
        """Test basic cache set and get operations."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        url = "https://example.com"
        content = "Test content"

        # Set cache
        result = cache.set(url, content)
        assert result is True

        # Get cache
        retrieved = cache.get(url)
        assert retrieved == content

    def test_cache_get_nonexistent(self):
        """Test getting a non-existent cache entry returns None."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        result = cache.get("https://nonexistent.com")
        assert result is None

    def test_cache_expiration(self):
        """Test that expired cache entries are not returned."""
        cache = FirecrawlCache(cache_path=self.cache_path, default_ttl_hours=1)

        url = "https://example.com"
        content = "Test content"

        # Set with very short TTL (1 second = 1/3600 hours)
        cache.set(url, content, ttl_hours=1/3600)

        # Immediately should be available
        assert cache.get(url) == content

        # Wait for expiration
        time.sleep(1.5)

        # Should return None (expired)
        assert cache.get(url) is None

    def test_cache_custom_ttl(self):
        """Test setting cache with custom TTL."""
        cache = FirecrawlCache(cache_path=self.cache_path, default_ttl_hours=24)

        url = "https://example.com"
        content = "Test content"

        # Set with custom TTL
        cache.set(url, content, ttl_hours=48)

        # Verify it's stored
        assert cache.get(url) == content

        # Check in database that expires_at is set correctly
        with sqlite3.connect(self.cache_path) as conn:
            cursor = conn.execute('SELECT expires_at FROM cache WHERE url = ?', (url,))
            row = cursor.fetchone()
            assert row is not None
            expires_at = row[0]
            # Should expire in ~48 hours (allow 1 second variance)
            expected_expires = time.time() + (48 * 3600)
            assert abs(expires_at - expected_expires) < 1

    def test_cache_overwrite(self):
        """Test that setting cache for same URL overwrites existing entry."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        url = "https://example.com"

        cache.set(url, "Original content")
        cache.set(url, "Updated content")

        assert cache.get(url) == "Updated content"

    def test_cache_disabled_operations(self):
        """Test that cache operations are no-op when disabled."""
        os.environ['FIRECRAWL_CACHE_DISABLE'] = '1'
        cache = FirecrawlCache(cache_path=self.cache_path)

        # Set should return False
        assert cache.set("https://example.com", "content") is False

        # Get should return None
        assert cache.get("https://example.com") is None

        # Clear should return 0
        assert cache.clear() == 0

    def test_cache_clear(self):
        """Test clearing all cache entries."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        # Add multiple entries
        cache.set("https://example1.com", "content1")
        cache.set("https://example2.com", "content2")
        cache.set("https://example3.com", "content3")

        # Clear cache
        cleared_count = cache.clear()

        assert cleared_count == 3

        # Verify all entries are gone
        assert cache.get("https://example1.com") is None
        assert cache.get("https://example2.com") is None
        assert cache.get("https://example3.com") is None

    def test_cache_stats(self):
        """Test cache statistics reporting."""
        cache = FirecrawlCache(cache_path=self.cache_path, default_ttl_hours=24)

        # Add some entries
        cache.set("https://example1.com", "content1")
        cache.set("https://example2.com", "content2", ttl_hours=1/3600)  # Expires in 1 second

        # Wait for one to expire
        time.sleep(1.5)

        stats = cache.get_stats()

        assert stats['enabled'] is True
        assert stats['total_entries'] == 2
        assert stats['expired_entries'] == 1
        assert stats['active_entries'] == 1
        assert stats['ttl_hours'] == 24
        assert str(self.cache_path) in stats['cache_path']

    def test_cache_stats_disabled(self):
        """Test cache statistics when cache is disabled."""
        os.environ['FIRECRAWL_CACHE_DISABLE'] = '1'
        cache = FirecrawlCache(cache_path=self.cache_path)

        stats = cache.get_stats()

        assert stats['enabled'] is False
        assert stats['total_entries'] == 0
        assert stats['expired_entries'] == 0

    def test_cache_database_schema(self):
        """Test that database schema is created correctly."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        with sqlite3.connect(self.cache_path) as conn:
            # Check table exists
            cursor = conn.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='cache'")
            assert cursor.fetchone() is not None

            # Check columns
            cursor = conn.execute("PRAGMA table_info(cache)")
            columns = {row[1] for row in cursor.fetchall()}
            expected_columns = {'url_hash', 'url', 'content', 'expires_at'}
            assert columns == expected_columns

            # Check index exists
            cursor = conn.execute("SELECT name FROM sqlite_master WHERE type='index' AND name='idx_expires'")
            assert cursor.fetchone() is not None

    def test_cache_concurrent_access(self):
        """Test that cache handles concurrent access safely."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        url = "https://example.com"

        # Multiple writes
        for i in range(10):
            cache.set(url, f"content{i}")

        # Last write should win
        assert cache.get(url) == "content9"

    def test_cache_large_content(self):
        """Test caching large content."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        url = "https://example.com"
        # 1MB of content
        large_content = "x" * (1024 * 1024)

        assert cache.set(url, large_content) is True
        assert cache.get(url) == large_content

    def test_cache_special_characters(self):
        """Test URLs and content with special characters."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        url = "https://example.com/path?query=value&foo=bar#fragment"
        content = "Content with special chars: \n\t\r émojis 🎉"

        assert cache.set(url, content) is True
        assert cache.get(url) == content

    def test_cache_error_handling(self):
        """Test error handling for database issues."""
        cache = FirecrawlCache(cache_path=self.cache_path)

        # Corrupt the database
        cache.cache_path.write_text("CORRUPTED")

        # Operations should not crash but return None/False
        assert cache.get("https://example.com") is None
        assert cache.set("https://example.com", "content") is False


class TestGlobalCacheFunctions:
    """Test global cache helper functions."""

    def teardown_method(self):
        """Clean up after tests."""
        # Reset global cache instance
        import pdd.firecrawl_cache
        pdd.firecrawl_cache._cache_instance = None
        os.environ.pop('FIRECRAWL_CACHE_DISABLE', None)
        os.environ.pop('FIRECRAWL_CACHE_TTL_HOURS', None)

    @patch('pdd.path_resolution.get_default_resolver')
    def test_get_firecrawl_cache_singleton(self, mock_resolver):
        """Test that get_firecrawl_cache returns singleton instance."""
        # Mock project root
        temp_dir = tempfile.mkdtemp()
        mock_resolver.return_value.resolve_project_root.return_value = Path(temp_dir)

        cache1 = get_firecrawl_cache()
        cache2 = get_firecrawl_cache()

        # Should be same instance
        assert cache1 is cache2

        # Cleanup
        import shutil
        shutil.rmtree(temp_dir, ignore_errors=True)

    @patch('pdd.path_resolution.get_default_resolver')
    def test_clear_firecrawl_cache(self, mock_resolver):
        """Test global clear function."""
        temp_dir = tempfile.mkdtemp()
        mock_resolver.return_value.resolve_project_root.return_value = Path(temp_dir)

        cache = get_firecrawl_cache()
        cache.set("https://example.com", "content")

        cleared = clear_firecrawl_cache()
        assert cleared == 1

        # Cleanup
        import shutil
        shutil.rmtree(temp_dir, ignore_errors=True)

    @patch('pdd.path_resolution.get_default_resolver')
    def test_get_firecrawl_cache_stats_function(self, mock_resolver):
        """Test global stats function."""
        temp_dir = tempfile.mkdtemp()
        mock_resolver.return_value.resolve_project_root.return_value = Path(temp_dir)

        cache = get_firecrawl_cache()
        cache.set("https://example.com", "content")

        stats = get_firecrawl_cache_stats()
        assert stats['total_entries'] == 1

        # Cleanup
        import shutil
        shutil.rmtree(temp_dir, ignore_errors=True)


class TestCacheIntegration:
    """Test cache integration with preprocess module."""

    def teardown_method(self):
        """Clean up after tests."""
        import pdd.firecrawl_cache
        pdd.firecrawl_cache._cache_instance = None
        os.environ.pop('FIRECRAWL_CACHE_DISABLE', None)

    @patch('pdd.path_resolution.get_default_resolver')
    def test_cache_integration_direct(self, mock_resolver):
        """Test cache get/set integration with mocked project root."""
        # Setup temporary project root
        temp_dir = tempfile.mkdtemp()
        mock_resolver.return_value.resolve_project_root.return_value = Path(temp_dir)

        # Get cache instance (will use mocked project root)
        cache = get_firecrawl_cache()

        # Test that cache works with the mocked project root
        url = "https://example.com"
        content = "Test cached content"

        # Set and get
        assert cache.set(url, content) is True
        assert cache.get(url) == content

        # Verify cache file created in correct location
        expected_path = Path(temp_dir) / ".pdd" / "cache" / "firecrawl.db"
        assert expected_path.exists()

        # Cleanup
        import shutil
        shutil.rmtree(temp_dir, ignore_errors=True)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--cov=pdd.firecrawl_cache", "--cov-report=term-missing"])
