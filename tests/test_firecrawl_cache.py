#!/usr/bin/env python3
"""
Test suite for Firecrawl caching functionality.

This test suite validates the Firecrawl caching implementation that addresses
issue #46: Cache firecrawl results so it doesn't use up the API credit.

Tests cover:
- Cache storage and retrieval
- URL normalization
- TTL and expiration handling
- Cache cleanup and size management
- Integration with preprocess module
- CLI commands
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
        # Create a temporary directory for cache
        self.temp_dir = tempfile.mkdtemp()
        self.cache_path = Path(self.temp_dir) / "test_cache.db"
        self.cache = FirecrawlCache(cache_path=self.cache_path, default_ttl_hours=1)

    def teardown_method(self):
        """Clean up test environment after each test method."""
        # Clean up temporary directory
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)
        # Clean environment variables
        os.environ.pop('FIRECRAWL_CACHE_ENABLE', None)
        os.environ.pop('FIRECRAWL_CACHE_TTL_HOURS', None)
        os.environ.pop('FIRECRAWL_CACHE_MAX_SIZE_MB', None)
        os.environ.pop('FIRECRAWL_CACHE_MAX_ENTRIES', None)
        os.environ.pop('FIRECRAWL_CACHE_AUTO_CLEANUP', None)

    def test_cache_initialization(self):
        """Test that cache initializes correctly."""
        assert self.cache.cache_path.exists()
        assert self.cache.default_ttl_hours == 1
        assert self.cache.enabled is True

    def test_url_normalization(self):
        """Test URL normalization for consistent cache keys."""
        # Test basic normalization
        url1 = "https://example.com/"
        url2 = "https://example.com"
        assert self.cache._normalize_url(url1) == self.cache._normalize_url(url2)

        # Test case normalization
        url3 = "https://EXAMPLE.COM"
        assert self.cache._normalize_url(url1) == self.cache._normalize_url(url3)

        # Test parameter handling
        url4 = "https://example.com?utm_source=test&id=123"
        url5 = "https://example.com?id=123"
        # Should remove tracking parameters but keep essential ones
        normalized4 = self.cache._normalize_url(url4)
        normalized5 = self.cache._normalize_url(url5)
        assert "utm_source" not in normalized4
        assert "id=123" in normalized4

    def test_url_hash_generation(self):
        """Test URL hash generation for cache keys."""
        url1 = "https://example.com/"
        url2 = "https://example.com"

        hash1 = self.cache._url_hash(url1)
        hash2 = self.cache._url_hash(url2)

        # Same normalized URL should produce same hash
        assert hash1 == hash2
        assert len(hash1) == 64  # SHA256 hash length

    def test_content_hash_generation(self):
        """Test content hash generation."""
        content = "Test content"
        hash1 = self.cache._content_hash(content)
        hash2 = self.cache._content_hash(content)

        assert hash1 == hash2
        assert len(hash1) == 32  # MD5 hash length

    def test_cache_set_and_get(self):
        """Test basic cache set and get operations."""
        url = "https://example.com"
        content = "Test web content"

        # Initially should not be cached
        assert self.cache.get(url) is None

        # Set content in cache
        success = self.cache.set(url, content)
        assert success is True

        # Should now be retrievable
        cached_content = self.cache.get(url)
        assert cached_content == content

    def test_cache_expiration(self):
        """Test cache expiration based on TTL."""
        url = "https://example.com"
        content = "Test content"

        # Set with very short TTL
        self.cache.set(url, content, ttl_hours=0.001)  # ~3.6 seconds

        # Should be available immediately
        assert self.cache.get(url) == content

        # Wait for expiration
        time.sleep(4)

        # Should now be expired
        assert self.cache.get(url) is None

    def test_cache_metadata(self):
        """Test cache metadata storage and retrieval."""
        url = "https://example.com"
        content = "Test content"
        metadata = {"scraped_at": time.time(), "source": "test"}

        self.cache.set(url, content, metadata=metadata)

        # Verify content is cached
        cached_content = self.cache.get(url)
        assert cached_content == content

        # Verify metadata is stored (check database directly)
        with sqlite3.connect(self.cache.cache_path) as conn:
            cursor = conn.execute(
                'SELECT metadata FROM cache WHERE url = ?', (url,)
            )
            row = cursor.fetchone()
            assert row is not None
            import json
            stored_metadata = json.loads(row[0])
            assert stored_metadata["source"] == "test"

    def test_cache_access_counting(self):
        """Test that cache tracks access counts."""
        url = "https://example.com"
        content = "Test content"

        self.cache.set(url, content)

        # Access multiple times
        for _ in range(3):
            self.cache.get(url)

        # Check access count in database
        with sqlite3.connect(self.cache.cache_path) as conn:
            cursor = conn.execute(
                'SELECT access_count FROM cache WHERE url = ?', (url,)
            )
            row = cursor.fetchone()
            assert row is not None
            # First set counts as 1 access, then 3 more gets
            assert row[0] >= 3

    def test_cache_cleanup_expired(self):
        """Test automatic cleanup of expired entries."""
        url1 = "https://example1.com"
        url2 = "https://example2.com"
        content = "Test content"

        # Set one with short TTL, one with long TTL
        self.cache.set(url1, content, ttl_hours=0.001)  # Expires quickly
        self.cache.set(url2, content, ttl_hours=24)     # Long TTL

        # Wait for first to expire
        time.sleep(4.5)

        # Trigger cleanup
        self.cache._cleanup_expired()

        # First should be gone, second should remain
        assert self.cache.get(url1) is None
        assert self.cache.get(url2) == content

    def test_cache_size_limits(self):
        """Test cache size limit enforcement."""
        # Set a very small max entries limit
        self.cache.max_entries = 2

        # Add more entries than the limit
        for i in range(4):
            url = f"https://example{i}.com"
            content = f"Content {i}"
            self.cache.set(url, content)

        # Should only have max_entries in cache
        with sqlite3.connect(self.cache.cache_path) as conn:
            cursor = conn.execute('SELECT COUNT(*) FROM cache')
            count = cursor.fetchone()[0]
            assert count <= self.cache.max_entries

    def test_cache_clear(self):
        """Test cache clearing functionality."""
        url = "https://example.com"
        content = "Test content"

        # Add content to cache
        self.cache.set(url, content)
        assert self.cache.get(url) == content

        # Clear cache
        self.cache.clear()

        # Should be empty
        assert self.cache.get(url) is None

    def test_cache_stats(self):
        """Test cache statistics generation."""
        # Add some test data
        for i in range(3):
            url = f"https://example{i}.com"
            content = f"Content {i}"
            self.cache.set(url, content)

        # Get stats
        stats = self.cache.get_stats()

        assert stats['total_entries'] == 3
        assert stats['active_entries'] == 3
        assert stats['expired_entries'] == 0
        assert stats['enabled'] is True
        assert stats['ttl_hours'] == 1
        assert 'total_size_mb' in stats
        assert 'average_access_count' in stats
        assert 'cache_efficiency' in stats

    def test_cache_disabled(self):
        """Test cache behavior when disabled."""
        os.environ['FIRECRAWL_CACHE_ENABLE'] = 'false'
        cache_path = Path(self.temp_dir) / "disabled_cache.db"
        cache = FirecrawlCache(cache_path=cache_path)

        assert cache.enabled is False

        url = "https://example.com"
        content = "Test content"

        # Set should return False
        assert cache.set(url, content) is False

        # Get should return None
        assert cache.get(url) is None

    def test_environment_configuration(self):
        """Test cache configuration from environment variables."""
        with patch.dict(os.environ, {
            'FIRECRAWL_CACHE_TTL_HOURS': '48',
            'FIRECRAWL_CACHE_MAX_SIZE_MB': '200',
            'FIRECRAWL_CACHE_MAX_ENTRIES': '2000',
            'FIRECRAWL_CACHE_ENABLE': 'false',
            'FIRECRAWL_CACHE_AUTO_CLEANUP': 'false'
        }):
            # Create new cache instance to load env vars
            cache_path = Path(self.temp_dir) / "env_cache.db"
            cache = FirecrawlCache(cache_path=cache_path)

            assert cache.default_ttl_hours == 48
            assert cache.max_cache_size_mb == 200
            assert cache.max_entries == 2000
            assert cache.enabled is False
            assert cache.auto_cleanup is False

    def test_cache_database_schema(self):
        """Test that database schema is created correctly."""
        with sqlite3.connect(self.cache.cache_path) as conn:
            # Check table exists
            cursor = conn.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='cache'")
            assert cursor.fetchone() is not None

            # Check columns
            cursor = conn.execute("PRAGMA table_info(cache)")
            columns = {row[1] for row in cursor.fetchall()}
            expected_columns = {
                'url_hash', 'url', 'content', 'timestamp', 'expires_at',
                'content_hash', 'metadata', 'access_count', 'last_accessed'
            }
            assert columns == expected_columns

            # Check indices exist
            cursor = conn.execute("SELECT name FROM sqlite_master WHERE type='index' AND name='idx_expires'")
            assert cursor.fetchone() is not None
            cursor = conn.execute("SELECT name FROM sqlite_master WHERE type='index' AND name='idx_last_accessed'")
            assert cursor.fetchone() is not None


class TestGlobalCacheFunctions:
    """Test global cache functions."""

    def setup_method(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()
        # Reset global cache instance
        import pdd.firecrawl_cache
        pdd.firecrawl_cache._cache_instance = None

    def teardown_method(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)
        # Reset global cache instance
        import pdd.firecrawl_cache
        pdd.firecrawl_cache._cache_instance = None
        os.environ.pop('FIRECRAWL_CACHE_ENABLE', None)

    @patch('pdd.path_resolution.get_default_resolver')
    def test_get_firecrawl_cache(self, mock_resolver):
        """Test global cache instance retrieval."""
        mock_resolver.return_value.resolve_project_root.return_value = Path(self.temp_dir)
        cache = get_firecrawl_cache()
        assert isinstance(cache, FirecrawlCache)

    @patch('pdd.path_resolution.get_default_resolver')
    def test_clear_firecrawl_cache(self, mock_resolver):
        """Test global cache clearing."""
        mock_resolver.return_value.resolve_project_root.return_value = Path(self.temp_dir)
        cache = get_firecrawl_cache()
        cache.set("https://example.com", "test content")

        clear_firecrawl_cache()

        assert cache.get("https://example.com") is None

    @patch('pdd.path_resolution.get_default_resolver')
    def test_get_firecrawl_cache_stats(self, mock_resolver):
        """Test global cache stats retrieval."""
        mock_resolver.return_value.resolve_project_root.return_value = Path(self.temp_dir)
        stats = get_firecrawl_cache_stats()
        assert isinstance(stats, dict)
        assert 'total_entries' in stats


class TestCacheCLI:
    """Test cache CLI commands."""

    def setup_method(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()

    def teardown_method(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    def test_cli_stats_command(self, mock_get_stats):
        """Test CLI stats command."""
        from pdd.commands.firecrawl import firecrawl_cache
        from click.testing import CliRunner

        mock_stats = {
            'enabled': True,
            'total_entries': 5,
            'active_entries': 4,
            'expired_entries': 1,
            'total_size_mb': 2.5,
            'average_access_count': 3.2,
            'cache_efficiency': 80.0,
            'ttl_hours': 24,
            'max_entries': 1000,
            'max_size_mb': 100,
            'cache_path': str(Path(self.temp_dir) / "cache.db"),
            'auto_cleanup': True
        }
        mock_get_stats.return_value = mock_stats

        runner = CliRunner()
        result = runner.invoke(firecrawl_cache, ['stats'])
        assert result.exit_code == 0

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    def test_cli_clear_command(self, mock_clear_cache, mock_get_stats):
        """Test CLI clear command."""
        from pdd.commands.firecrawl import firecrawl_cache
        from click.testing import CliRunner

        mock_get_stats.return_value = {'enabled': True, 'total_entries': 3}
        mock_clear_cache.return_value = 3

        runner = CliRunner()
        # Use --yes flag to skip confirmation
        result = runner.invoke(firecrawl_cache, ['clear'], input='y\n')
        assert result.exit_code == 0

    def test_cli_info_command(self):
        """Test CLI info command."""
        from pdd.commands.firecrawl import firecrawl_cache
        from click.testing import CliRunner

        runner = CliRunner()
        result = runner.invoke(firecrawl_cache, ['info'])
        assert result.exit_code == 0

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    def test_cli_check_command_cached(self, mock_get_cache):
        """Test CLI check command with cached URL."""
        from pdd.commands.firecrawl import firecrawl_cache
        from click.testing import CliRunner

        mock_cache = MagicMock()
        mock_cache.enabled = True
        mock_cache.get.return_value = "Cached content"
        mock_get_cache.return_value = mock_cache

        runner = CliRunner()
        result = runner.invoke(firecrawl_cache, ['check', 'https://example.com'])
        assert result.exit_code == 0

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    def test_cli_check_command_not_cached(self, mock_get_cache):
        """Test CLI check command with non-cached URL."""
        from pdd.commands.firecrawl import firecrawl_cache
        from click.testing import CliRunner

        mock_cache = MagicMock()
        mock_cache.enabled = True
        mock_cache.get.return_value = None
        mock_get_cache.return_value = mock_cache

        runner = CliRunner()
        result = runner.invoke(firecrawl_cache, ['check', 'https://example.com'])
        assert result.exit_code == 0


def test_integration_full_workflow():
    """Test complete integration workflow."""
    with tempfile.TemporaryDirectory() as temp_dir:
        # Create cache
        cache_path = Path(temp_dir) / "cache.db"
        cache = FirecrawlCache(cache_path=cache_path, default_ttl_hours=1)

        # Test URL
        url = "https://example.com"
        content = "Test web content"

        # Initially not cached
        assert cache.get(url) is None

        # Cache content
        success = cache.set(url, content, metadata={"test": True})
        assert success is True

        # Retrieve from cache
        cached_content = cache.get(url)
        assert cached_content == content

        # Check stats
        stats = cache.get_stats()
        assert stats['total_entries'] == 1
        assert stats['active_entries'] == 1

        # Clear cache
        cache.clear()
        assert cache.get(url) is None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
