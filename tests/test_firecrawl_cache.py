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
from unittest.mock import patch, MagicMock, mock_open
import sys

# Add the pdd directory to the path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "pdd"))

from pdd.firecrawl_cache import FirecrawlCache, get_firecrawl_cache, clear_firecrawl_cache
from pdd.preprocess import process_web_tags
from pdd.firecrawl_cache import get_firecrawl_cache_stats
from pdd.firecrawl_cache_cli import firecrawl_cache
from click.testing import CliRunner
from unittest.mock import patch, MagicMock

class TestFirecrawlCache:
    """Test class for FirecrawlCache functionality."""

    def setup_method(self):
        """Set up test environment before each test method."""
        # Create a temporary directory for cache
        self.temp_dir = tempfile.mkdtemp()
        self.cache = FirecrawlCache(cache_dir=self.temp_dir, default_ttl_hours=1)

    def teardown_method(self):
        """Clean up test environment after each test method."""
        # Clean up temporary directory
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_cache_initialization(self):
        """Test that cache initializes correctly."""
        assert self.cache.cache_dir.exists()
        assert self.cache.db_path.exists()
        assert self.cache.default_ttl_hours == 1

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
        
        hash1 = self.cache._get_url_hash(url1)
        hash2 = self.cache._get_url_hash(url2)
        
        # Same normalized URL should produce same hash
        assert hash1 == hash2
        assert len(hash1) == 64  # SHA256 hash length

    def test_content_hash_generation(self):
        """Test content hash generation."""
        content = "Test content"
        hash1 = self.cache._get_content_hash(content)
        hash2 = self.cache._get_content_hash(content)
        
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
        #time.sleep(0.005)  # 5ms should be enough; <not enough>
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
        with sqlite3.connect(self.cache.db_path) as conn:
            cursor = conn.execute(
                'SELECT metadata FROM cache_entries WHERE url = ?', (url,)
            )
            row = cursor.fetchone()
            assert row is not None
            stored_metadata = eval(row[0])  # Simple eval for test
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
        with sqlite3.connect(self.cache.db_path) as conn:
            cursor = conn.execute(
                'SELECT access_count FROM cache_entries WHERE url = ?', (url,)
            )
            row = cursor.fetchone()
            assert row is not None
            assert row[0] == 3

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
        with sqlite3.connect(self.cache.db_path) as conn:
            cursor = conn.execute('SELECT COUNT(*) FROM cache_entries')
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
        assert stats['cache_enabled'] is True
        assert stats['default_ttl_hours'] == 1

    def test_cache_disabled(self):
        """Test cache behavior when disabled."""
        # Disable cache
        self.cache.enable_cache = False
        
        url = "https://example.com"
        content = "Test content"
        
        # Set should return False
        assert self.cache.set(url, content) is False
        
        # Get should return None
        assert self.cache.get(url) is None

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
            cache = FirecrawlCache(cache_dir=self.temp_dir)
            
            assert cache.default_ttl_hours == 48
            assert cache.max_cache_size_mb == 200
            assert cache.max_entries == 2000
            assert cache.enable_cache is False
            assert cache.auto_cleanup is False


class TestGlobalCacheFunctions:
    """Test global cache functions."""

    def setup_method(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()

    def teardown_method(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_get_firecrawl_cache(self):
        """Test global cache instance retrieval."""
        cache = get_firecrawl_cache()
        assert isinstance(cache, FirecrawlCache)

    def test_clear_firecrawl_cache(self):
        """Test global cache clearing."""
        cache = get_firecrawl_cache()
        cache.set("https://example.com", "test content")
        
        clear_firecrawl_cache()
        
        assert cache.get("https://example.com") is None

    def test_get_firecrawl_cache_stats(self):
        """Test global cache stats retrieval."""
        stats = get_firecrawl_cache_stats()
        assert isinstance(stats, dict)
        assert 'total_entries' in stats


class TestPreprocessIntegration:
    """Test integration with preprocess module."""

    def setup_method(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()

    def teardown_method(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    @patch('pdd.preprocess.get_firecrawl_cache')
    def test_process_web_tags_with_cache_hit(self, mock_get_cache):
        """Test web tag processing with cache hit."""
        # Mock cache to return cached content
        mock_cache = MagicMock()
        mock_cache.get.return_value = "Cached content"
        mock_get_cache.return_value = mock_cache
        
        text = "Test <web>https://example.com</web> content"
        result = process_web_tags(text, recursive=False)
        
        # Should use cached content
        assert "Cached content" in result
        mock_cache.get.assert_called_once_with("https://example.com")

    @patch('pdd.preprocess.get_firecrawl_cache')
    @patch('pdd.preprocess.FirecrawlApp')
    def test_process_web_tags_with_cache_miss(self, mock_firecrawl_app, mock_get_cache):
        """Test web tag processing with cache miss."""
        # Mock cache to return None (cache miss)
        mock_cache = MagicMock()
        mock_cache.get.return_value = None
        mock_cache.set.return_value = True
        mock_get_cache.return_value = mock_cache
        
        # Mock Firecrawl response
        mock_response = MagicMock()
        mock_response.markdown = "Scraped content"
        mock_app = MagicMock()
        mock_app.scrape_url.return_value = mock_response
        mock_firecrawl_app.return_value = mock_app
        
        # Mock environment
        with patch.dict(os.environ, {'FIRECRAWL_API_KEY': 'test-key'}):
            text = "Test <web>https://example.com</web> content"
            result = process_web_tags(text, recursive=False)
            
            # Should scrape and cache content
            assert "Scraped content" in result
            mock_cache.get.assert_called_once_with("https://example.com")
            mock_cache.set.assert_called_once()
            mock_app.scrape_url.assert_called_once()

    def test_process_web_tags_recursive_mode(self):
        """Test web tag processing in recursive mode."""
        text = "Test <web>https://example.com</web> content"
        result = process_web_tags(text, recursive=True)
        
        # Should return original text unchanged in recursive mode
        assert result == text

    @patch.dict(os.environ, {}, clear=True)
    def test_process_web_tags_missing_api_key(self):
        """Test web tag processing with missing API key."""
        text = "Test <web>https://example.com</web> content"
        result = process_web_tags(text, recursive=False)
        
        # Should return error message
        assert "FIRECRAWL_API_KEY not set" in result

    @patch('pdd.preprocess.FirecrawlApp')
    def test_process_web_tags_import_error(self, mock_firecrawl_app):
        """Test web tag processing with Firecrawl import error."""
        # Mock import error
        mock_firecrawl_app.side_effect = ImportError("No module named 'firecrawl'")
        
        text = "Test <web>https://example.com</web> content"
        result = process_web_tags(text, recursive=False)
        
        # Should return error message
        assert "firecrawl-py package not installed" in result


class TestCacheCLI:
    """Test cache CLI commands."""

    def setup_method(self):
        """Set up test environment."""
        self.temp_dir = tempfile.mkdtemp()

    def teardown_method(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    @patch('pdd.firecrawl_cache_cli.get_firecrawl_cache_stats')
    def test_cli_stats_command(self, mock_get_stats):
        """Test CLI stats command."""
        
        mock_stats = {
            'total_entries': 5,
            'active_entries': 4,
            'expired_entries': 1,
            'total_size_mb': 2.5,
            'average_access_count': 3.2,
            'cache_enabled': True,
            'default_ttl_hours': 24,
            'max_entries': 1000,
            'max_size_mb': 100
        }
        mock_get_stats.return_value = mock_stats
        
        runner = CliRunner()
        result = runner.invoke(firecrawl_cache, ['stats'])
        assert result.exit_code == 0

    @patch('pdd.firecrawl_cache_cli.get_firecrawl_cache')
    def test_cli_clear_command(self, mock_get_cache):
        """Test CLI clear command."""
        
        mock_cache = MagicMock()
        mock_cache.get_stats.return_value = {'total_entries': 3}
        mock_get_cache.return_value = mock_cache
        
        # Mock click.confirm to return True
        with patch('click.confirm', return_value=True):
            runner = CliRunner()
            result = runner.invoke(firecrawl_cache, ['clear'])
            assert result.exit_code == 0
            mock_cache.clear.assert_called_once()

    def test_cli_info_command(self):
        """Test CLI info command."""
        runner = CliRunner()
        result = runner.invoke(firecrawl_cache, ['info'])
        assert result.exit_code == 0

    @patch('pdd.firecrawl_cache_cli.get_firecrawl_cache')
    def test_cli_check_command_cached(self, mock_get_cache):
        """Test CLI check command with cached URL."""
        
        mock_cache = MagicMock()
        mock_cache.get.return_value = "Cached content"
        mock_get_cache.return_value = mock_cache
        
        runner = CliRunner()
        result = runner.invoke(firecrawl_cache, ['check', 'https://example.com'])
        assert result.exit_code == 0

    @patch('pdd.firecrawl_cache_cli.get_firecrawl_cache')
    def test_cli_check_command_not_cached(self, mock_get_cache):
        """Test CLI check command with non-cached URL."""
        
        mock_cache = MagicMock()
        mock_cache.get.return_value = None
        mock_get_cache.return_value = mock_cache
        
        runner = CliRunner()
        result = runner.invoke(firecrawl_cache, ['check', 'https://example.com'])
        assert result.exit_code == 0


def test_integration_full_workflow():
    """Test complete integration workflow."""
    with tempfile.TemporaryDirectory() as temp_dir:
        # Create cache
        cache = FirecrawlCache(cache_dir=temp_dir, default_ttl_hours=1)
        
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
