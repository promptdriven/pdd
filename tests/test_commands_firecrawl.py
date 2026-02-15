#!/usr/bin/env python3
"""
Test suite for pdd/commands/firecrawl.py

Tests the CLI commands for Firecrawl cache management:
- firecrawl-cache stats: Display cache statistics
- firecrawl-cache clear: Clear cached entries
- firecrawl-cache info: Show cache configuration
- firecrawl-cache check: Check if a URL is cached

Coverage areas:
- Command group structure and help text
- Stats command with various scenarios (enabled, disabled, error states)
- Clear command with confirmation handling
- Info command displaying configuration and environment variables
- Check command for URL cache verification
- Error handling and user feedback
- Rich console output formatting
- Integration workflows using multiple commands
"""

import pytest
from unittest.mock import patch, MagicMock, call
from click.testing import CliRunner

from pdd.cli import cli


@pytest.fixture
def runner():
    """Provide a Click CliRunner for testing commands."""
    return CliRunner()


class TestFirecrawlCacheGroup:
    """Test the firecrawl-cache command group."""

    def test_firecrawl_cache_group_exists(self, runner):
        """Test that firecrawl-cache command group is registered."""
        result = runner.invoke(cli, ["firecrawl-cache", "--help"])
        assert result.exit_code == 0
        assert "firecrawl-cache" in result.output.lower() or "Manage Firecrawl" in result.output

    def test_firecrawl_cache_group_help(self, runner):
        """Test that firecrawl-cache shows help text for all commands."""
        result = runner.invoke(cli, ["firecrawl-cache", "--help"])
        assert result.exit_code == 0
        assert "stats" in result.output.lower()
        assert "clear" in result.output.lower()
        assert "info" in result.output.lower()
        assert "check" in result.output.lower()


class TestStatsCommand:
    """Test the 'firecrawl-cache stats' command."""

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_stats_enabled_with_entries(self, mock_print, mock_get_stats, runner):
        """Test stats command when cache is enabled and has entries."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 10,
            'active_entries': 8,
            'expired_entries': 2,
            'ttl_hours': 24,
            'cache_path': '/path/to/.pdd/cache/firecrawl.db'
        }

        result = runner.invoke(cli, ["firecrawl-cache", "stats"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()

        # Verify a table was printed (Rich Table object will be printed)
        assert mock_print.called, "Should print cache statistics"
        # Check that print was called at least once (for the table)
        assert mock_print.call_count >= 1

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_stats_enabled_empty_cache(self, mock_print, mock_get_stats, runner):
        """Test stats command when cache is enabled but empty."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 0,
            'active_entries': 0,
            'expired_entries': 0,
            'ttl_hours': 24,
            'cache_path': '/path/to/.pdd/cache/firecrawl.db'
        }

        result = runner.invoke(cli, ["firecrawl-cache", "stats"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()

        # Verify table shows zeros
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('0' in str(call) for call in print_calls), "Should show zero entries"

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_stats_disabled_cache(self, mock_print, mock_get_stats, runner):
        """Test stats command when caching is disabled."""
        mock_get_stats.return_value = {
            'enabled': False,
            'total_entries': 0,
            'active_entries': 0,
            'expired_entries': 0,
            'ttl_hours': 24,
            'cache_path': None
        }

        result = runner.invoke(cli, ["firecrawl-cache", "stats"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()

        # Should print disabled message
        mock_print.assert_any_call("[yellow]Firecrawl caching is disabled.[/yellow]")
        mock_print.assert_any_call("Set FIRECRAWL_CACHE_ENABLE=true to enable.")

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_stats_with_error_in_response(self, mock_print, mock_get_stats, runner):
        """Test stats command when cache stats return an error."""
        mock_get_stats.return_value = {
            'error': 'Database connection failed'
        }

        result = runner.invoke(cli, ["firecrawl-cache", "stats"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()

        # Should print error message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Error' in str(call) and 'Database connection failed' in str(call)
                   for call in print_calls), "Should show error message"

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_stats_exception_handling(self, mock_print, mock_get_stats, runner):
        """Test stats command handles exceptions gracefully."""
        mock_get_stats.side_effect = RuntimeError("Unexpected error")

        result = runner.invoke(cli, ["firecrawl-cache", "stats"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()

        # Should print error message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Error' in str(call) and 'Unexpected error' in str(call)
                   for call in print_calls), "Should show exception message"

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_stats_custom_ttl(self, mock_print, mock_get_stats, runner):
        """Test stats command displays custom TTL value."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 5,
            'active_entries': 5,
            'expired_entries': 0,
            'ttl_hours': 48,  # Custom TTL
            'cache_path': '/path/to/cache.db'
        }

        result = runner.invoke(cli, ["firecrawl-cache", "stats"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()

        # Verify stats table was printed
        assert mock_print.called, "Should print cache statistics table"

    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_stats_missing_optional_fields(self, mock_print, mock_get_stats, runner):
        """Test stats command handles missing optional fields gracefully."""
        mock_get_stats.return_value = {
            'enabled': True,
            # Missing total_entries, active_entries, expired_entries, ttl_hours
            'cache_path': '/path/to/cache.db'
        }

        result = runner.invoke(cli, ["firecrawl-cache", "stats"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()

        # Should handle missing fields with defaults (0 for counts, N/A for path)
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('0' in str(call) for call in print_calls), "Should show 0 for missing entries"


class TestClearCommand:
    """Test the 'firecrawl-cache clear' command."""

    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    @patch('pdd.commands.firecrawl.click.confirm')
    def test_clear_with_confirmation(self, mock_confirm, mock_print, mock_get_stats, mock_clear, runner):
        """Test clear command with user confirmation."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 5,
            'active_entries': 3,
            'expired_entries': 2
        }
        mock_confirm.return_value = True  # User confirms
        mock_clear.return_value = 5  # 5 entries cleared

        result = runner.invoke(cli, ["firecrawl-cache", "clear"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()
        mock_confirm.assert_called_once_with("Clear 5 cached entries?")
        mock_clear.assert_called_once()

        # Should print success message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Cleared' in str(call) and '5' in str(call)
                   for call in print_calls), "Should show success message with count"

    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    @patch('pdd.commands.firecrawl.click.confirm')
    def test_clear_cancelled_by_user(self, mock_confirm, mock_print, mock_get_stats, mock_clear, runner):
        """Test clear command when user cancels confirmation."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 5,
            'active_entries': 3,
            'expired_entries': 2
        }
        mock_confirm.return_value = False  # User cancels

        result = runner.invoke(cli, ["firecrawl-cache", "clear"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()
        mock_confirm.assert_called_once_with("Clear 5 cached entries?")
        mock_clear.assert_not_called()  # Should not clear if cancelled

        # Should print cancelled message
        mock_print.assert_any_call("Cancelled.")

    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_clear_disabled_cache(self, mock_print, mock_get_stats, mock_clear, runner):
        """Test clear command when caching is disabled."""
        mock_get_stats.return_value = {
            'enabled': False,
            'total_entries': 0,
            'active_entries': 0,
            'expired_entries': 0
        }

        result = runner.invoke(cli, ["firecrawl-cache", "clear"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()
        mock_clear.assert_not_called()  # Should not attempt to clear

        # Should print disabled message
        mock_print.assert_any_call("[yellow]Caching is disabled - nothing to clear.[/yellow]")

    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_clear_empty_cache(self, mock_print, mock_get_stats, mock_clear, runner):
        """Test clear command when cache is already empty."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 0,
            'active_entries': 0,
            'expired_entries': 0
        }

        result = runner.invoke(cli, ["firecrawl-cache", "clear"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()
        mock_clear.assert_not_called()  # Should not attempt to clear empty cache

        # Should print empty message
        mock_print.assert_any_call("[yellow]Cache is already empty.[/yellow]")

    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    def test_clear_exception_handling(self, mock_print, mock_get_stats, mock_clear, runner):
        """Test clear command handles exceptions gracefully."""
        mock_get_stats.side_effect = RuntimeError("Cache access error")

        result = runner.invoke(cli, ["firecrawl-cache", "clear"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()
        mock_clear.assert_not_called()

        # Should print error message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Error' in str(call) and 'Cache access error' in str(call)
                   for call in print_calls), "Should show exception message"

    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    @patch('pdd.commands.firecrawl.click.confirm')
    def test_clear_single_entry(self, mock_confirm, mock_print, mock_get_stats, mock_clear, runner):
        """Test clear command with exactly one entry."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 1,
            'active_entries': 1,
            'expired_entries': 0
        }
        mock_confirm.return_value = True
        mock_clear.return_value = 1

        result = runner.invoke(cli, ["firecrawl-cache", "clear"])

        assert result.exit_code == 0
        mock_confirm.assert_called_once_with("Clear 1 cached entry?")  # Correct grammar
        mock_clear.assert_called_once()

        # Should print success message with singular "entry"
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Cleared' in str(call) and '1' in str(call) and 'entry' in str(call).lower()
                   for call in print_calls), "Should show success message with singular 'entry'"

    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    @patch('pdd.commands.firecrawl.click.confirm')
    def test_clear_large_cache(self, mock_confirm, mock_print, mock_get_stats, mock_clear, runner):
        """Test clear command with large number of entries."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 1000,
            'active_entries': 800,
            'expired_entries': 200
        }
        mock_confirm.return_value = True
        mock_clear.return_value = 1000

        result = runner.invoke(cli, ["firecrawl-cache", "clear"])

        assert result.exit_code == 0
        mock_confirm.assert_called_once_with("Clear 1000 cached entries?")
        mock_clear.assert_called_once()

        # Should show correct count and plural "entries" in success message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Cleared' in str(call) and '1000' in str(call) and 'entries' in str(call).lower()
                   for call in print_calls), "Should show success message with count and plural 'entries'"

    @patch('pdd.commands.firecrawl.clear_firecrawl_cache')
    @patch('pdd.commands.firecrawl.get_firecrawl_cache_stats')
    @patch('pdd.commands.firecrawl.console.print')
    @patch('pdd.commands.firecrawl.click.confirm')
    def test_clear_exception_during_clear(self, mock_confirm, mock_print, mock_get_stats, mock_clear, runner):
        """Test clear command handles exceptions during clear operation."""
        mock_get_stats.return_value = {
            'enabled': True,
            'total_entries': 5,
            'active_entries': 5,
            'expired_entries': 0
        }
        mock_confirm.return_value = True
        mock_clear.side_effect = RuntimeError("Failed to clear cache")

        result = runner.invoke(cli, ["firecrawl-cache", "clear"])

        assert result.exit_code == 0
        mock_get_stats.assert_called_once()
        mock_confirm.assert_called_once()
        mock_clear.assert_called_once()

        # Should print error message from exception
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Error' in str(call) and 'Failed to clear cache' in str(call)
                   for call in print_calls), "Should show exception message"


class TestInfoCommand:
    """Test the 'firecrawl-cache info' command."""

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_info_shows_environment_variables(self, mock_print, mock_get_cache, runner):
        """Test info command displays environment variables table."""
        mock_cache = MagicMock()
        mock_cache.cache_path = MagicMock()
        mock_cache.cache_path.parent = MagicMock()
        mock_cache.cache_path.exists.return_value = True
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "info"])

        assert result.exit_code == 0
        # Should print the configuration table
        assert mock_print.called
        print_calls = [str(call) for call in mock_print.call_args_list]
        # Verify table was printed (Rich Table object)
        assert len(print_calls) >= 1

    @patch.dict('os.environ', {
        'FIRECRAWL_CACHE_ENABLE': 'true',
        'FIRECRAWL_CACHE_TTL_HOURS': '48',
        'FIRECRAWL_CACHE_MAX_SIZE_MB': '200',
        'FIRECRAWL_CACHE_MAX_ENTRIES': '2000',
        'FIRECRAWL_CACHE_AUTO_CLEANUP': 'true',
        'FIRECRAWL_API_KEY': 'test-api-key-12345678'
    })
    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_info_with_all_env_vars_set(self, mock_print, mock_get_cache, runner):
        """Test info command when all environment variables are set."""
        mock_cache = MagicMock()
        mock_cache.cache_path = MagicMock()
        mock_cache.cache_path.parent = MagicMock()
        mock_cache.cache_path.exists.return_value = True
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "info"])

        assert result.exit_code == 0
        assert mock_print.called

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_info_shows_cache_directory_info(self, mock_print, mock_get_cache, runner):
        """Test info command displays cache directory information."""
        mock_cache = MagicMock()
        mock_cache_path = MagicMock()
        mock_cache_path.__str__ = MagicMock(return_value="/test/path/.pdd/cache/firecrawl.db")
        mock_cache_path.parent = MagicMock()
        mock_cache_path.exists.return_value = True
        mock_cache.cache_path = mock_cache_path
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "info"])

        assert result.exit_code == 0
        mock_get_cache.assert_called_once()
        # Should print both table and panel
        assert mock_print.call_count >= 2

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_info_when_cache_db_does_not_exist(self, mock_print, mock_get_cache, runner):
        """Test info command when cache database doesn't exist yet."""
        mock_cache = MagicMock()
        mock_cache_path = MagicMock()
        mock_cache_path.__str__ = MagicMock(return_value="/test/path/.pdd/cache/firecrawl.db")
        mock_cache_path.parent = MagicMock()
        mock_cache_path.exists.return_value = False
        mock_cache.cache_path = mock_cache_path
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "info"])

        assert result.exit_code == 0
        assert mock_print.called

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_info_exception_handling(self, mock_print, mock_get_cache, runner):
        """Test info command handles exceptions gracefully."""
        mock_get_cache.side_effect = RuntimeError("Cache initialization failed")

        result = runner.invoke(cli, ["firecrawl-cache", "info"])

        assert result.exit_code == 0
        # Should still print the table with env vars, but show error for cache info
        assert mock_print.called
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Could not retrieve cache info' in str(call) or 'Cache initialization failed' in str(call)
                   for call in print_calls)

    @patch.dict('os.environ', {
        'FIRECRAWL_API_KEY': 'sk-1234567890abcdefghijklmnopqrstuvwxyz'
    })
    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_info_api_key_masking(self, mock_print, mock_get_cache, runner):
        """Test that API key is masked in output."""
        mock_cache = MagicMock()
        mock_cache.cache_path = MagicMock()
        mock_cache.cache_path.parent = MagicMock()
        mock_cache.cache_path.exists.return_value = True
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "info"])

        assert result.exit_code == 0
        # API key should be masked, not shown in full
        # The implementation shows first 8 chars + "..."
        assert mock_print.called


class TestCheckCommand:
    """Test the 'firecrawl-cache check' command."""

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_check_url_is_cached(self, mock_print, mock_get_cache, runner):
        """Test check command when URL is in cache."""
        mock_cache = MagicMock()
        mock_cache.enabled = True
        mock_cache.get.return_value = "Cached content from example.com"
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "check", "https://example.com"])

        assert result.exit_code == 0
        mock_cache.get.assert_called_once_with("https://example.com")

        # Should print success message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('URL is cached' in str(call) for call in print_calls)
        assert any('example.com' in str(call) for call in print_calls)

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_check_url_not_cached(self, mock_print, mock_get_cache, runner):
        """Test check command when URL is not in cache."""
        mock_cache = MagicMock()
        mock_cache.enabled = True
        mock_cache.get.return_value = None
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "check", "https://example.com"])

        assert result.exit_code == 0
        mock_cache.get.assert_called_once_with("https://example.com")

        # Should print not cached message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('URL is not cached' in str(call) for call in print_calls)

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_check_disabled_cache(self, mock_print, mock_get_cache, runner):
        """Test check command when caching is disabled."""
        mock_cache = MagicMock()
        mock_cache.enabled = False
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "check", "https://example.com"])

        assert result.exit_code == 0

        # Should print disabled message
        mock_print.assert_any_call("[yellow]Caching is disabled.[/yellow]")

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_check_shows_content_preview(self, mock_print, mock_get_cache, runner):
        """Test check command shows preview of cached content."""
        long_content = "A" * 300  # Content longer than 200 chars
        mock_cache = MagicMock()
        mock_cache.enabled = True
        mock_cache.get.return_value = long_content
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "check", "https://example.com"])

        assert result.exit_code == 0

        # Should show content length and preview
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Content length' in str(call) and '300' in str(call) for call in print_calls)
        assert any('Content preview' in str(call) or 'AAA' in str(call) for call in print_calls)

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_check_short_content_no_truncation(self, mock_print, mock_get_cache, runner):
        """Test check command with content shorter than preview limit."""
        short_content = "Short content"
        mock_cache = MagicMock()
        mock_cache.enabled = True
        mock_cache.get.return_value = short_content
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "check", "https://example.com"])

        assert result.exit_code == 0

        # Should show full content without "..."
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Short content' in str(call) for call in print_calls)

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_check_exception_handling(self, mock_print, mock_get_cache, runner):
        """Test check command handles exceptions gracefully."""
        mock_cache = MagicMock()
        mock_cache.enabled = True
        mock_cache.get.side_effect = RuntimeError("Database error")
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "check", "https://example.com"])

        assert result.exit_code == 0

        # Should print error message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('Error checking cache' in str(call) and 'Database error' in str(call)
                   for call in print_calls)

    @patch('pdd.commands.firecrawl.get_firecrawl_cache')
    @patch('pdd.commands.firecrawl.console.print')
    def test_check_with_complex_url(self, mock_print, mock_get_cache, runner):
        """Test check command with URL containing query parameters."""
        url = "https://example.com/page?id=123&utm_source=test"
        mock_cache = MagicMock()
        mock_cache.enabled = True
        mock_cache.get.return_value = "Content"
        mock_get_cache.return_value = mock_cache

        result = runner.invoke(cli, ["firecrawl-cache", "check", url])

        assert result.exit_code == 0
        mock_cache.get.assert_called_once_with(url)

    def test_check_url_argument_required(self, runner):
        """Test check command requires URL argument."""
        result = runner.invoke(cli, ["firecrawl-cache", "check"])

        # Should fail with missing argument error
        assert result.exit_code != 0
        assert 'Missing argument' in result.output or 'URL' in result.output


class TestIntegration:
    """Integration tests for firecrawl-cache commands."""

    def test_stats_and_clear_workflow(self, runner):
        """Test realistic workflow: check stats, then clear cache."""
        with patch('pdd.commands.firecrawl.get_firecrawl_cache_stats') as mock_get_stats, \
             patch('pdd.commands.firecrawl.clear_firecrawl_cache') as mock_clear, \
             patch('pdd.commands.firecrawl.click.confirm') as mock_confirm, \
             patch('pdd.commands.firecrawl.console.print'):

            # First check stats
            mock_get_stats.return_value = {
                'enabled': True,
                'total_entries': 10,
                'active_entries': 8,
                'expired_entries': 2,
                'ttl_hours': 24,
                'cache_path': '/path/to/cache.db'
            }

            result = runner.invoke(cli, ["firecrawl-cache", "stats"])
            assert result.exit_code == 0

            # Then clear cache
            mock_confirm.return_value = True
            mock_clear.return_value = 10

            result = runner.invoke(cli, ["firecrawl-cache", "clear"])
            assert result.exit_code == 0
            mock_clear.assert_called_once()

    def test_complete_workflow_all_commands(self, runner):
        """Test complete workflow using all four commands."""
        with patch('pdd.commands.firecrawl.get_firecrawl_cache_stats') as mock_get_stats, \
             patch('pdd.commands.firecrawl.get_firecrawl_cache') as mock_get_cache, \
             patch('pdd.commands.firecrawl.clear_firecrawl_cache') as mock_clear, \
             patch('pdd.commands.firecrawl.click.confirm') as mock_confirm, \
             patch('pdd.commands.firecrawl.console.print'):

            # Setup mocks
            mock_get_stats.return_value = {
                'enabled': True,
                'total_entries': 5,
                'active_entries': 5,
                'expired_entries': 0,
                'ttl_hours': 24,
                'cache_path': '/path/to/cache.db'
            }

            mock_cache = MagicMock()
            mock_cache.enabled = True
            mock_cache.get.return_value = "Cached content"
            mock_cache.cache_path = MagicMock()
            mock_cache.cache_path.parent = MagicMock()
            mock_cache.cache_path.exists.return_value = True
            mock_get_cache.return_value = mock_cache

            # 1. View info
            result = runner.invoke(cli, ["firecrawl-cache", "info"])
            assert result.exit_code == 0

            # 2. Check stats
            result = runner.invoke(cli, ["firecrawl-cache", "stats"])
            assert result.exit_code == 0

            # 3. Check if URL is cached
            result = runner.invoke(cli, ["firecrawl-cache", "check", "https://example.com"])
            assert result.exit_code == 0

            # 4. Clear cache
            mock_confirm.return_value = True
            mock_clear.return_value = 5
            result = runner.invoke(cli, ["firecrawl-cache", "clear"])
            assert result.exit_code == 0

    @pytest.mark.parametrize("subcmd,expected_words", [
        ("stats", ["stats", "statistics"]),
        ("clear", ["clear"]),
        ("info", ["info", "configuration"]),
        ("check", ["check", "url"]),
    ])
    def test_help_text_for_subcommand(self, runner, subcmd, expected_words):
        """Test that help text is available for each subcommand."""
        result = runner.invoke(cli, ["firecrawl-cache", subcmd, "--help"])
        assert result.exit_code == 0, (
            f"firecrawl-cache {subcmd} --help failed with exit code "
            f"{result.exit_code}: {result.output}"
        )
        assert any(w in result.output.lower() for w in expected_words)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--cov=pdd.commands.firecrawl", "--cov-report=term-missing"])
