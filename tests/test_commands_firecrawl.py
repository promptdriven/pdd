#!/usr/bin/env python3
"""
Test suite for pdd/commands/firecrawl.py

Tests the CLI commands for Firecrawl cache management:
- firecrawl-cache stats: Display cache statistics
- firecrawl-cache clear: Clear cached entries

Coverage areas:
- Command group structure
- Stats command with various scenarios (enabled, disabled, error states)
- Clear command with confirmation handling
- Error handling and user feedback
- Rich console output formatting
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
        """Test that firecrawl-cache shows help text."""
        result = runner.invoke(cli, ["firecrawl-cache", "--help"])
        assert result.exit_code == 0
        assert "stats" in result.output.lower()
        assert "clear" in result.output.lower()


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
        mock_print.assert_any_call("Set FIRECRAWL_CACHE_DISABLE=1 to enable.")

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
        mock_confirm.assert_called_once_with("Clear 1 cached entries?")  # Note: grammar issue in original
        mock_clear.assert_called_once()

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

        # Should show correct count in success message
        print_calls = [str(call) for call in mock_print.call_args_list]
        assert any('1000' in str(call) for call in print_calls)

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

    def test_help_text_for_both_commands(self, runner):
        """Test that help text is available for both subcommands."""
        # Test stats help
        result = runner.invoke(cli, ["firecrawl-cache", "stats", "--help"])
        assert result.exit_code == 0
        assert "stats" in result.output.lower() or "statistics" in result.output.lower()

        # Test clear help
        result = runner.invoke(cli, ["firecrawl-cache", "clear", "--help"])
        assert result.exit_code == 0
        assert "clear" in result.output.lower()


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--cov=pdd.commands.firecrawl", "--cov-report=term-missing"])
