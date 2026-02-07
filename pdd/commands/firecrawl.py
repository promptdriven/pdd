"""
Firecrawl cache management commands.

Provides debugging and management commands for the automatic Firecrawl cache.
Most users won't need these - caching is automatic and transparent.
"""
import os
import click
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.text import Text

from ..firecrawl_cache import get_firecrawl_cache_stats, clear_firecrawl_cache, get_firecrawl_cache

console = Console()


@click.group("firecrawl-cache")
def firecrawl_cache_group():
    """Manage Firecrawl web scraping cache (automatic - debugging only)."""
    pass


@firecrawl_cache_group.command()
def stats():
    """Show Firecrawl cache statistics."""
    try:
        stats = get_firecrawl_cache_stats()

        if 'error' in stats:
            console.print(f"[bold red]Error:[/bold red] {stats['error']}")
            return

        if not stats.get('enabled'):
            console.print("[yellow]Firecrawl caching is disabled.[/yellow]")
            console.print("Set FIRECRAWL_CACHE_ENABLE=true to enable.")
            return

        table = Table(title="Firecrawl Cache Statistics", show_header=True, header_style="bold magenta")
        table.add_column("Metric", style="cyan", no_wrap=True)
        table.add_column("Value", style="green")

        table.add_row("Status", "Enabled ✓")
        table.add_row("Total Entries", str(stats.get('total_entries', 0)))
        table.add_row("Active Entries", str(stats.get('active_entries', 0)))
        table.add_row("Expired Entries", str(stats.get('expired_entries', 0)))
        table.add_row("Total Size", f"{stats.get('total_size_mb', 0)} MB")
        table.add_row("Average Access Count", str(stats.get('average_access_count', 0)))
        table.add_row("Cache Efficiency", f"{stats.get('cache_efficiency', 0)}%")
        table.add_row("Default TTL", f"{stats.get('ttl_hours', 24)} hours")
        table.add_row("Max Entries", str(stats.get('max_entries', 1000)))
        table.add_row("Max Size", f"{stats.get('max_size_mb', 100)} MB")
        table.add_row("Auto Cleanup", "Yes" if stats.get('auto_cleanup', True) else "No")
        table.add_row("Location", stats.get('cache_path', 'N/A'))

        console.print(table)

        # Show cache efficiency indicator
        efficiency = stats.get('cache_efficiency', 0)
        if efficiency > 75:
            efficiency_style = "bold green"
            efficiency_msg = "Excellent"
        elif efficiency > 50:
            efficiency_style = "bold yellow"
            efficiency_msg = "Good"
        else:
            efficiency_style = "bold red"
            efficiency_msg = "Consider cleanup"

        efficiency_text = Text(f"\nCache Health: {efficiency_msg}", style=efficiency_style)
        console.print(efficiency_text)

    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")


@firecrawl_cache_group.command()
def clear():
    """Clear all cached Firecrawl entries."""
    try:
        stats = get_firecrawl_cache_stats()

        if not stats.get('enabled'):
            console.print("[yellow]Caching is disabled - nothing to clear.[/yellow]")
            return

        total = stats.get('total_entries', 0)
        if total == 0:
            console.print("[yellow]Cache is already empty.[/yellow]")
            return

        entry_word = "entry" if total == 1 else "entries"
        if not click.confirm(f"Clear {total} cached {entry_word}?"):
            console.print("Cancelled.")
            return

        cleared = clear_firecrawl_cache()
        cleared_word = "entry" if cleared == 1 else "entries"
        console.print(f"[bold green]✓[/bold green] Cleared {cleared} {cleared_word}")

    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")


@firecrawl_cache_group.command()
def info():
    """Show Firecrawl cache configuration and environment variables."""
    # Create configuration table
    table = Table(title="Firecrawl Cache Configuration", show_header=True, header_style="bold magenta")
    table.add_column("Setting", style="cyan", no_wrap=True)
    table.add_column("Value", style="green")
    table.add_column("Description", style="dim")

    # Environment variables
    env_vars = {
        'FIRECRAWL_CACHE_ENABLE': 'Enable/disable caching (default: true)',
        'FIRECRAWL_CACHE_TTL_HOURS': 'Default cache TTL in hours (default: 24)',
        'FIRECRAWL_CACHE_MAX_SIZE_MB': 'Maximum cache size in MB (default: 100)',
        'FIRECRAWL_CACHE_MAX_ENTRIES': 'Maximum number of cache entries (default: 1000)',
        'FIRECRAWL_CACHE_AUTO_CLEANUP': 'Enable automatic cleanup (default: true)',
        'FIRECRAWL_API_KEY': 'Firecrawl API key (required for scraping)'
    }

    for var, description in env_vars.items():
        value = os.environ.get(var, 'Not set')
        if var == 'FIRECRAWL_API_KEY' and value != 'Not set':
            value = f"{value[:8]}..." if len(value) > 8 else "Set"
        table.add_row(var, value, description)

    console.print(table)

    # Show cache directory info
    try:
        cache = get_firecrawl_cache()
        cache_path = cache.cache_path
        cache_dir = cache_path.parent

        info_panel = Panel(
            f"Cache Directory: {cache_dir}\n"
            f"Database File: {cache_path}\n"
            f"Database Exists: {'Yes' if cache_path.exists() else 'No'}",
            title="Cache Storage",
            border_style="blue"
        )
        console.print(info_panel)
    except Exception as e:
        console.print(f"[yellow]Could not retrieve cache info: {e}[/yellow]")


@firecrawl_cache_group.command()
@click.argument('url')
def check(url):
    """Check if a specific URL is cached."""
    try:
        cache = get_firecrawl_cache()

        if not cache.enabled:
            console.print("[yellow]Caching is disabled.[/yellow]")
            return

        cached_content = cache.get(url)

        if cached_content is not None:
            console.print(f"[bold green]URL is cached:[/bold green] {url}")
            console.print(f"Content length: {len(cached_content)} characters")

            # Show first 200 characters of content
            preview = cached_content[:200] + "..." if len(cached_content) > 200 else cached_content
            console.print(f"\nContent preview:\n{preview}")
        else:
            console.print(f"[yellow]URL is not cached:[/yellow] {url}")

    except Exception as e:
        console.print(f"[bold red]Error checking cache:[/bold red] {e}")


# Export the group with the original name for CLI registration
firecrawl_cache = firecrawl_cache_group
