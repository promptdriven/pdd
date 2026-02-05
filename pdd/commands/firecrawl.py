"""
Firecrawl cache management commands.

Provides basic debugging commands for the automatic Firecrawl cache.
Most users won't need these - caching is automatic and transparent.
"""
import click
from rich.console import Console
from rich.table import Table

from ..firecrawl_cache import get_firecrawl_cache_stats, clear_firecrawl_cache

console = Console()


@click.group("firecrawl-cache")
def firecrawl_cache():
    """Manage Firecrawl web scraping cache (automatic - debugging only)."""
    pass


@firecrawl_cache.command()
def stats():
    """Show Firecrawl cache statistics."""
    try:
        stats = get_firecrawl_cache_stats()

        if 'error' in stats:
            console.print(f"[bold red]Error:[/bold red] {stats['error']}")
            return

        if not stats.get('enabled'):
            console.print("[yellow]Firecrawl caching is disabled.[/yellow]")
            console.print("Set FIRECRAWL_CACHE_DISABLE=1 to enable.")
            return

        table = Table(title="Firecrawl Cache Statistics", show_header=True, header_style="bold magenta")
        table.add_column("Metric", style="cyan")
        table.add_column("Value", style="green")

        table.add_row("Status", "Enabled ✓")
        table.add_row("Total Entries", str(stats.get('total_entries', 0)))
        table.add_row("Active Entries", str(stats.get('active_entries', 0)))
        table.add_row("Expired Entries", str(stats.get('expired_entries', 0)))
        table.add_row("TTL (hours)", str(stats.get('ttl_hours', 24)))
        table.add_row("Location", stats.get('cache_path', 'N/A'))

        console.print(table)

    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")


@firecrawl_cache.command()
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

        if not click.confirm(f"Clear {total} cached entries?"):
            console.print("Cancelled.")
            return

        cleared = clear_firecrawl_cache()
        console.print(f"[bold green]✓[/bold green] Cleared {cleared} entries")

    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")
