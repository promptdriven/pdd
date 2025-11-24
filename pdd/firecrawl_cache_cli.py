#!/usr/bin/env python3
"""
CLI commands for managing Firecrawl cache.

This module provides command-line interface for managing the Firecrawl cache,
including viewing statistics, clearing cache, and configuring cache settings.

Usage:
    pdd firecrawl-cache stats    # Show cache statistics
    pdd firecrawl-cache clear    # Clear all cached entries
    pdd firecrawl-cache info     # Show cache configuration
"""

import click
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.text import Text
from .firecrawl_cache import get_firecrawl_cache, clear_firecrawl_cache, get_firecrawl_cache_stats

console = Console()

@click.group()
def firecrawl_cache():
    """Manage Firecrawl web scraping cache."""
    pass

@firecrawl_cache.command()
def stats():
    """Show Firecrawl cache statistics."""
    try:
        stats = get_firecrawl_cache_stats()
        
        if 'error' in stats:
            console.print(f"[bold red]Error getting cache stats:[/bold red] {stats['error']}")
            return
        
        # Create statistics table
        table = Table(title="Firecrawl Cache Statistics", show_header=True, header_style="bold magenta")
        table.add_column("Metric", style="cyan", no_wrap=True)
        table.add_column("Value", style="green")
        
        table.add_row("Total Entries", str(stats.get('total_entries', 0)))
        table.add_row("Active Entries", str(stats.get('active_entries', 0)))
        table.add_row("Expired Entries", str(stats.get('expired_entries', 0)))
        table.add_row("Total Size", f"{stats.get('total_size_mb', 0)} MB")
        table.add_row("Average Access Count", str(stats.get('average_access_count', 0)))
        table.add_row("Cache Enabled", "Yes" if stats.get('cache_enabled', False) else "No")
        table.add_row("Default TTL", f"{stats.get('default_ttl_hours', 0)} hours")
        table.add_row("Max Entries", str(stats.get('max_entries', 0)))
        table.add_row("Max Size", f"{stats.get('max_size_mb', 0)} MB")
        
        console.print(table)
        
        # Show cache efficiency
        total_entries = stats.get('total_entries', 0)
        active_entries = stats.get('active_entries', 0)
        
        if total_entries > 0:
            efficiency = (active_entries / total_entries) * 100
            efficiency_text = Text(f"Cache Efficiency: {efficiency:.1f}%", style="bold green" if efficiency > 50 else "bold yellow")
            console.print(efficiency_text)
        
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")

@firecrawl_cache.command()
def clear():
    """Clear all cached Firecrawl entries."""
    try:
        cache = get_firecrawl_cache()
        stats_before = cache.get_stats()
        
        if stats_before.get('total_entries', 0) == 0:
            console.print("[yellow]Cache is already empty.[/yellow]")
            return
        
        # Confirm before clearing
        if not click.confirm(f"Clear {stats_before.get('total_entries', 0)} cached entries?"):
            console.print("Cache clear cancelled.")
            return
        
        cache.clear()
        console.print("[bold green]Cache cleared successfully![/bold green]")
        
    except Exception as e:
        console.print(f"[bold red]Error clearing cache:[/bold red] {e}")

@firecrawl_cache.command()
def info():
    """Show Firecrawl cache configuration and environment variables."""
    import os
    
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
    cache = get_firecrawl_cache()
    cache_dir = cache.cache_dir
    db_path = cache.db_path
    
    info_panel = Panel(
        f"Cache Directory: {cache_dir}\n"
        f"Database File: {db_path}\n"
        f"Database Exists: {'Yes' if db_path.exists() else 'No'}",
        title="Cache Storage",
        border_style="blue"
    )
    console.print(info_panel)

@firecrawl_cache.command()
@click.argument('url')
def check(url):
    """
    #Check if a specific URL is cached.
    if not url:
        console.print("[bold red]Error:[/bold red] URL is required. Use --url option.")
        return
    """
    try:
        cache = get_firecrawl_cache()
        cached_content = cache.get(url)
        
        if cached_content is not None:
            console.print(f"[bold green]URL is cached:[/bold green] {url}")
            console.print(f"Content length: {len(cached_content)} characters")
            
            # Show first 200 characters of content
            preview = cached_content[:200] + "..." if len(cached_content) > 200 else cached_content
            console.print(f"Content preview:\n{preview}")
        else:
            console.print(f"[yellow]URL is not cached:[/yellow] {url}")
            
    except Exception as e:
        console.print(f"[bold red]Error checking cache:[/bold red] {e}")

if __name__ == '__main__':
    firecrawl_cache()
