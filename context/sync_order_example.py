"""
Example usage of the pdd.sync_order module.

This script demonstrates how to:
1. Create a temporary directory with mock prompt files.
2. Build a dependency graph from those prompts.
3. Perform a topological sort to determine the correct sync order.
4. Identify affected modules given a set of changes.
5. Generate a shell script to execute the sync commands.
"""

import os
import shutil
from pathlib import Path
from rich.console import Console

# Import the module functions
# Note: In a real package, this would be: from pdd.sync_order import ...
try:
    from pdd.sync_order import (
        build_dependency_graph,
        topological_sort,
        get_affected_modules,
        generate_sync_order_script
    )
except ImportError:
    # Fallback or mock for demonstration if the package is not installed
    def build_dependency_graph(p): return {}
    def topological_sort(g): return [], []
    def get_affected_modules(s, m, g): return []
    def generate_sync_order_script(s, p): pass

console = Console()

def create_mock_prompts(base_dir: Path) -> Path:
    """Creates a set of dummy prompt files with dependencies."""
    prompts_dir = base_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # 1. base_utils (No dependencies)
    (prompts_dir / "base_utils_python.prompt").write_text(
        "This is the base utility module.", encoding="utf-8"
    )

    # 2. logger (Depends on base_utils)
    (prompts_dir / "logger_python.prompt").write_text(
        """
        This module handles logging.
        <include>prompts/base_utils_python.prompt</include>
        """, encoding="utf-8"
    )

    # 3. database (Depends on logger)
    (prompts_dir / "database_python.prompt").write_text(
        """
        This module handles DB connections.
        <include>prompts/logger_python.prompt</include>
        """, encoding="utf-8"
    )

    # 4. api (Depends on database and logger)
    (prompts_dir / "api_python.prompt").write_text(
        """
        This is the API layer.
        <include>prompts/database_python.prompt</include>
        <include>prompts/logger_python.prompt</include>
        """, encoding="utf-8"
    )

    return prompts_dir

def main() -> None:
    # Setup temporary directory
    temp_dir = Path("temp_pdd_example")
    if temp_dir.exists():
        shutil.rmtree(temp_dir)
    
    try:
        console.print("[bold blue]1. Creating mock prompt files...[/bold blue]")
        prompts_dir = create_mock_prompts(temp_dir)
        console.print(f"Created prompts in: {prompts_dir}")

        # ---------------------------------------------------------
        # Step 2: Build Dependency Graph
        # ---------------------------------------------------------
        console.print("\n[bold blue]2. Building dependency graph...[/bold blue]")
        graph = build_dependency_graph(prompts_dir)
        
        console.print("Dependency Graph (Module -> Depends On):")
        for module, deps in graph.items():
            console.print(f"  - [cyan]{module}[/cyan] depends on: {deps}")

        # ---------------------------------------------------------
        # Step 3: Topological Sort
        # ---------------------------------------------------------
        console.print("\n[bold blue]3. Calculating topological sort order...[/bold blue]")
        sorted_modules, cycles = topological_sort(graph)

        if cycles:
            console.print(f"[red]Cycles detected: {cycles}[/red]")
        else:
            console.print(f"Sync Order: [green]{' -> '.join(sorted_modules)}[/green]")

        # ---------------------------------------------------------
        # Step 4: Determine Affected Modules
        # ---------------------------------------------------------
        # Scenario: We modified 'base_utils'. Everything depends on it transitively.
        modified_modules = {"base_utils"}
        console.print(f"\n[bold blue]4. Calculating impact of modifying: {modified_modules}[/bold blue]")
        
        affected = get_affected_modules(sorted_modules, modified_modules, graph)
        console.print(f"Affected modules (in sync order): [yellow]{affected}[/yellow]")
        
        # ---------------------------------------------------------
        # Step 5: Generate Sync Script
        # ---------------------------------------------------------
        console.print("\n[bold blue]5. Generating sync script...[/bold blue]")
        script_path = temp_dir / "sync_all.sh"
        
        # Generate script for ALL modules
        generate_sync_order_script(sorted_modules, script_path)
        
        console.print(f"Script written to: {script_path}")
        if script_path.exists():
            console.print("[dim]Script content preview:[/dim]")
            console.print(script_path.read_text())

    finally:
        # Cleanup
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
            console.print("\n[dim]Cleaned up temporary files.[/dim]")

if __name__ == "__main__":
    main()