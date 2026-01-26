from __future__ import annotations

import os
import re
import stat
import logging
from datetime import datetime
from pathlib import Path
from typing import Set, Optional, Dict, List, Tuple, Deque
from collections import deque, defaultdict

from rich.console import Console

from pdd.construct_paths import _is_known_language

# Initialize rich console
console = Console()

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")
logger = logging.getLogger(__name__)

def extract_includes_from_file(file_path: Path) -> Set[str]:
    """
    Parses <include> tags from a prompt file.

    Args:
        file_path: Path to the prompt file.

    Returns:
        Set of included paths found in the file. Returns empty set if file
        cannot be read.
    """
    if not file_path.exists() or not file_path.is_file():
        logger.warning(f"File not found or not a file: {file_path}")
        return set()

    try:
        content = file_path.read_text(encoding="utf-8")
        # Regex pattern matching <include>...</include> tags
        pattern = r'<include>(.*?)</include>'
        matches = re.findall(pattern, content, re.DOTALL)
        
        # Clean up matches (strip whitespace)
        includes = {m.strip() for m in matches if m.strip()}
        return includes
    except Exception as e:
        logger.error(f"Error reading file {file_path}: {e}")
        return set()


def extract_module_from_include(include_path: str) -> Optional[str]:
    """
    Maps include paths to module names by stripping suffixes.

    Args:
        include_path: The path string found inside an include tag.

    Returns:
        The extracted module name, or None if it's not a module include.
    """
    path_obj = Path(include_path)
    filename = path_obj.name
    stem = path_obj.stem

    # Logic:
    # 1. If it's a context example file (e.g., context/llm_invoke_example.py)
    # 2. If it's a prompt file with language suffix (e.g., prompts/cli_python.prompt)

    # Check if it looks like a module file:
    # - Example files contain "_example" in the stem
    # - Prompt files must have a KNOWN language suffix (e.g., _python, _java, _go, _rust)
    # - LLM prompts (_LLM) are runtime prompts, NOT code generation prompts
    # - Exclude 'prompt' suffix as it's not a programming language
    is_example = "_example" in stem
    suffix_match = re.search(r'_([a-zA-Z0-9]+)$', stem)
    suffix_value = suffix_match.group(1).lower() if suffix_match else None

    # Exclude special suffixes that are in the CSV but aren't programming languages
    excluded_suffixes = {'llm', 'prompt'}
    if suffix_value in excluded_suffixes:
        # LLM and prompt suffixes are NOT code generation prompts
        is_lang_suffix = False
    else:
        # Check if it's a known programming language from data/language_format.csv
        is_lang_suffix = _is_known_language(suffix_value) if suffix_value else False

    is_module_prompt = filename.endswith(".prompt") and is_lang_suffix

    if not (is_example or is_module_prompt):
        return None

    # Remove suffixes
    # Order matters: remove language specific suffixes first, then _example
    clean_name = stem

    # Only remove suffix if it's a known language suffix
    if is_lang_suffix:
        clean_name = re.sub(r'_[a-zA-Z0-9]+$', '', clean_name)

    # Remove example suffix
    clean_name = re.sub(r'_example$', '', clean_name, flags=re.IGNORECASE)

    if not clean_name:
        return None

    return clean_name


def build_dependency_graph(prompts_dir: Path) -> Dict[str, List[str]]:
    """
    Scans prompt files and builds a dependency graph based on includes.

    Args:
        prompts_dir: Directory containing .prompt files.

    Returns:
        Dictionary mapping module_name -> list of dependencies (modules it depends on).
    """
    if not prompts_dir.exists() or not prompts_dir.is_dir():
        logger.error(f"Prompts directory not found: {prompts_dir}")
        return {}

    dependency_graph: Dict[str, Set[str]] = defaultdict(set)
    
    # Scan all prompt files with language suffix, excluding LLM runtime prompts
    all_prompts = list(prompts_dir.rglob("*_*.prompt"))
    prompt_files = [f for f in all_prompts if not f.stem.lower().endswith('_llm')]

    for p_file in prompt_files:
        # Determine current module name from filename
        # e.g., "foo_python.prompt" -> "foo"
        current_module = extract_module_from_include(p_file.name)
        
        if not current_module:
            continue

        # Ensure module exists in graph even if it has no dependencies
        if current_module not in dependency_graph:
            dependency_graph[current_module] = set()

        # Parse includes
        includes = extract_includes_from_file(p_file)
        
        for inc in includes:
            dep_module = extract_module_from_include(inc)
            
            # Add dependency if valid and not self-reference
            if dep_module and dep_module != current_module:
                dependency_graph[current_module].add(dep_module)

    # Convert sets to lists for return type consistency
    return {k: list(v) for k, v in dependency_graph.items()}


def topological_sort(graph: Dict[str, List[str]]) -> Tuple[List[str], List[List[str]]]:
    """
    Performs topological sort using Kahn's algorithm.

    Args:
        graph: Adjacency list (module -> dependencies).

    Returns:
        Tuple containing:
        1. List of modules in topological order (dependencies first).
        2. List of cycles detected (if any).
    """
    # Calculate in-degrees (number of modules depending on key)
    # Note: The input graph is "Module -> Depends On".
    # For Kahn's algo to output [Dependency, ..., Dependent], we need to process
    # nodes with 0 dependencies first.
    
    # Normalize graph to ensure all nodes are keys
    all_nodes = set(graph.keys())
    for deps in graph.values():
        all_nodes.update(deps)
    
    adj_list = {node: graph.get(node, []) for node in all_nodes}
    
    # In Kahn's, usually we track edges: Dependency -> Dependent.
    # Our input is Dependent -> [Dependencies].
    # So, in-degree here represents "number of unsatisfied dependencies".
    in_degree = {node: 0 for node in all_nodes}
    
    # Reverse graph: Dependency -> [Dependents] (needed to update neighbors)
    reverse_graph: Dict[str, List[str]] = defaultdict(list)
    
    for node, deps in adj_list.items():
        in_degree[node] = len(deps)
        for dep in deps:
            reverse_graph[dep].append(node)

    # Queue for nodes with 0 dependencies
    queue: Deque[str] = deque([node for node, deg in in_degree.items() if deg == 0])
    
    sorted_list: List[str] = []
    processed_count = 0
    
    while queue:
        u = queue.popleft()
        sorted_list.append(u)
        processed_count += 1
        
        # For every module 'v' that depends on 'u'
        for v in reverse_graph[u]:
            in_degree[v] -= 1
            if in_degree[v] == 0:
                queue.append(v)

    cycles: List[List[str]] = []

    if processed_count != len(all_nodes):
        remaining = {n for n, deg in in_degree.items() if deg > 0}

        # Find actual cycle participants: nodes that can reach themselves
        # through remaining-only edges (DFS reachability check)
        actual_cyclic: Set[str] = set()
        for node in remaining:
            visited: Set[str] = set()
            stack = [dep for dep in adj_list.get(node, []) if dep in remaining]
            found_cycle = False
            while stack and not found_cycle:
                current = stack.pop()
                if current == node:
                    found_cycle = True
                    break
                if current in visited:
                    continue
                visited.add(current)
                stack.extend(dep for dep in adj_list.get(current, []) if dep in remaining)
            if found_cycle:
                actual_cyclic.add(node)

        if actual_cyclic:
            cycles.append(sorted(actual_cyclic))
            logger.warning(f"Cyclic dependencies detected involving: {sorted(actual_cyclic)}")

        # Append non-cyclic remaining nodes to sorted_list in best-effort order
        # (these depend on cyclic nodes but aren't cyclic themselves)
        non_cyclic_remaining = remaining - actual_cyclic
        if non_cyclic_remaining:
            ordered = sorted(non_cyclic_remaining, key=lambda n: (in_degree[n], n))
            sorted_list.extend(ordered)

    return sorted_list, cycles


def get_affected_modules(sorted_modules: List[str], modified: Set[str], graph: Dict[str, List[str]], cyclic_modules: Optional[Set[str]] = None) -> List[str]:
    """
    Identifies modules that need syncing based on modified modules and dependencies.

    Args:
        sorted_modules: Full list of modules in topological order.
        modified: Set of module names that have changed.
        graph: Dependency graph (module -> dependencies).
        cyclic_modules: Optional set of modules that are part of dependency cycles.
            These are excluded from sorted_modules by topological sort but should
            still be included if they're affected.

    Returns:
        List of modules to sync, preserving topological order for non-cyclic modules,
        with cyclic modules appended at the end in alphabetical order.
    """
    if not modified:
        return []

    # Build reverse graph: Dependency -> [Dependents]
    # This allows us to traverse "up" the chain from a modified dependency to things that use it
    reverse_graph: Dict[str, Set[str]] = defaultdict(set)
    for node, deps in graph.items():
        for dep in deps:
            reverse_graph[dep].add(node)

    affected = set()
    queue = deque(modified)
    
    # BFS to find all transitive dependents
    while queue:
        current = queue.popleft()
        if current in affected:
            continue
            
        affected.add(current)
        
        # Add all modules that depend on current
        for dependent in reverse_graph.get(current, []):
            if dependent not in affected:
                queue.append(dependent)

    # Filter sorted_modules to keep only affected ones, preserving order
    result = [m for m in sorted_modules if m in affected]

    # Include affected modules that are in cycles (append at end, sorted for determinism)
    if cyclic_modules:
        cyclic_affected = sorted([m for m in cyclic_modules if m in affected and m not in result])
        result.extend(cyclic_affected)

    return result


def generate_sync_order_script(modules: List[str], output_path: Path, worktree_path: Optional[Path] = None) -> str:
    """
    Generates a shell script to execute pdd sync commands in order.

    Args:
        modules: Ordered list of module names to sync.
        output_path: Path where the script should be written.
        worktree_path: Optional path to cd into before running commands.

    Returns:
        The content of the generated script.
    """
    if not modules:
        logger.info("No modules to sync. Skipping script generation.")
        return ""

    lines = [
        "#!/bin/bash",
        "#",
        "# PDD Sync Order Script",
        f"# Generated: {datetime.now().isoformat()}",
        f"# Total Modules: {len(modules)}",
        "#",
        "",
        "set -e  # Exit immediately if a command exits with a non-zero status",
        ""
    ]

    if worktree_path:
        lines.append("# Run this script from your repository root directory")
        lines.append("")

    total = len(modules)
    for i, module in enumerate(modules, 1):
        lines.append(f'echo "[{i}/{total}] Syncing {module}..."')
        lines.append(f"pdd sync {module}")
        lines.append("")

    script_content = "\n".join(lines)

    try:
        output_path.write_text(script_content, encoding="utf-8")
        
        # Make executable (chmod +x)
        st = os.stat(output_path)
        os.chmod(output_path, st.st_mode | stat.S_IEXEC)
        
        console.print(f"[green]Successfully generated sync script at: {output_path}[/green]")
    except Exception as e:
        console.print(f"[red]Failed to write sync script: {e}[/red]")
        raise

    return script_content