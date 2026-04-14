"""
This module provides the `auto_include` function to automatically find and
generate proper dependencies with selective extraction attributes.
"""
import os
import re
from io import StringIO
from pathlib import Path
from typing import Callable, List, Optional, Set, Tuple

import pandas as pd
from pydantic import BaseModel, Field
from rich.console import Console
from rich.panel import Panel

from . import DEFAULT_TIME, DEFAULT_STRENGTH
from .embed_retrieve import embed_and_retrieve
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .summarize_directory import summarize_directory

console = Console()


# ---------------------------------------------------------------------------
# Pydantic models for structured LLM output
# ---------------------------------------------------------------------------

class NewInclude(BaseModel):
    """A new include to add to the prompt."""
    file: str
    module: str
    select: Optional[str] = None
    query: Optional[str] = None


class IncludeAnnotation(BaseModel):
    """An annotation for an existing include already in the prompt."""
    file: str
    select: Optional[str] = None
    query: Optional[str] = None


class AutoIncludeResult(BaseModel):
    """Structured output from the auto_include_LLM prompt."""
    reasoning: str = Field(description="Chain-of-thought reasoning (discarded after parsing)")
    new_includes: List[NewInclude] = Field(default_factory=list)
    existing_include_annotations: List[IncludeAnnotation] = Field(default_factory=list)


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _validate_input(strength: float, temperature: float) -> None:
    """Validate strength and temperature are between 0 and 1."""
    if not 0 <= strength <= 1:
        raise ValueError("Strength must be between 0 and 1")
    if not 0 <= temperature <= 1:
        raise ValueError("Temperature must be between 0 and 1")


def _format_csv_rows_for_llm(csv_output: str, directory_path: str = "") -> str:
    """Format CSV rows as structured metadata for the LLM.

    Each row becomes:
        File: {full_path}
        Purpose: {file_summary}
        Key Exports: {key_exports}
        Dependencies: {dependencies}

    ``directory_path`` is accepted for API compatibility but is no longer
    used.  CSV paths are stored relative to the project root since the
    Bug #2 fix, so no qualification is needed.
    """
    if not csv_output:
        return ""
    try:
        dataframe = pd.read_csv(StringIO(csv_output))
        entries = []
        for _, row in dataframe.iterrows():
            full_path = row.get('full_path', '')
            # CSV paths are repo-root-relative, no qualification needed.
            file_summary = row.get('file_summary', '')
            key_exports = row.get('key_exports', '[]')
            dependencies = row.get('dependencies', '[]')
            entry = (
                f"File: {full_path}\n"
                f"Purpose: {file_summary}\n"
                f"Key Exports: {key_exports}\n"
                f"Dependencies: {dependencies}"
            )
            entries.append(entry)
        return "\n".join(entries)
    except Exception as ex:
        console.print(f"[red]Error parsing CSV: {ex}[/red]")
        return ""


def _embed_and_rank(input_prompt: str, candidates: List[str], top_n: int = 50) -> List[str]:
    """Pre-filter candidates by cosine similarity using embed_and_retrieve.

    When the number of candidates exceeds a threshold, this function uses
    embedding-based retrieval to select the top-N most relevant candidates
    before passing them to the LLM.

    Falls back to returning all candidates if the embedding call fails.
    """
    try:
        ranked = embed_and_retrieve(query=input_prompt, candidates=candidates, top_n=top_n)
        # Extract just the candidate texts (drop scores)
        return [text for text, _score in ranked]
    except Exception as ex:
        console.print(f"[yellow]Warning: embed_and_rank fallback – {ex}[/yellow]")
        return candidates


def _directory_prefix(directory_path: str) -> str:
    """Extract the directory portion from a directory_path that may be a glob.

    E.g. ``'context/*.py'`` → ``'context'``,  ``'test_auto_deps/'`` → ``'test_auto_deps'``.
    Returns ``''`` if no meaningful directory prefix can be determined.
    """
    if not directory_path:
        return ""
    # Strip glob wildcards
    prefix = directory_path.split('*')[0].rstrip('/')
    if not prefix:
        return ""
    if os.path.isdir(prefix):
        return prefix
    parent = os.path.dirname(prefix)
    return parent if parent else prefix


def _enforce_select_query_exclusivity(result: AutoIncludeResult) -> None:
    """Drop redundant ``query=`` attributes when ``select=`` is also set.

    For file types that support structural selectors (.py, .md, .json,
    .yaml, .yml), ``select=`` is deterministic and should win over
    ``query=``. The LLM occasionally produces both; this normalizes the
    result in-place.
    """
    if not isinstance(result, AutoIncludeResult):
        return

    _STRUCTURAL_EXTENSIONS = {'.py', '.md', '.json', '.yaml', '.yml'}

    for inc in result.new_includes:
        if inc.select and inc.query:
            ext = os.path.splitext(inc.file)[1].lower()
            if ext in _STRUCTURAL_EXTENSIONS:
                inc.query = None
    for ann in result.existing_include_annotations:
        if ann.select and ann.query:
            ext = os.path.splitext(ann.file)[1].lower()
            if ext in _STRUCTURAL_EXTENSIONS:
                ann.query = None


def _build_new_block(inc: NewInclude) -> str:
    """Build a <new> block from a NewInclude."""
    attrs = ""
    if inc.select:
        attrs += f' select="{inc.select}"'
    if inc.query:
        attrs += f' query="{inc.query}"'
    inner = f"<include{attrs}>{inc.file}</include>"
    return f"<new>\n<{inc.module}>{inner}</{inc.module}>\n</new>"


def _build_update_block(ann: IncludeAnnotation) -> str:
    """Build an <update> block from an IncludeAnnotation.

    Skip entries with neither select nor query.
    """
    if not ann.select and not ann.query:
        return ""
    attrs = ""
    if ann.select:
        attrs += f' select="{ann.select}"'
    if ann.query:
        attrs += f' query="{ann.query}"'
    return f"<update>\n<include{attrs}>{ann.file}</include>\n</update>"


def _build_include_directives(result: AutoIncludeResult) -> str:
    """Build the include_directives string from the structured LLM result."""
    blocks = []
    for inc in result.new_includes:
        blocks.append(_build_new_block(inc))
    for ann in result.existing_include_annotations:
        block = _build_update_block(ann)
        if block:
            blocks.append(block)
    return "\n".join(blocks)


def _extract_module_name(prompt_filename: Optional[str]) -> Optional[str]:
    """Extract module name from prompt filename.

    E.g. 'prompts/agentic_fix_python.prompt' -> 'agentic_fix'
    """
    if not prompt_filename:
        return None
    match = re.search(r'([^/]+)_[^_]+\.prompt$', prompt_filename)
    if match:
        return match.group(1)
    return None


def _filter_duplicates(directives: str, input_prompt: str) -> str:
    """Remove <new> blocks whose file path already appears in input_prompt.

    Compares both full paths and basenames to catch duplicates even when
    the directive uses a qualified path (e.g. ``dir/file.py``) and the
    prompt already contains the bare filename (``file.py``), or vice-versa.
    """
    existing_paths = set(re.findall(r'<include[^>]*>([^<]+)</include>', input_prompt))
    if not existing_paths:
        return directives

    existing_basenames = {os.path.basename(p.strip()) for p in existing_paths}

    def should_keep(block: str) -> bool:
        m = re.search(r'<include[^>]*>([^<]+)</include>', block)
        if not m:
            return True
        new_path = m.group(1).strip()
        if new_path in existing_paths:
            return False
        if os.path.basename(new_path) in existing_basenames:
            return False
        return True

    new_blocks = re.findall(r'<new>\n.*?\n</new>', directives, re.DOTALL)
    result = directives
    for block in new_blocks:
        if not should_keep(block):
            result = result.replace(block, "")
    return result.strip()


def _filter_self_references(directives: str, module_name: Optional[str]) -> str:
    """Remove <new> blocks that reference the module's own example file."""
    if not module_name:
        return directives
    pattern = rf'<new>\n.*?{re.escape(module_name)}_example\.py.*?\n</new>'
    return re.sub(pattern, '', directives, flags=re.DOTALL).strip()


def _extract_example_modules(content: str) -> Set[str]:
    """Extract module names from _example.py includes in content."""
    pattern = r'<include[^>]*>([^<]+)</include>'
    matches = re.findall(pattern, content)
    modules = set()
    for match in matches:
        path = match.strip()
        example_match = re.search(r'context/(?:[^/]+/)*([^/]+)_example\.py$', path)
        if example_match:
            modules.add(example_match.group(1))
    return modules


def _detect_circular_dependencies(
    current_prompt: str,
    new_directives: str,
    prompts_dir: Optional[str] = None,
) -> List[List[str]]:
    """Detect circular dependencies through example file includes.

    A circular dependency occurs when module A is about to include module B's
    example, and module B's prompt already includes module A's example.
    """
    current_module = _extract_module_name(current_prompt)
    if not current_module:
        return []

    new_dep_modules = _extract_example_modules(new_directives)
    if not new_dep_modules:
        return []

    if prompts_dir:
        base_dir = Path(prompts_dir)
    else:
        current_path = Path(current_prompt)
        if current_path.parent.name == 'prompts' or 'prompts' in str(current_path):
            base_dir = current_path.parent
        else:
            base_dir = Path('prompts')

    current_prompt_name = Path(current_prompt).name
    cycles: List[List[str]] = []

    for dep_module in new_dep_modules:
        prompt_patterns = [
            f"{dep_module}_python.prompt",
            f"{dep_module}_LLM.prompt",
            f"{dep_module}.prompt",
        ]
        for pat in prompt_patterns:
            prompt_path = base_dir / pat
            if prompt_path.exists():
                try:
                    content = prompt_path.read_text(encoding='utf-8')
                    dep_modules = _extract_example_modules(content)
                    if current_module in dep_modules:
                        cycles.append([current_prompt_name, pat, current_prompt_name])
                except Exception:
                    pass
                break

    return cycles


def _filter_circular_dependencies(directives: str, cycles: List[List[str]]) -> str:
    """Remove <new> blocks that would create circular dependencies."""
    if not cycles:
        return directives

    problematic_modules: Set[str] = set()
    for cycle in cycles:
        for prompt_name in cycle:
            module_name = _extract_module_name(prompt_name)
            if module_name:
                problematic_modules.add(module_name)

    result = directives
    for module in problematic_modules:
        pattern = rf'<new>\n.*?{re.escape(module)}_example\.py.*?\n</new>'
        result = re.sub(pattern, '', result, flags=re.DOTALL)
    return result.strip()


def _get_file_line_count(file_path: str) -> int:
    """Return the number of lines in a file, or 0 if unreadable."""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            return sum(1 for _ in f)
    except Exception:
        return 0


def _strip_selectors_from_small_files(directives: str, threshold: int = 100, directory_path: str = "") -> str:
    """Strip selectors from files under `threshold` lines.

    For <new> blocks: remove select/query attributes but keep the include.
    For <update> blocks: remove the entire block.

    Resolves relative paths against the project root so that
    repo-root-relative CSV paths are found regardless of CWD.
    """
    from .path_resolution import find_project_root_from_path
    _found = find_project_root_from_path(directory_path or ".")
    _project_root = _found if _found else os.path.abspath(directory_path or ".")

    def _resolve_and_count(file_path: str) -> int:
        """Try the path as-is, then relative to project root."""
        count = _get_file_line_count(file_path)
        if count > 0:
            return count
        resolved = os.path.join(_project_root, file_path)
        count = _get_file_line_count(resolved)
        return count

    def process_new_block(match: str) -> str:
        file_match = re.search(r'<include[^>]*>([^<]+)</include>', match)
        if not file_match:
            return match
        file_path = file_match.group(1).strip()
        if _resolve_and_count(file_path) < threshold:
            # Remove select/query attributes but keep the include
            return re.sub(r'<include\s+[^>]+>', '<include>', match)
        return match

    # Process <new> blocks
    def replace_new(m: re.Match) -> str:
        return process_new_block(m.group(0))

    result = re.sub(r'<new>\n.*?\n</new>', replace_new, directives, flags=re.DOTALL)

    # Process <update> blocks — remove entirely if file is small
    def replace_update(m: re.Match) -> str:
        block = m.group(0)
        file_match = re.search(r'<include[^>]*>([^<]+)</include>', block)
        if not file_match:
            return block
        file_path = file_match.group(1).strip()
        if _resolve_and_count(file_path) < threshold:
            return ""
        return block

    result = re.sub(r'<update>\n.*?\n</update>', replace_update, result, flags=re.DOTALL)
    return result.strip()


# ---------------------------------------------------------------------------
# Main function
# ---------------------------------------------------------------------------

def auto_include(
    input_prompt: str,
    directory_path: str,
    csv_file: Optional[str] = None,
    prompt_filename: Optional[str] = None,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    verbose: bool = False,
    progress_callback: Optional[Callable[[int, int], None]] = None,
    include_docs: bool = False,
    max_workers: int = 1,
    csv_path: Optional[str] = None,
) -> Tuple[str, str, float, str]:
    """
    Automatically find and generate proper dependencies with selective
    extraction attributes.

    Returns:
        (include_directives, csv_output, total_cost, model_name)
    """
    # Req 7: validate inputs
    _validate_input(strength, temperature)

    # Req 1: load prompt template
    auto_include_prompt = load_prompt_template("auto_include_LLM")
    if not auto_include_prompt:
        raise ValueError("Failed to load prompt template 'auto_include_LLM'")

    llm_kwargs = {
        "strength": strength,
        "temperature": temperature,
        "time": time,
        "verbose": verbose,
    }

    # Req 2: run summarize_directory
    if verbose:
        console.print(Panel("Step 1: Running summarize_directory", style="blue"))

    csv_output, summary_cost, summary_model = summarize_directory(
        directory_path=directory_path,
        csv_file=csv_file,
        progress_callback=progress_callback,
        csv_path=csv_path,
        include_docs=include_docs,
        max_workers=max_workers,
        **llm_kwargs,
    )

    available_includes = _format_csv_rows_for_llm(csv_output, directory_path=directory_path)

    # Req 3: Two-stage retrieval — pre-filter with embeddings when candidates > 50
    if available_includes:
        # Split formatted entries by the "File: " line prefix
        candidate_entries = re.split(r'(?=^File: )', available_includes, flags=re.MULTILINE)
        candidate_entries = [e.strip() for e in candidate_entries if e.strip()]
        if len(candidate_entries) > 50:
            if verbose:
                console.print(
                    f"[blue]Candidates ({len(candidate_entries)}) exceed 50 — "
                    f"running embedding pre-filter[/blue]"
                )
            filtered_entries = _embed_and_rank(input_prompt, candidate_entries, top_n=50)
            available_includes = "\n".join(filtered_entries)

    # Req 4: invoke LLM with Pydantic structured output
    if verbose:
        console.print(Panel("Step 2: Running auto_include_LLM", style="blue"))

    try:
        llm_response = llm_invoke(
            prompt=auto_include_prompt,
            input_json={
                "input_prompt": input_prompt,
                "available_includes": available_includes,
            },
            output_pydantic=AutoIncludeResult,
            **llm_kwargs,
        )
        total_cost = summary_cost + llm_response["cost"]
        model_name = llm_response["model_name"]
        llm_result: AutoIncludeResult = llm_response["result"]
    except Exception as ex:
        if verbose:
            console.print(f"[red]LLM invocation failed: {ex}[/red]")
        # Req 7: on LLM failure, return empty include_directives
        return "", csv_output, summary_cost, summary_model

    # Normalize the structured result: when the LLM returns both select= and
    # query= on the same include, keep only the deterministic select= for
    # file types that support structural selectors.
    _enforce_select_query_exclusivity(llm_result)

    # Req 4: build include_directives from structured result
    include_directives = _build_include_directives(llm_result)

    # Req 5a: filter duplicates (file path already in input_prompt)
    include_directives = _filter_duplicates(include_directives, input_prompt)

    # Req 5b: filter self-references
    module_name = _extract_module_name(prompt_filename)
    include_directives = _filter_self_references(include_directives, module_name)

    # Req 5c: filter circular dependencies
    if prompt_filename:
        cycles = _detect_circular_dependencies(
            current_prompt=prompt_filename,
            new_directives=include_directives,
        )
        if cycles:
            include_directives = _filter_circular_dependencies(include_directives, cycles)
            for cycle in cycles:
                console.print(
                    f"[yellow]Warning: Filtered circular dependency: "
                    f"{' -> '.join(cycle)}[/yellow]"
                )

    # Req 6: strip selectors from small files
    include_directives = _strip_selectors_from_small_files(include_directives, directory_path=directory_path)

    if verbose:
        console.print(Panel(
            f"Results:\n"
            f"Include directives: {include_directives}\n"
            f"Total Cost: ${total_cost:.6f}\n"
            f"Model Used: {model_name}",
            style="green",
        ))

    # Req 8: return tuple
    return include_directives, csv_output, total_cost, model_name
