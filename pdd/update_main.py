import fnmatch
import re
import subprocess
import sys
from collections import Counter, defaultdict
from typing import Tuple, Optional, List, Dict, Any, Set
import click
from rich import print as rprint
import os
from pathlib import Path
import git
from rich.console import Console
from rich.progress import (
    Progress,
    SpinnerColumn,
    TextColumn,
    BarColumn,
    TimeRemainingColumn,
)
from rich.table import Table
from rich.theme import Theme

from .construct_paths import (
    construct_paths,
    get_tests_dir_from_config,
    detect_context_for_file,
    resolve_effective_config as resolve_target_context,
)
from .config_resolution import resolve_effective_config as resolve_command_config
from .get_language import get_language
from .update_prompt import update_prompt
from .git_update import git_update
from .agentic_common import get_available_agents
from .agentic_update import run_agentic_update
from .sync_determine_operation import calculate_sha256, extract_include_deps, read_fingerprint
from . import DEFAULT_TIME

# Config/data files that should not get prompts in repo-scan mode.
# Users can still target these explicitly with single-file mode.
_SKIP_EXTENSIONS = {
    '.json', '.jsonl', '.yaml', '.yml', '.md', '.toml', '.ini',
    '.css', '.html', '.lock', '.svg', '.png', '.jpg', '.gif',
    '.ico', '.woff', '.woff2', '.ttf', '.eot', '.map',
    '.csv', '.txt',
}
_SKIP_FILENAMES = {
    'package-lock.json', '.prettierrc', '.eslintrc', '.gitignore',
    'tsconfig.json', 'next-env.d.ts',
    'jest.config.js', 'jest.config.ts', 'jest.setup.js', 'jest.setup.ts',
    'next.config.js', 'next.config.ts', 'next.config.mjs',
    'tailwind.config.js', 'tailwind.config.ts',
    'playwright.config.ts', 'playwright.config.js',
    'vitest.config.ts', 'vitest.config.js', 'vitest.config.unit.ts',
    'postcss.config.js', 'postcss.config.mjs', 'postcss.config.cjs',
    'babel.config.js', 'babel.config.json',
    '.eslintrc.js', '.eslintrc.json', '.eslintrc.cjs',
    '.prettierrc.js', '.prettierrc.json', '.prettierrc.cjs',
    'setupTests.ts', 'setupTests.js',
    'mockServiceWorker.js',
}

_SKIP_BASENAME_SUFFIXES = {
    '.config', '.setup',
    '.stories', '.story',
    '.test', '.spec',
    '.e2e.test', '.e2e.spec',
    '.d',
}


def _has_skip_suffix(filepath: str) -> bool:
    """Check if file stem has a skip suffix like .test, .stories, .config."""
    stem = os.path.splitext(os.path.basename(filepath))[0]
    for suffix in _SKIP_BASENAME_SUFFIXES:
        if stem.endswith(suffix):
            return True
    return False


def _load_pddignore(scan_root: str) -> Tuple[List[str], str]:
    """Load .pddignore patterns, searching upward from *scan_root* to git root.

    Returns (patterns, pddignore_dir) where *pddignore_dir* is the directory
    containing the .pddignore file (used as the base for relative-path matching).
    If no file is found, returns ([], scan_root).
    """
    # Walk upward from scan_root to find .pddignore
    current = os.path.abspath(scan_root)
    while True:
        candidate = os.path.join(current, '.pddignore')
        if os.path.isfile(candidate):
            patterns: List[str] = []
            with open(candidate, 'r') as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith('#'):
                        continue
                    patterns.append(line)
            return patterns, current
        parent = os.path.dirname(current)
        if parent == current:
            break
        # Stop at git root (don't escape the repo)
        if os.path.isdir(os.path.join(current, '.git')):
            break
        current = parent
    return [], scan_root


def _has_meaningful_code(filepath: str) -> bool:
    """Return True if a file contains at least one non-blank, non-comment line."""
    try:
        with open(filepath, 'r', errors='replace') as f:
            for line in f:
                stripped = line.strip()
                if stripped and not stripped.startswith('#'):
                    return True
    except (OSError, IOError):
        return False
    return False


def _is_pddignored(filepath: str, pddignore_root: str, patterns: List[str]) -> bool:
    """Check if a file matches any .pddignore pattern.

    Matches against:
    - Relative path from *pddignore_root* (for patterns like ``frontend/src/components/ui/*``)
    - Basename (for patterns like ``*.stories.tsx``)
    - Directory prefix (for patterns ending with ``/`` like ``ui/``)
    """
    try:
        rel_path = os.path.relpath(filepath, pddignore_root).replace('\\', '/')
    except ValueError:
        return False
    basename = os.path.basename(filepath)
    for pat in patterns:
        if pat.endswith('/'):
            # Directory prefix pattern: match if any path component equals the dir name
            dir_name = pat.rstrip('/')
            parts = rel_path.split('/')
            if dir_name in parts[:-1]:
                return True
        else:
            if fnmatch.fnmatch(rel_path, pat):
                return True
            if fnmatch.fnmatch(basename, pat):
                return True
    return False

custom_theme = Theme({
    "info": "cyan",
    "warning": "yellow",
    "error": "bold red",
    "success": "green",
    "path": "dim blue",
})
console = Console(theme=custom_theme)

def _extract_template_vars(concrete_path: str, template: str) -> Optional[Dict[str, str]]:
    """Reverse-match a concrete path against a template to extract variable values.

    Args:
        concrete_path: Actual file path (e.g., "frontend/src/app/billing/page.tsx")
        template: Template pattern (e.g., "frontend/src/{category}/{name}/{name}.tsx")

    Returns:
        Dictionary of extracted variables, or None if no match.
    """
    # Split template into literal and placeholder parts
    parts = re.split(r'(\{[^}]+\})', template)
    regex_parts = []
    seen_vars: Set[str] = set()
    for part in parts:
        m = re.match(r'\{(\w+)\}', part)
        if m:
            var = m.group(1)
            if var in seen_vars:
                regex_parts.append(f'(?P={var})')
            else:
                regex_parts.append(f'(?P<{var}>[^/]+)')
                seen_vars.add(var)
        else:
            regex_parts.append(re.escape(part))

    pattern = '^' + ''.join(regex_parts) + '$'
    match = re.match(pattern, concrete_path)
    if match:
        return match.groupdict()
    return None


def _resolve_prompt_from_pddrc(code_file_path: str, repo_root: str, language: str) -> Optional[str]:
    """Try to resolve prompt path using .pddrc template configuration.

    Loads .pddrc, finds the matching context for the code file, and if the
    context has outputs.prompt.path and outputs.code.path templates, extracts
    template variables from the code path and expands the prompt template.

    Args:
        code_file_path: Path to the code file.
        repo_root: Repository root directory.
        language: Language name for the code file.

    Returns:
        Absolute prompt path string, or None to fall back to default behavior.
    """
    from .construct_paths import _find_pddrc_file, _load_pddrc_config, detect_context_for_file, BUILTIN_EXT_MAP
    from .template_expander import expand_template

    # Prefer .pddrc at repo_root (the caller already resolved the nearest one),
    # fall back to searching from the code file's parent directory.
    pddrc_path = None
    repo_root_pddrc = Path(repo_root) / ".pddrc"
    if repo_root_pddrc.is_file():
        pddrc_path = repo_root_pddrc
    if not pddrc_path:
        pddrc_path = _find_pddrc_file(Path(code_file_path).parent)
    if not pddrc_path:
        return None

    try:
        config = _load_pddrc_config(pddrc_path)
    except Exception:
        return None

    pddrc_parent = pddrc_path.parent

    # Find matching context — use pddrc_parent as the effective root
    context_name, _ = detect_context_for_file(code_file_path, str(pddrc_parent))

    # If paths-based matching only found 'default', try matching via
    # outputs.code.path — needed when paths patterns are prompt-name
    # globs (e.g., "*api_specs_route*") that don't match code file paths.
    if not context_name or context_name == 'default':
        code_abs = os.path.abspath(code_file_path)
        try:
            code_rel = os.path.relpath(code_abs, str(pddrc_parent)).replace('\\', '/')
        except ValueError:
            code_rel = None
        if code_rel:
            contexts = config.get('contexts', {})
            for ctx_name, ctx_config in contexts.items():
                if ctx_name == 'default':
                    continue
                ctx_code_path = ctx_config.get('defaults', {}).get('outputs', {}).get('code', {}).get('path')
                if ctx_code_path and ctx_code_path == code_rel:
                    context_name = ctx_name
                    break

    if not context_name:
        return None

    # Get outputs config from the context
    contexts = config.get('contexts', {})
    context_config = contexts.get(context_name, {})
    defaults = context_config.get('defaults', {})
    outputs = defaults.get('outputs', {})
    prompt_template = outputs.get('prompt', {}).get('path')
    code_template = outputs.get('code', {}).get('path')

    if not prompt_template:
        return None

    # Get code file relative to pddrc_parent (normalize to forward slashes for template matching)
    code_abs = os.path.abspath(code_file_path)
    try:
        code_rel = os.path.relpath(code_abs, str(pddrc_parent)).replace('\\', '/')
    except ValueError:
        return None

    # Extract name from filename (without extension)
    base_name = os.path.splitext(os.path.basename(code_file_path))[0]

    # Try to extract {category} and other vars from code template
    category = ''
    if code_template:
        extracted = _extract_template_vars(code_rel, code_template)
        if extracted:
            category = extracted.get('category', '')
            base_name = extracted.get('name', base_name)

    # Get file extension for language (without leading dot, matching template convention)
    ext = BUILTIN_EXT_MAP.get(language.lower(), '').lstrip('.')

    # Expand prompt template using shared template_expander
    template_context = {
        'name': base_name,
        'category': category,
        'dir_prefix': f'{category}/' if category else '',
        'ext': ext,
        'language': language,
    }
    expanded = expand_template(prompt_template, template_context)

    return str(pddrc_parent / expanded)


def _resolve_existing_prompt_path_case_insensitive(prompt_path: Path) -> Path:
    """Return an existing prompt path using its on-disk filename casing."""
    parent = prompt_path.parent
    if not parent.exists():
        return prompt_path

    target_name = prompt_path.name.lower()
    try:
        for candidate in parent.iterdir():
            if candidate.is_file() and candidate.name.lower() == target_name:
                return candidate
    except OSError:
        return prompt_path

    return prompt_path


def resolve_prompt_code_pair(code_file_path: str, quiet: bool = False, output_dir: Optional[str] = None, create_missing: bool = True) -> Tuple[str, str]:
    """
    Derives the corresponding prompt file path from a code file path.
    Searches for and creates prompts only in the specified output directory or 'prompts' directory.
    If the prompt file does not exist, it creates an empty one in the target directory.
    Preserves the subdirectory structure of the code file relative to the repository root.

    Args:
        code_file_path: Path to the code file
        quiet: Whether to suppress output messages
        output_dir: Custom output directory (overrides default 'prompts' directory)
    """
    language = get_language(os.path.splitext(code_file_path)[1])
    if not language:
        language = "unknown"

    # Extract the filename without extension and directory
    code_filename = os.path.basename(code_file_path)
    base_name, _ = os.path.splitext(code_filename)
    
    code_file_abs_path = os.path.abspath(code_file_path)
    code_dir = os.path.dirname(code_file_abs_path)

    # Find the repository root (where the code file is located)
    # This is needed for relative path calculation to preserve structure
    # First find the git root as fallback and search boundary
    git_root = code_dir
    try:
        import git
        repo = git.Repo(code_dir, search_parent_directories=True)
        git_root = repo.working_tree_dir
    except:
        # If not a git repo, use the directory containing the code file
        pass

    # Find the nearest .pddrc starting from the code file — its parent
    # directory becomes the effective repo_root for path calculations.
    from .construct_paths import _find_nearest_pddrc_for_file
    nearest_pddrc, effective_root = _find_nearest_pddrc_for_file(
        Path(code_file_abs_path), stop_at=Path(git_root)
    )
    repo_root = str(effective_root) if effective_root else git_root

    # Try template-based resolution from .pddrc first (when no explicit output_dir)
    if not output_dir:
        template_path = _resolve_prompt_from_pddrc(code_file_path, repo_root, language)
        if template_path:
            prompt_path = _resolve_existing_prompt_path_case_insensitive(Path(template_path))
            if create_missing:
                if not prompt_path.parent.exists():
                    try:
                        prompt_path.parent.mkdir(parents=True, exist_ok=True)
                        if not quiet:
                            console.print(f"[success]Created prompts directory:[/success] [path]{prompt_path.parent}[/path]")
                    except OSError as e:
                        console.print(f"[error]Failed to create prompts directory: {e}[/error]")
                if not prompt_path.exists():
                    try:
                        prompt_path.touch()
                        if not quiet:
                            console.print(f"[success]Created missing prompt file:[/success] [path]{prompt_path}[/path]")
                    except OSError as e:
                        console.print(f"[error]Failed to create file {prompt_path}: {e}[/error]")
            return str(prompt_path), code_file_path

    # Determine the base prompts directory
    context_config = {}
    if output_dir:
        # Use the custom output directory (absolute path)
        base_prompts_dir = os.path.abspath(output_dir)
    else:
        # Use context-aware prompts_dir from .pddrc if available
        context_name, context_config = detect_context_for_file(code_file_path, repo_root)
        prompts_dir_config = context_config.get("prompts_dir", "prompts")
        if os.path.isabs(prompts_dir_config):
            base_prompts_dir = prompts_dir_config
        else:
            base_prompts_dir = os.path.join(repo_root, prompts_dir_config)

    # Calculate relative path from repo_root to code_dir to preserve structure
    try:
        rel_dir = os.path.relpath(code_dir, repo_root)
        if rel_dir == ".":
            rel_dir = ""
        else:
            # If context has a code root (generate_output_path), strip that prefix
            # E.g., for pdd/commands/file.py with generate_output_path="pdd",
            # strip "pdd/" to get "commands/"
            code_root = context_config.get("generate_output_path", "").rstrip(os.sep + "/")
            if code_root and rel_dir.startswith(code_root + os.sep):
                # Strip the code root prefix
                rel_dir = rel_dir[len(code_root) + len(os.sep):]
            elif code_root and rel_dir == code_root:
                # File is directly in code root
                rel_dir = ""
    except ValueError:
        # Can happen on Windows if paths are on different drives
        rel_dir = ""

    # Construct the final directory including the relative structure
    final_prompts_dir = os.path.join(base_prompts_dir, rel_dir)

    # Construct the prompt filename in the determined directory
    prompt_filename = f"{base_name}_{language.lower()}.prompt"
    prompt_path_str = os.path.join(final_prompts_dir, prompt_filename)
    prompt_path = _resolve_existing_prompt_path_case_insensitive(Path(prompt_path_str))
    prompt_path_str = str(prompt_path)

    # Create directory and empty prompt file only when requested
    if create_missing:
        prompts_path = Path(final_prompts_dir)
        if not prompts_path.exists():
            try:
                prompts_path.mkdir(parents=True, exist_ok=True)
                if not quiet:
                    console.print(f"[success]Created prompts directory:[/success] [path]{final_prompts_dir}[/path]")
            except OSError as e:
                console.print(f"[error]Failed to create prompts directory {final_prompts_dir}: {e}[/error]")

        if not prompt_path.exists():
            try:
                prompt_path.touch()
                if not quiet:
                    console.print(f"[success]Created missing prompt file:[/success] [path]{prompt_path_str}[/path]")
            except OSError as e:
                console.print(f"[error]Failed to create file {prompt_path_str}: {e}[/error]")
                # Even if creation fails, return the intended path

    return prompt_path_str, code_file_path

def find_and_resolve_all_pairs(repo_root: str, quiet: bool = False, extensions: Optional[str] = None, output_dir: Optional[str] = None) -> List[Tuple[str, str]]:
    """
    Scans the repo for code files, resolves their prompt pairs, and returns all pairs.
    """
    pairs = []

    if not quiet:
        console.print(f"[info]Scanning repository and resolving prompt/code pairs...[/info]")

    allowed_extensions: Optional[set] = None
    if extensions:
        ext_list = [e.strip().lower() for e in extensions.split(',')]
        allowed_extensions = {f'.{e}' if not e.startswith('.') else e for e in ext_list}
        if not quiet:
            console.print(f"[info]Filtering for extensions: {', '.join(allowed_extensions)}[/info]")

    # Use git ls-files to respect .gitignore automatically.
    # Falls back to os.walk with hardcoded ignores if git is unavailable.
    all_files = []
    try:
        result = subprocess.run(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
            capture_output=True, text=True, cwd=repo_root, check=True,
        )
        for rel_path in result.stdout.strip().splitlines():
            if rel_path:
                all_files.append(os.path.join(repo_root, rel_path))
    except (subprocess.CalledProcessError, FileNotFoundError):
        # Fallback: os.walk with hardcoded directory ignores
        ignored_dirs = {'.git', '.idea', '.vscode', '__pycache__', 'node_modules',
                         '.venv', 'venv', 'dist', 'build',
                         '.next', '.nuxt', '.output', '.cache', '.turbo',
                         '.parcel-cache', 'coverage', '.pdd'}
        for root, dirs, files in os.walk(repo_root, topdown=True):
            dirs[:] = [d for d in dirs if d not in ignored_dirs]
            for file in files:
                all_files.append(os.path.join(root, file))

    pddignore_patterns, pddignore_root = _load_pddignore(repo_root)

    code_files = [
        f for f in all_files
        if (
            get_language(os.path.splitext(f)[1]) and  # Pass extension, not full path
            not f.endswith('.prompt') and
            not os.path.splitext(os.path.basename(f))[0].startswith('test_') and
            not os.path.splitext(os.path.basename(f))[0].endswith('_example') and
            os.path.splitext(f)[1].lower() not in _SKIP_EXTENSIONS and
            os.path.basename(f) not in _SKIP_FILENAMES and
            not _has_skip_suffix(f) and
            not _is_pddignored(f, pddignore_root, pddignore_patterns) and
            _has_meaningful_code(f)
        )
    ]

    if allowed_extensions:
        code_files = [
            f for f in code_files
            if os.path.splitext(f)[1].lower() in allowed_extensions
        ]
    
    for file_path in code_files:
        prompt_path, code_path = resolve_prompt_code_pair(file_path, quiet, output_dir, create_missing=False)
        pairs.append((prompt_path, code_path))
        
    return pairs

def get_git_changed_files(repo_root: str, base_branch: str = "main") -> Set[str]:
    """Get the set of files changed relative to a base branch.

    Combines three sources:
    - Files changed between merge-base and HEAD (committed changes)
    - Uncommitted changes (staged + unstaged vs HEAD)
    - Untracked files

    Args:
        repo_root: Absolute path to the repository root.
        base_branch: The base branch to compare against.

    Returns:
        Set of absolute file paths that have changed.
    """
    changed: Set[str] = set()

    try:
        # Find the merge base
        merge_base = subprocess.run(
            ["git", "merge-base", "HEAD", base_branch],
            capture_output=True, text=True, cwd=repo_root, check=True,
        ).stdout.strip()

        # Committed changes since merge-base (Added, Copied, Modified, Renamed)
        committed = subprocess.run(
            ["git", "diff", "--name-only", "--diff-filter=ACMR", merge_base, "HEAD"],
            capture_output=True, text=True, cwd=repo_root, check=True,
        ).stdout.strip()
        if committed:
            for f in committed.splitlines():
                changed.add(os.path.join(repo_root, f))
    except subprocess.CalledProcessError:
        # If merge-base fails (e.g., no common ancestor), skip committed changes
        pass

    try:
        # Uncommitted changes (staged + unstaged)
        uncommitted = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            capture_output=True, text=True, cwd=repo_root, check=True,
        ).stdout.strip()
        if uncommitted:
            for f in uncommitted.splitlines():
                changed.add(os.path.join(repo_root, f))
    except subprocess.CalledProcessError:
        pass

    try:
        # Untracked files
        untracked = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard"],
            capture_output=True, text=True, cwd=repo_root, check=True,
        ).stdout.strip()
        if untracked:
            for f in untracked.splitlines():
                changed.add(os.path.join(repo_root, f))
    except subprocess.CalledProcessError:
        pass

    return changed


def derive_basename_and_language(
    code_file_path: str, repo_root: str
) -> Tuple[Optional[str], Optional[str]]:
    """Extract basename (relative path stem) and language from a code file path.

    Uses the path relative to repo_root (without extension) as the basename
    to avoid fingerprint collisions when multiple files share the same filename
    (e.g., settings/page.tsx vs dashboard/page.tsx).

    Args:
        code_file_path: Absolute path to the code file.
        repo_root: Absolute path to the repository root.

    Returns:
        (basename, language) or (None, None) for unknown extensions.
    """
    ext = os.path.splitext(code_file_path)[1]
    language = get_language(ext)
    if not language:
        return None, None

    try:
        rel_path = os.path.relpath(code_file_path, repo_root)
    except ValueError:
        rel_path = os.path.basename(code_file_path)
    basename = os.path.splitext(rel_path)[0]
    return basename, language.lower()


def _check_include_deps_changed(fingerprint) -> Tuple[bool, str]:
    """Check if any stored include dependencies have changed on disk."""
    if not isinstance(fingerprint.include_deps, dict) or not fingerprint.include_deps:
        return False, "no include deps in fingerprint"
    for dep_path_str, stored_hash in fingerprint.include_deps.items():
        dep_path = Path(dep_path_str)
        if not dep_path.exists():
            return True, f"include dependency deleted: {dep_path_str}"
        current_hash = calculate_sha256(dep_path)
        if current_hash is None:
            # Treat unreadable dependencies as changed so they can be re-synced.
            return True, f"include dependency unreadable: {dep_path_str}"
        if current_hash != stored_hash:
            return True, f"include dependency changed: {dep_path_str}"
    return False, "include deps unchanged"


def is_code_changed(
    code_file_path: str,
    repo_root: str,
    git_changed_files: Set[str],
    prompt_file_path: Optional[str] = None,
) -> Tuple[bool, str]:
    """Determine whether a code file has changed since last sync.

    Strategy:
    1. If a fingerprint exists, compare current SHA256 vs stored code_hash.
    2. If code hash matches, check stored include dependency hashes.
    3. If no fingerprint, fall back to git changed-files set.

    When *prompt_file_path* is provided, uses ``infer_module_identity`` to
    derive the fingerprint key (matching the write path in update_main).
    Falls back to ``derive_basename_and_language`` otherwise.

    Args:
        code_file_path: Absolute path to the code file.
        repo_root: Absolute path to the repository root.
        git_changed_files: Set of absolute paths from get_git_changed_files().
        prompt_file_path: Optional prompt path for accurate fingerprint lookup.

    Returns:
        (is_changed, reason) tuple.
    """
    basename, language = None, None

    # Prefer prompt-path-based identity (matches the write path)
    if prompt_file_path:
        from .operation_log import infer_module_identity
        basename, language = infer_module_identity(prompt_file_path)

    # Fallback to code-path-based identity
    if basename is None or language is None:
        basename, language = derive_basename_and_language(code_file_path, repo_root)

    if basename is None or language is None:
        return False, "unknown extension"

    fingerprint = read_fingerprint(basename, language)

    if fingerprint is not None:
        stored_hash = fingerprint.code_hash
        if stored_hash is None:
            return True, "fingerprint exists but has no code_hash"

        current_hash = calculate_sha256(Path(code_file_path))
        if current_hash is None:
            return False, "could not compute current hash"

        if current_hash != stored_hash:
            return True, "code hash differs from fingerprint"

        # Check include dependencies (shared files like preambles, examples)
        include_changed, include_reason = _check_include_deps_changed(fingerprint)
        if include_changed:
            return True, include_reason

        return False, "code hash matches fingerprint"

    # No fingerprint — fall back to git
    abs_path = os.path.abspath(code_file_path)
    if abs_path in git_changed_files:
        return True, "no fingerprint, file in git changed set"
    return False, "no fingerprint, file not in git changed set"


def update_file_pair(
    prompt_file: str,
    code_file: str,
    ctx: click.Context,
    repo: git.Repo,
    simple: bool = False,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
) -> Dict[str, Any]:
    """
    Wrapper to update a single file pair, choosing the correct method based on Git status and prompt content.
    """
    try:
        verbose = ctx.obj.get("verbose", False)
        quiet = ctx.obj.get("quiet", False)

        # Agentic routing - try first before legacy paths
        use_agentic = not simple and get_available_agents()

        if use_agentic:
            tests_dir = get_tests_dir_from_config()
            success, message, agentic_cost, provider, changed_files = run_agentic_update(
                prompt_file=prompt_file,
                code_file=code_file,
                test_files=None,
                tests_dir=tests_dir,
                verbose=verbose,
                quiet=quiet,
            )

            if success:
                with open(prompt_file, 'r') as f:
                    modified_prompt = f.read()
                return {
                    "prompt_file": prompt_file,
                    "status": "✅ Success (agentic)",
                    "cost": agentic_cost,
                    "model": provider,
                    "error": "",
                }
            # Agentic failed - fall through to legacy

        # Legacy path: Read the prompt first to decide the strategy.
        try:
            with open(prompt_file, 'r') as f:
                input_prompt = f.read()
        except FileNotFoundError:
            input_prompt = ""

        relative_code_path = os.path.relpath(code_file, repo.working_tree_dir)
        is_untracked = relative_code_path in repo.untracked_files

        # GENERATION MODE: Trigger if the file is new OR if the prompt is empty.
        if is_untracked or not input_prompt.strip():
            if not quiet:
                if is_untracked:
                    console.print(f"[info]New untracked file detected, generating new prompt for:[/info] [path]{relative_code_path}[/path]")
                else:
                    console.print(f"[info]Empty prompt detected, generating new prompt for:[/info] [path]{relative_code_path}[/path]")

            with open(code_file, 'r') as f:
                modified_code = f.read()

            effective_config = _resolve_update_runtime_config(
                ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                strength=strength,
                temperature=temperature,
            )
            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt="no prompt exists yet, create a new one",
                input_code="",  # No previous version for generation
                modified_code=modified_code,
                strength=effective_config["strength"],
                temperature=effective_config["temperature"],
                verbose=verbose,
                time=ctx.obj.get('time', DEFAULT_TIME),
            )
        # UPDATE MODE: Only trigger if the file is tracked AND the prompt has content.
        else:
            effective_config = _resolve_update_runtime_config(
                ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                strength=strength,
                temperature=temperature,
            )
            modified_prompt, total_cost, model_name = git_update(
                input_prompt=input_prompt,
                modified_code_file=code_file,
                strength=effective_config["strength"],
                temperature=effective_config["temperature"],
                verbose=verbose,
                time=ctx.obj.get('time', DEFAULT_TIME),
                simple=True,  # Force legacy since we already tried agentic,
                quiet=quiet,
                prompt_file=prompt_file,
            )

        if modified_prompt is not None:
            # Overwrite the original prompt file
            with open(prompt_file, "w") as f:
                f.write(modified_prompt)
            return {
                "prompt_file": prompt_file,
                "status": "✅ Success",
                "cost": total_cost,
                "model": model_name,
                "error": "",
            }
        else:
            return {
                "prompt_file": prompt_file,
                "status": "❌ Failed",
                "cost": 0.0,
                "model": "",
                "error": "Update process returned no result.",
            }
    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        return {
            "prompt_file": prompt_file,
            "status": "❌ Failed",
            "cost": 0.0,
            "model": "",
            "error": str(e),
        }

def _read_text_byte_len(path: str) -> int:
    """Best-effort size of file text for dry-run cost sizing (chars)."""
    try:
        return len(Path(path).read_text(encoding="utf-8", errors="ignore"))
    except (OSError, IOError):
        return 0


def _repo_relative_md_dep(dep_str: str, repo_root_p: Path) -> Optional[str]:
    """Return repo-relative path for a resolved include target, or None if outside repo / not doc."""
    dep_p = Path(dep_str)
    if not dep_p.is_absolute():
        dep_p = (Path.cwd() / dep_p).resolve()
    else:
        dep_p = dep_p.resolve()
    if dep_p.suffix.lower() not in (".md", ".mdx"):
        return None
    try:
        rel = dep_p.relative_to(repo_root_p)
    except ValueError:
        return None
    return str(rel).replace("\\", "/")


def _md_doc_prompt_reference_counts(
    repo_root: str, prompt_paths: List[str]
) -> Dict[str, Set[str]]:
    """Map repo-relative .md/.mdx → set of prompt paths that <include> it (scan-wide)."""
    repo_root_p = Path(repo_root).resolve()
    doc_to_prompts: Dict[str, Set[str]] = defaultdict(set)
    for prompt_path_str in prompt_paths:
        deps = extract_include_deps(Path(prompt_path_str))
        for dep_str in deps:
            rel = _repo_relative_md_dep(dep_str, repo_root_p)
            if rel:
                doc_to_prompts[rel].add(prompt_path_str)
    return doc_to_prompts


def _included_docs_for_drift_report(
    repo_root: str,
    all_prompt_paths: List[str],
    drifted_prompt_paths: List[str],
) -> List[Tuple[str, int]]:
    """Docs referenced by at least one drifted prompt; count = prompts in full scan that include each doc."""
    drifted_set = set(drifted_prompt_paths)
    doc_to_prompts = _md_doc_prompt_reference_counts(repo_root, all_prompt_paths)
    rows: List[Tuple[str, int]] = []
    for doc_rel, prompters in doc_to_prompts.items():
        if not prompters & drifted_set:
            continue
        rows.append((doc_rel, len(prompters)))
    return sorted(rows, key=lambda x: (-x[1], x[0]))


def _resolve_update_runtime_config(
    ctx: click.Context,
    *,
    prompt_file: Optional[str] = None,
    code_file: Optional[str] = None,
    resolved_config: Optional[Dict[str, Any]] = None,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
) -> Dict[str, Any]:
    """Resolve effective update config for a single target.

    Update flows can span multiple contexts in one command, especially in repo mode,
    so config must be resolved per target instead of written once into ``ctx.obj``.
    """

    if resolved_config is None:
        quiet = ctx.obj.get("quiet", False)
        context_override = ctx.obj.get("context")
        candidate_paths: List[str] = []
        if prompt_file:
            candidate_paths.append(prompt_file)
        if code_file and code_file not in candidate_paths:
            candidate_paths.append(code_file)

        resolved_candidates: List[Dict[str, Any]] = []
        for candidate in candidate_paths:
            candidate_path = Path(candidate)
            candidate_cwd = candidate_path.parent if candidate_path.parent else Path.cwd()
            _, _, _, candidate_config, _ = resolve_target_context(
                cli_options={},
                context_override=context_override,
                cwd=candidate_cwd,
                prompt_file=str(candidate_path),
                quiet=quiet,
            )
            resolved_candidates.append(candidate_config)
            if candidate_config.get("_matched_context") not in ("default", "none"):
                resolved_config = candidate_config
                break

        if resolved_config is None:
            if resolved_candidates:
                resolved_config = resolved_candidates[0]
            else:
                _, _, _, resolved_config, _ = resolve_target_context(
                    cli_options={},
                    context_override=context_override,
                    cwd=Path.cwd(),
                    quiet=quiet,
                )

    return resolve_command_config(
        ctx,
        resolved_config,
        param_overrides={"strength": strength, "temperature": temperature},
    )


def _estimate_dry_run_cost_range(
    ctx: click.Context,
    repo_obj: git.Repo,
    simple: bool,
    changed_items: List[Tuple[str, str, str]],
) -> Tuple[float, float]:
    """Flat heuristic total $ range for dry-run (not billed).

    Historically, each per-file update tends to cost around $0.50–$1.00. For dry-run,
    report a simple flat estimate based on the number of drifted pairs.
    """
    n = len(changed_items)
    return (n * 0.5, n * 1.0)


def _print_repository_drift_report(
    repo_root: str,
    n_changed: int,
    n_pairs: int,
    changed_items: List[Tuple[str, str, str]],
    included_docs: List[Tuple[str, int]],
    cost_low: float,
    cost_high: float,
) -> None:
    """Print the repository drift summary for `pdd update --dry-run` (no LLM)."""
    console.print()
    console.print("[bold]Repository drift report:[/bold]")
    console.print(f"  Changed files: [cyan]{n_changed}[/cyan] of [cyan]{n_pairs}[/cyan] pairs")
    console.print(
        f"  Estimated cost: [yellow]${cost_low:.2f}–${cost_high:.2f}[/yellow] "
        "(flat $0.50–$1.00 per drifted pair; not billed in dry run)"
    )
    console.print()
    console.print("  [bold]Drifted modules:[/bold]")
    rows = sorted(changed_items, key=lambda x: x[1])
    code_width = 0
    for _p, code_path, _r in rows:
        code_width = max(code_width, len(os.path.relpath(code_path, repo_root)))
    code_width = min(max(code_width, 12), 52)
    for i, (prompt_path, code_path, _reason) in enumerate(rows, start=1):
        cr = os.path.relpath(code_path, repo_root)
        pr = os.path.relpath(prompt_path, repo_root)
        pad = max(code_width - len(cr), 0)
        console.print(f"    {i}. {cr}{' ' * pad}  →  {pr}")
    console.print()
    console.print("  [bold]Included docs that may need updating:[/bold]")
    if not included_docs:
        console.print("    [dim](none detected among drifted prompts)[/dim]")
    else:
        for doc_rel, cnt in included_docs:
            console.print(f"    - {doc_rel} (included by {cnt} prompt{'s' if cnt != 1 else ''})")
    console.print()


def _find_prd_file(project_root: Path) -> Optional[Path]:
    """Find PRD file by convention: PRD.md, prd.md, *_prd.md, *_PRD.md."""
    for pattern in ["PRD.md", "prd.md", "*_prd.md", "*_PRD.md"]:
        matches = list(project_root.glob(pattern))
        if matches:
            return matches[0]
    return None


def update_main(
    ctx: click.Context,
    input_prompt_file: Optional[str],
    modified_code_file: Optional[str],
    input_code_file: Optional[str],
    output: Optional[str],
    use_git: bool = False,
    repo: bool = False,
    extensions: Optional[str] = None,
    directory: Optional[str] = None,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    simple: bool = False,
    base_branch: str = "main",
    budget: Optional[float] = None,
    dry_run: bool = False,
) -> Optional[Tuple[str, float, str]]:
    """
    CLI wrapper for updating prompts based on modified code.
    Can operate on a single file or an entire repository.

    :param ctx: Click context object containing CLI options and parameters.
    :param input_prompt_file: Path to the original prompt file.
    :param modified_code_file: Path to the modified code file.
    :param input_code_file: Optional path to the original code file. If None, Git history is used if --git is True.
    :param output: Optional path to save the updated prompt.
    :param use_git: Use Git history to retrieve the original code if True.
    :param repo: If True, run in repository-wide mode.
    :param extensions: Comma-separated string of file extensions to filter by in repo mode.
    :param directory: Optional directory to scan in repo mode (defaults to repo root).
    :param strength: Optional strength parameter (overrides ctx.obj if provided).
    :param temperature: Optional temperature parameter (overrides ctx.obj if provided).
    :param base_branch: Git branch to compare against for change detection in repo mode.
    :param budget: Optional repository-wide cap; stop processing once cumulative update cost reaches this amount.
    :param dry_run: If True in repo mode, list pending updates only (no LLM, no prompt writes, no architecture/PRD sync).
    :return: Tuple containing the updated prompt, total cost, and model name.
    """
    quiet = ctx.obj.get("quiet", False)
    if repo:
        try:
            # Find the repo root by searching up from the current directory
            repo_obj = git.Repo(os.getcwd(), search_parent_directories=True)
            repo_root = repo_obj.working_tree_dir
        except git.InvalidGitRepositoryError:
            rprint("[bold red]Error:[/bold red] Repository-wide mode requires the current directory to be within a Git repository.")
            # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
            return None

        # Use specified directory if provided; if CWD has its own .pddrc
        # (subdirectory project), scope scan to CWD instead of the git root.
        if directory:
            scan_dir = os.path.abspath(directory)
        else:
            cwd = os.getcwd()
            cwd_pddrc = Path(cwd) / ".pddrc"
            if cwd_pddrc.is_file() and os.path.abspath(cwd) != os.path.abspath(repo_root):
                scan_dir = cwd
            else:
                scan_dir = repo_root
        pairs = find_and_resolve_all_pairs(scan_dir, quiet, extensions, output)

        if pairs and not dry_run:
            from .pddrc_initializer import ensure_pddrc_for_scan
            code_files_for_pddrc = [code_path for _, code_path in pairs]
            ensure_pddrc_for_scan(scan_dir, repo_root, code_files_for_pddrc, quiet=quiet)

        if not pairs:
            rprint("[info]No scannable code files found in the repository.[/info]")
            return None

        # Change-detection: filter to changed code files OR empty prompts
        git_changed_files = get_git_changed_files(repo_root, base_branch)

        changed_items = []
        for prompt_path, code_path in pairs:
            # Empty prompts always need generation, regardless of code changes
            prompt_p = Path(prompt_path)
            if prompt_p.exists() and prompt_p.stat().st_size == 0:
                changed_items.append((prompt_path, code_path, "empty prompt file"))
                continue
            changed, reason = is_code_changed(code_path, repo_root, git_changed_files, prompt_file_path=prompt_path)
            if changed:
                changed_items.append((prompt_path, code_path, reason))

        if not changed_items:
            if not quiet:
                rprint("[info]No changed code files detected. Everything is in sync.[/info]")
            return None

        if dry_run:
            if not quiet:
                drift_prompts = [p for p, _c, _r in changed_items]
                all_prompt_paths = [p for p, _c in pairs]
                included_docs = _included_docs_for_drift_report(
                    repo_root, all_prompt_paths, drift_prompts
                )
                cost_low, cost_high = _estimate_dry_run_cost_range(
                    ctx, repo_obj, simple, changed_items
                )
                _print_repository_drift_report(
                    repo_root,
                    len(changed_items),
                    len(pairs),
                    changed_items,
                    included_docs,
                    cost_low,
                    cost_high,
                )
                rprint(
                    "[dim]No LLM calls, no prompt writes, no architecture or PRD sync.[/dim]"
                )
            n = len(changed_items)
            return (
                f"Dry run: {n} prompt(s) would be updated (no changes made).",
                0.0,
                "N/A",
            )

        if not quiet:
            rprint(
                f"[info]Found {len(changed_items)} changed file(s) "
                f"out of {len(pairs)} total pairs.[/info]"
            )

        results = []
        total_repo_cost = 0.0
        budget_reached = False

        progress = Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}", justify="right"),
            BarColumn(bar_width=None),
            TextColumn("[progress.percentage]{task.percentage:>3.1f}%"),
            TextColumn("•"),
            TimeRemainingColumn(),
            TextColumn("•"),
            TextColumn("Total Cost: $[bold green]{task.fields[total_cost]:.6f}[/bold green]"),
            console=console,
            transient=True,
        )

        with progress:
            task = progress.add_task(
                "Updating prompts...",
                total=len(changed_items),
                total_cost=0.0
            )

            for prompt_path, code_path, _reason in changed_items:
                if budget is not None and total_repo_cost >= budget:
                    budget_reached = True
                    if not quiet:
                        rprint(
                            f"[info]Budget cap reached (${budget:.2f}); "
                            f"stopping with {len(results)} file(s) processed.[/info]"
                        )
                    break
                relative_path = os.path.relpath(code_path, repo_root)
                progress.update(task, description=f"Processing [path]{relative_path}[/path]")

                result = update_file_pair(
                    prompt_path,
                    code_path,
                    ctx,
                    repo_obj,
                    simple=simple,
                    strength=strength,
                    temperature=temperature,
                )
                results.append(result)

                total_repo_cost += result.get("cost", 0.0)

                # Save fingerprint so the file isn't detected as changed next run
                if "Success" in result.get("status", ""):
                    from .operation_log import save_fingerprint, infer_module_identity
                    basename, language = infer_module_identity(prompt_path)
                    if basename and language:
                        try:
                            paths = {
                                "prompt": Path(prompt_path),
                                "code": Path(code_path),
                            }
                            save_fingerprint(
                                basename, language,
                                operation="update",
                                paths=paths,
                                cost=result.get("cost", 0.0),
                                model=result.get("model", "unknown"),
                            )
                        except Exception:
                            pass  # Best-effort; don't fail the update

                progress.update(task, advance=1, total_cost=total_repo_cost)

        # --- Post-update: Architecture sync ---
        arch_entries_updated = 0
        prd_status = "skipped"

        # Determine prompts directory and architecture path
        prompts_dir = Path(repo_root) / "prompts"
        from .architecture_registry import find_architecture_for_project
        arch_files = find_architecture_for_project(Path(repo_root))
        architecture_path = arch_files[0] if arch_files else Path(repo_root) / "architecture.json"

        successful_prompts = [
            res["prompt_file"] for res in results
            if "Success" in res.get("status", "")
        ]

        if successful_prompts and architecture_path.exists():
            from .architecture_sync import update_architecture_from_prompt
            for prompt_file in successful_prompts:
                prompt_filename = os.path.basename(prompt_file)
                try:
                    arch_result = update_architecture_from_prompt(
                        prompt_filename,
                        prompts_dir=prompts_dir,
                        architecture_path=architecture_path,
                    )
                    if arch_result.get("success") and arch_result.get("updated"):
                        arch_entries_updated += 1
                except Exception:
                    # Architecture sync is best-effort; don't fail the update
                    pass

        # --- Post-update: PRD sync (only if architecture changed) ---
        if arch_entries_updated > 0:
            prd_file = _find_prd_file(Path(repo_root))
            if prd_file is None:
                prd_status = "not found"
            else:
                try:
                    from .agentic_common import run_agentic_task

                    prd_content = prd_file.read_text(encoding="utf-8")
                    arch_json = architecture_path.read_text(encoding="utf-8")

                    instruction = (
                        "You are reviewing whether a PRD (Product Requirements Document) needs updating "
                        "after architecture changes.\n\n"
                        f"Current PRD:\n{prd_content}\n\n"
                        f"Updated architecture.json:\n{arch_json}\n\n"
                        f"Architecture entries updated: {arch_entries_updated}\n\n"
                        "If the PRD needs updating to reflect these architecture changes, output the "
                        "complete updated PRD between <updated-prd> and </updated-prd> tags.\n"
                        "If no update is needed, output: NO_UPDATE_NEEDED"
                    )

                    llm_output = run_agentic_task(
                        instruction=instruction,
                        cwd=Path(repo_root),
                        verbose=ctx.obj.get("verbose", False),
                        quiet=True,
                        label="prd-sync",
                    )

                    if llm_output and "<updated-prd>" in llm_output:
                        import re
                        match = re.search(
                            r"<updated-prd>(.*?)</updated-prd>",
                            llm_output,
                            re.DOTALL,
                        )
                        if match:
                            prd_file.write_text(match.group(1).strip() + "\n", encoding="utf-8")
                            prd_status = "updated"
                        else:
                            prd_status = "unchanged"
                    else:
                        prd_status = "unchanged"
                except Exception:
                    prd_status = "error"
        else:
            prd_status = "skipped (no arch changes)"

        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Prompt File", style="dim", width=50)
        table.add_column("Status")
        table.add_column("Cost", justify="right")
        table.add_column("Model")
        table.add_column("Error", style="error")

        models_used = set()
        for res in sorted(results, key=lambda x: x["prompt_file"]):
            table.add_row(
                os.path.relpath(res["prompt_file"], repo_root),
                res["status"],
                f"${res['cost']:.6f}",
                res["model"],
                res["error"],
            )
            if res["model"]:
                models_used.add(res["model"])

        console.print("\n[bold]Repository Update Summary[/bold]")
        console.print(table)
        if budget_reached:
            console.print(f"[info]Budget cap reached: ${budget:.2f}[/info]")
        if arch_entries_updated > 0 or prd_status != "skipped (no arch changes)":
            console.print(f"\n[info]Architecture entries updated: {arch_entries_updated}[/info]")
            console.print(f"[info]PRD status: {prd_status}[/info]")
        console.print(f"\n[bold]Total Estimated Cost: ${total_repo_cost:.6f}[/bold]")

        final_model_str = ", ".join(sorted(models_used)) if models_used else "N/A"
        return "Repository update complete.", total_repo_cost, final_model_str

    # --- Single file logic ---
    try:
        # Case 1: Regeneration Mode.
        # Triggered when ONLY the modified_code_file is provided.
        # This creates a new prompt or overwrites an existing one from scratch.
        is_regeneration_mode = (input_prompt_file is None and input_code_file is None)

        if is_regeneration_mode:
            if not quiet:
                rprint("[bold yellow]Regeneration mode: Creating or overwriting prompt from code file.[/bold yellow]")

            # Determine output path based on --output flag
            if output:
                # Check if output is a directory or file path
                if os.path.isdir(output) or output.endswith('/'):
                    # Output is a directory, pass as output_dir to resolve_prompt_code_pair
                    prompt_path, _ = resolve_prompt_code_pair(modified_code_file, quiet, output)
                else:
                    # Output is a specific file path, use it directly
                    prompt_path = os.path.abspath(output)
                    # Ensure the directory exists
                    os.makedirs(os.path.dirname(prompt_path), exist_ok=True)
            else:
                # No output specified, use default behavior
                prompt_path, _ = resolve_prompt_code_pair(modified_code_file, quiet)

            # Agentic routing for regeneration mode
            use_agentic = not simple and get_available_agents()
            verbose = ctx.obj.get("verbose", False)

            if use_agentic:
                # Ensure prompt file exists for agentic
                Path(prompt_path).touch(exist_ok=True)

                tests_dir = get_tests_dir_from_config()
                success, message, agentic_cost, provider, changed_files = run_agentic_update(
                    prompt_file=prompt_path,
                    code_file=modified_code_file,
                    test_files=None,
                    tests_dir=tests_dir,
                    verbose=verbose,
                    quiet=quiet,
                )

                if success:
                    with open(prompt_path, 'r') as f:
                        generated_prompt = f.read()

                    if not quiet:
                        rprint("[bold green]Prompt generated successfully (agentic).[/bold green]")
                        rprint(f"[bold]Provider:[/bold] {provider}")
                        rprint(f"[bold]Total cost:[/bold] ${agentic_cost:.6f}")
                        rprint(f"[bold]Prompt saved to:[/bold] {prompt_path}")

                    return generated_prompt, agentic_cost, provider

                # Agentic failed - fall through to legacy
                if not quiet:
                    rprint(f"[warning]Agentic failed: {message}. Falling back to legacy.[/warning]")

            # Legacy path
            with open(modified_code_file, 'r') as f:
                modified_code_content = f.read()

            # Read the existing prompt when one is present so the LLM can
            # preserve its structure. Only fall back to the first-time
            # sentinel when the file truly doesn't exist or is empty —
            # otherwise the legacy path regenerates from scratch and strips
            # <pdd.*> tags, <include> preambles, and % markers (gltanaka/pdd#1220).
            existing_prompt_text = ""
            try:
                if prompt_path and Path(prompt_path).exists():
                    existing_prompt_text = Path(prompt_path).read_text()
            except (OSError, UnicodeDecodeError):
                # OSError: I/O failure. UnicodeDecodeError: corrupt/binary
                # prompt file (e.g., mojibake from a prior destructive heal).
                # In both cases, degrade to the first-time sentinel rather
                # than crashing the whole update pipeline.
                existing_prompt_text = ""

            input_prompt_arg = (
                existing_prompt_text
                if existing_prompt_text.strip()
                else "no prompt exists yet, create a new one"
            )
            effective_config = _resolve_update_runtime_config(
                ctx,
                prompt_file=prompt_path,
                code_file=modified_code_file,
                strength=strength,
                temperature=temperature,
            )

            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt=input_prompt_arg,
                input_code="",
                modified_code=modified_code_content,
                strength=effective_config["strength"],
                temperature=effective_config["temperature"],
                verbose=verbose,
                time=ctx.obj.get('time', DEFAULT_TIME)
            )

            # Write the result to the derived/correct prompt path.
            with open(prompt_path, "w") as f:
                f.write(modified_prompt)

            if not quiet:
                rprint("[bold green]Prompt generated successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                rprint(f"[bold]Prompt saved to:[/bold] {prompt_path}")

            return modified_prompt, total_cost, model_name

        # Case 2: True Update Mode.
        # Triggered when the user provides the prompt file, indicating a desire to update it.
        else:
            actual_input_prompt_file = input_prompt_file
            final_output_path = output or actual_input_prompt_file
            verbose = ctx.obj.get("verbose", False)

            # Agentic routing for true update mode (try before construct_paths)
            use_agentic = not simple and get_available_agents()

            if use_agentic:
                tests_dir = get_tests_dir_from_config()

                # If output differs from input, work on a copy to avoid modifying source
                if final_output_path != actual_input_prompt_file:
                    import shutil
                    shutil.copy2(actual_input_prompt_file, final_output_path)
                    agentic_prompt_file = final_output_path
                else:
                    agentic_prompt_file = actual_input_prompt_file

                success, message, agentic_cost, provider, changed_files = run_agentic_update(
                    prompt_file=agentic_prompt_file,
                    code_file=modified_code_file,
                    test_files=None,
                    tests_dir=tests_dir,
                    verbose=verbose,
                    quiet=quiet,
                )

                if success:
                    with open(agentic_prompt_file, 'r') as f:
                        updated_prompt = f.read()

                    if not quiet:
                        rprint("[bold green]Prompt updated successfully (agentic).[/bold green]")
                        rprint(f"[bold]Provider:[/bold] {provider}")
                        rprint(f"[bold]Total cost:[/bold] ${agentic_cost:.6f}")
                        rprint(f"[bold]Updated prompt saved to:[/bold] {final_output_path}")

                    return updated_prompt, agentic_cost, provider

                # Agentic failed - fall through to legacy
                if not quiet:
                    rprint(f"[warning]Agentic failed: {message}. Falling back to legacy.[/warning]")

            # Legacy path: Prepare input_file_paths for construct_paths
            input_file_paths = {
                "input_prompt_file": actual_input_prompt_file,
                "modified_code_file": modified_code_file
            }
            if input_code_file:
                input_file_paths["input_code_file"] = input_code_file

            command_options = {"output": final_output_path}

            resolved_config, input_strings, output_file_paths, _ = construct_paths(
                input_file_paths=input_file_paths,
                force=ctx.obj.get("force", False),
                quiet=quiet,
                command="update",
                command_options=command_options,
                context_override=ctx.obj.get('context'),
                confirm_callback=ctx.obj.get('confirm_callback')
            )

            input_prompt = input_strings["input_prompt_file"]
            modified_code = input_strings["modified_code_file"]
            input_code = input_strings.get("input_code_file")
            time = ctx.obj.get('time', DEFAULT_TIME)
            effective_config = _resolve_update_runtime_config(
                ctx,
                prompt_file=actual_input_prompt_file,
                code_file=modified_code_file,
                resolved_config=resolved_config,
                strength=strength,
                temperature=temperature,
            )

            if not modified_code.strip():
                raise ValueError("Modified code file cannot be empty when updating or generating a prompt.")

            if not input_prompt.strip():
                input_prompt = "no prompt exists yet, create a new one"
                if not use_git and input_code is None:
                    input_code = ""
                if not quiet:
                    rprint("[bold yellow]Empty prompt file detected. Generating a new prompt from the modified code.[/bold yellow]")

            if use_git:
                if input_code_file:
                    raise ValueError("Cannot use both --git and provide an input code file.")
                modified_prompt, total_cost, model_name = git_update(
                    input_prompt=input_prompt,
                    modified_code_file=modified_code_file,
                    strength=effective_config["strength"],
                    temperature=effective_config["temperature"],
                    verbose=verbose,
                    time=time,
                    simple=True if use_agentic else simple,  # Force legacy if agentic was tried
                    quiet=quiet,
                    prompt_file=actual_input_prompt_file,
                )
            else:
                if input_code is None:
                    # This will now only be triggered if --git is not used and no input_code_file is provided,
                    # which is an error state for a true update.
                    raise ValueError("For a true update, you must either provide an original code file or use the --git flag.")

                modified_prompt, total_cost, model_name = update_prompt(
                    input_prompt=input_prompt,
                    input_code=input_code,
                    modified_code=modified_code,
                    strength=effective_config["strength"],
                    temperature=effective_config["temperature"],
                    verbose=verbose,
                    time=time
                )

            # Defense-in-depth: validate prompt is not empty before writing
            if not modified_prompt or not modified_prompt.strip():
                raise ValueError(
                    "Update produced an empty prompt. The LLM may have failed to generate a valid response."
                )

            with open(output_file_paths["output"], "w") as f:
                f.write(modified_prompt)

            if not quiet:
                rprint("[bold green]Prompt updated successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                rprint(f"[bold]Updated prompt saved to:[/bold] {output_file_paths['output']}")

            return modified_prompt, total_cost, model_name

    except (ValueError, git.InvalidGitRepositoryError) as e:
        if not quiet:
            rprint(f"[bold red]Input error:[/bold red] {str(e)}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return None
    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return None
