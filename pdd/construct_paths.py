# pdd/construct_paths.py
from __future__ import annotations

import sys
import os
from pathlib import Path
from typing import Dict, Tuple, Any, Optional, List, Callable
import fnmatch
import logging

import click
import yaml
from rich.console import Console
from rich.theme import Theme

from .get_extension import get_extension
from .get_language import get_language
from .generate_output_paths import generate_output_paths

# Assume generate_output_paths raises ValueError on unknown command

# Add csv import for the new helper function
import csv

console = Console(theme=Theme({"info": "cyan", "warning": "yellow", "error": "bold red"}))

# Configuration loading functions
def _find_pddrc_file(start_path: Optional[Path] = None) -> Optional[Path]:
    """Find .pddrc file by searching upward from the given path."""
    if start_path is None:
        start_path = Path.cwd()
    
    # Search upward through parent directories
    for path in [start_path] + list(start_path.parents):
        pddrc_file = path / ".pddrc"
        if pddrc_file.is_file():
            return pddrc_file
    return None

def _load_pddrc_config(pddrc_path: Path) -> Dict[str, Any]:
    """Load and parse .pddrc configuration file."""
    try:
        with open(pddrc_path, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)
        
        if not isinstance(config, dict):
            raise ValueError(f"Invalid .pddrc format: expected dictionary at root level")
        
        # Validate basic structure
        if 'contexts' not in config:
            raise ValueError(f"Invalid .pddrc format: missing 'contexts' section")
        
        return config
    except yaml.YAMLError as e:
        raise ValueError(f"YAML syntax error in .pddrc: {e}")
    except Exception as e:
        raise ValueError(f"Error loading .pddrc: {e}")

def list_available_contexts(start_path: Optional[Path] = None) -> list[str]:
    """Return sorted context names from the nearest .pddrc.

    - Searches upward from `start_path` (or CWD) for a `.pddrc` file.
    - If found, loads and validates it, then returns sorted context names.
    - If no `.pddrc` exists, returns ["default"].
    - Propagates ValueError for malformed `.pddrc` to allow callers to render
      helpful errors.
    """
    pddrc = _find_pddrc_file(start_path)
    if not pddrc:
        return ["default"]
    config = _load_pddrc_config(pddrc)
    contexts = config.get("contexts", {})
    names = sorted(contexts.keys()) if isinstance(contexts, dict) else []
    return names or ["default"]

def _match_path_to_contexts(
    path_str: str,
    contexts: Dict[str, Any],
    use_specificity: bool = False,
    is_absolute: bool = False
) -> Optional[str]:
    """
    Core pattern matching logic - matches a path against context patterns.

    Args:
        path_str: Path to match (can be relative or absolute)
        contexts: The contexts dict from .pddrc config
        use_specificity: If True, return most specific match; else first match
        is_absolute: If True, use absolute path matching with "*/" prefix

    Returns:
        Context name or None
    """
    matches = []
    for context_name, context_config in contexts.items():
        if context_name == 'default':
            continue
        for path_pattern in context_config.get('paths', []):
            pattern_base = path_pattern.rstrip('/**').rstrip('/*')

            # Check for match - handle both absolute and relative paths
            matched = False
            if is_absolute:
                # For absolute paths (CWD-based detection), use existing logic
                if fnmatch.fnmatch(path_str, f"*/{path_pattern}") or \
                   fnmatch.fnmatch(path_str, path_pattern) or \
                   path_str.endswith(f"/{pattern_base}"):
                    matched = True
            else:
                # For relative paths (file-based detection)
                if fnmatch.fnmatch(path_str, path_pattern) or \
                   path_str.startswith(pattern_base + '/') or \
                   path_str.startswith(pattern_base):
                    matched = True

            if matched:
                if not use_specificity:
                    return context_name  # First match wins
                matches.append((context_name, len(pattern_base)))

    if matches:
        matches.sort(key=lambda x: x[1], reverse=True)
        return matches[0][0]

    return 'default' if 'default' in contexts else None


def _detect_context(current_dir: Path, config: Dict[str, Any], context_override: Optional[str] = None) -> Optional[str]:
    """Detect the appropriate context based on current directory path."""
    if context_override:
        # Validate that the override context exists
        contexts = config.get('contexts', {})
        if context_override not in contexts:
            available = list(contexts.keys())
            raise ValueError(f"Unknown context '{context_override}'. Available contexts: {available}")
        return context_override

    contexts = config.get('contexts', {})
    return _match_path_to_contexts(str(current_dir), contexts, use_specificity=False, is_absolute=True)


def detect_context_for_file(file_path: str, repo_root: Optional[str] = None) -> Tuple[Optional[str], Dict[str, Any]]:
    """
    Detect the appropriate context for a file path based on .pddrc configuration.

    This function finds the most specific matching context by comparing pattern lengths.
    For example, 'backend/functions/utils/**' is more specific than 'backend/**'.

    Args:
        file_path: Path to the file (can be absolute or relative)
        repo_root: Optional repository root path. If not provided, will be detected.

    Returns:
        Tuple of (context_name, context_config_defaults) or (None, {}) if no match.
    """
    # Find repo root if not provided
    if repo_root is None:
        try:
            import git
            repo = git.Repo(file_path, search_parent_directories=True)
            repo_root = repo.working_tree_dir
        except:
            repo_root = os.getcwd()

    # Make file_path relative to repo_root for matching
    file_path_abs = os.path.abspath(file_path)
    repo_root_abs = os.path.abspath(repo_root)

    if file_path_abs.startswith(repo_root_abs):
        relative_path = os.path.relpath(file_path_abs, repo_root_abs)
    else:
        relative_path = file_path

    # Find and load .pddrc
    pddrc_path = _find_pddrc_file(Path(repo_root))
    if not pddrc_path:
        return None, {}

    try:
        config = _load_pddrc_config(pddrc_path)
    except ValueError:
        return None, {}

    contexts = config.get('contexts', {})

    # Use shared helper with specificity matching for file-based detection
    context_name = _match_path_to_contexts(relative_path, contexts, use_specificity=True, is_absolute=False)
    return context_name, _get_context_config(config, context_name)


def _get_context_config(config: Dict[str, Any], context_name: Optional[str]) -> Dict[str, Any]:
    """Get configuration settings for the specified context."""
    if not context_name:
        return {}
    
    contexts = config.get('contexts', {})
    context_config = contexts.get(context_name, {})
    return context_config.get('defaults', {})

def _resolve_config_hierarchy(
    cli_options: Dict[str, Any],
    context_config: Dict[str, Any],
    env_vars: Dict[str, str]
) -> Dict[str, Any]:
    """Apply configuration hierarchy: CLI > context > environment > defaults."""
    resolved = {}
    
    # Configuration keys to resolve
    config_keys = {
        'generate_output_path': 'PDD_GENERATE_OUTPUT_PATH',
        'test_output_path': 'PDD_TEST_OUTPUT_PATH',
        'example_output_path': 'PDD_EXAMPLE_OUTPUT_PATH',
        'prompts_dir': 'PDD_PROMPTS_DIR',
        'default_language': 'PDD_DEFAULT_LANGUAGE',
        'target_coverage': 'PDD_TEST_COVERAGE_TARGET',
        'strength': None,
        'temperature': None,
        'budget': None,
        'max_attempts': None,
    }
    
    for config_key, env_var in config_keys.items():
        # 1. CLI options (highest priority)
        if config_key in cli_options and cli_options[config_key] is not None:
            resolved[config_key] = cli_options[config_key]
        # 2. Context configuration
        elif config_key in context_config:
            resolved[config_key] = context_config[config_key]
        # 3. Environment variables
        elif env_var and env_var in env_vars:
            resolved[config_key] = env_vars[env_var]
        # 4. Defaults are handled elsewhere
    
    return resolved


def get_tests_dir_from_config(start_path: Optional[Path] = None) -> Optional[Path]:
    """
    Get the tests directory from .pddrc configuration.

    Searches for .pddrc, detects the appropriate context, and returns the
    configured test_output_path as a Path object.

    Args:
        start_path: Starting directory for .pddrc search. Defaults to CWD.

    Returns:
        Path to tests directory if configured, None otherwise.
    """
    if start_path is None:
        start_path = Path.cwd()

    # Find and load .pddrc
    pddrc_path = _find_pddrc_file(start_path)
    if not pddrc_path:
        return None

    try:
        config = _load_pddrc_config(pddrc_path)
    except ValueError:
        return None

    # Detect context and get its config
    context_name = _detect_context(start_path, config)
    context_config = _get_context_config(config, context_name)

    # Check context config first, then env var
    test_output_path = context_config.get('test_output_path')
    if not test_output_path:
        test_output_path = os.environ.get('PDD_TEST_OUTPUT_PATH')

    if test_output_path:
        return Path(test_output_path)

    return None


def _read_file(path: Path) -> str:
    """Read a text file safely and return its contents."""
    try:
        return path.read_text(encoding="utf-8")
    except Exception as exc:  # pragma: no cover
        # Error is raised in the main function after this fails
        console.print(f"[error]Could not read {path}: {exc}", style="error")
        raise


def _ensure_error_file(path: Path, quiet: bool) -> None:
    """Create an empty error log file if it doesn't exist."""
    if not path.exists():
        if not quiet:
            # Use console.print from the main module scope
            # Print without Rich tags for easier testing
            console.print(f"Warning: Error file '{path.resolve()}' does not exist. Creating an empty file.", style="warning")
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.touch()
        except Exception as exc: # pragma: no cover
             console.print(f"[error]Could not create error file {path}: {exc}", style="error")
             raise


def _candidate_prompt_path(input_files: Dict[str, Path]) -> Path | None:
    """Return the path most likely to be the prompt file, if any."""
    # Prioritize specific keys known to hold the primary prompt
    for key in (
        "prompt_file",          # generate, test, fix, crash, trace, verify, auto-deps
        "input_prompt",         # split
        "input_prompt_file",    # update, change (non-csv), bug
        "prompt1",              # conflicts
        # Less common / potentially ambiguous keys last
        "change_prompt_file",   # change (specific case handled in _extract_basename)
    ):
        if key in input_files:
            return input_files[key]

    # Fallback: first file with a .prompt extension if no specific key matches
    for p in input_files.values():
        if p.suffix == ".prompt":
            return p
    
    # Final fallback: Return the first file path available (e.g. for pdd update <code_file>)
    if input_files:
        return next(iter(input_files.values()))
        
    return None


# New helper function to check if a language is known
def _is_known_language(language_name: str) -> bool:
    """Return True if the language is recognized.

    Prefer CSV in PDD_PATH if available; otherwise fall back to a built-in set
    so basename/language inference does not fail when PDD_PATH is unset.
    """
    language_name_lower = (language_name or "").lower()
    if not language_name_lower:
        return False

    builtin_languages = {
        'python', 'javascript', 'typescript', 'java', 'cpp', 'c', 'go', 'ruby', 'rust',
        'kotlin', 'swift', 'csharp', 'php', 'scala', 'r', 'lua', 'perl', 'bash', 'shell',
        'powershell', 'sql', 'prompt', 'html', 'css', 'makefile',
        # Common data and config formats for architecture prompts and configs
        'json', 'jsonl', 'yaml', 'yml', 'toml', 'ini'
    }

    pdd_path_str = os.getenv('PDD_PATH')
    if not pdd_path_str:
        return language_name_lower in builtin_languages

    csv_file_path = Path(pdd_path_str) / 'data' / 'language_format.csv'
    if not csv_file_path.is_file():
        return language_name_lower in builtin_languages

    try:
        with open(csv_file_path, mode='r', encoding='utf-8', newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                if row.get('language', '').lower() == language_name_lower:
                    return True
    except csv.Error as e:
        console.print(f"[error]CSV Error reading {csv_file_path}: {e}", style="error")
        return language_name_lower in builtin_languages

    return language_name_lower in builtin_languages


def _strip_language_suffix(path_like: os.PathLike[str]) -> str:
    """
    Remove trailing '_<language>' from a filename stem if it matches a known language.
    """
    p = Path(path_like)
    stem = p.stem  # removes last extension (e.g., '.prompt', '.py')

    if "_" not in stem:
        return stem

    parts = stem.split("_")
    candidate_lang = parts[-1]

    if _is_known_language(candidate_lang):
        # Do not strip '_prompt' from a non-.prompt file (e.g., 'test_prompt.txt')
        if candidate_lang == 'prompt' and p.suffix != '.prompt':
            return stem
        return "_".join(parts[:-1])
    
    return stem


def _extract_basename(
    command: str,
    input_file_paths: Dict[str, Path],
) -> str:
    """
    Deduce the project basename according to the rules explained in *Step A*.
    """
    # Handle 'fix' command specifically to create a unique basename per test file
    if command == "fix":
        prompt_path = _candidate_prompt_path(input_file_paths)
        if not prompt_path:
            raise ValueError("Could not determine prompt file for 'fix' command.")
        
        prompt_basename = _strip_language_suffix(prompt_path)
        
        unit_test_path = input_file_paths.get("unit_test_file")
        if not unit_test_path:
            # Fallback to just the prompt basename if no unit test file is provided
            # This might happen in some edge cases, but 'fix' command structure requires it
            return prompt_basename

        # Use the stem of the unit test file to make the basename unique
        test_basename = Path(unit_test_path).stem
        return f"{prompt_basename}_{test_basename}"
        
    # Handle conflicts first due to its unique structure
    if command == "conflicts":
        key1 = "prompt1"
        key2 = "prompt2"
        # Ensure keys exist before proceeding
        if key1 in input_file_paths and key2 in input_file_paths:
            p1 = Path(input_file_paths[key1])
            p2 = Path(input_file_paths[key2])
            base1 = _strip_language_suffix(p1)
            base2 = _strip_language_suffix(p2)
            # Combine basenames, ensure order for consistency (sorted)
            return "_".join(sorted([base1, base2]))
        # else: Fall through might occur if keys missing, handled by general logic/fallback

    # Special‑case commands that choose a non‑prompt file for the basename
    elif command == "detect":
        key = "change_file"
        if key in input_file_paths:
            # Basename is from change_file, no language suffix stripping needed usually
            return Path(input_file_paths[key]).stem
    elif command == "change":
         # If change_prompt_file is given, use its stem (no language strip needed per convention)
         if "change_prompt_file" in input_file_paths:
              return Path(input_file_paths["change_prompt_file"]).stem
         # If --csv is used or change_prompt_file is absent, fall through to general logic
         pass

    # General case: Use the primary prompt file
    prompt_path = _candidate_prompt_path(input_file_paths)
    if prompt_path:
        return _strip_language_suffix(prompt_path)

    # Fallback: If no prompt found (e.g., command only takes code files?),
    # use the first input file's stem. This requires input_file_paths not to be empty.
    # This fallback is reached only if input_file_paths is not empty (checked earlier)
    first_path = next(iter(input_file_paths.values()))
    # Should we strip language here too? Let's be consistent.
    return _strip_language_suffix(first_path)


def _determine_language(
    command_options: Dict[str, Any], # Keep original type hint
    input_file_paths: Dict[str, Path],
    command: str = "",  # New parameter for the command name
) -> str:
    """
    Apply the language discovery strategy.
    Priority: Explicit option > Code/Test file extension > Prompt filename suffix.
    For 'detect' command, default to 'prompt' as it typically doesn't need a language.
    """
    # Diagnostic check for None (should be handled by caller, but for safety)
    command_options = command_options or {}
    # 1 – explicit option
    explicit_lang = command_options.get("language")
    if explicit_lang:
        lang_lower = explicit_lang.lower()
        # Optional: Validate known language? Let's assume valid for now.
        return lang_lower

    # 2 – infer from extension of any code/test file (excluding .prompt)
    # Iterate through values, ensuring consistent order if needed (e.g., sort keys)
    # For now, rely on dict order (Python 3.7+)
    for key, p in input_file_paths.items():
        path_obj = Path(p)
        ext = path_obj.suffix
        # Prioritize non-prompt code files
        if ext and ext != ".prompt":
            try:
                language = get_language(ext)
                if language:
                    return language.lower()
            except ValueError:
                # Fallback: load language CSV file directly when PDD_PATH is not set
                try:
                    import csv
                    import os
                    # Try to find the CSV file relative to this script
                    script_dir = os.path.dirname(os.path.abspath(__file__))
                    csv_path = os.path.join(script_dir, 'data', 'language_format.csv')
                    if os.path.exists(csv_path):
                        with open(csv_path, 'r') as csvfile:
                            reader = csv.DictReader(csvfile)
                            for row in reader:
                                if row['extension'].lower() == ext.lower():
                                    return row['language'].lower()
                except (FileNotFoundError, csv.Error):
                    pass
        # Handle files without extension like Makefile
        elif not ext and path_obj.is_file(): # Check it's actually a file
            try:
                language = get_language(path_obj.name) # Check name (e.g., 'Makefile')
                if language:
                    return language.lower()
            except ValueError:
                # Fallback: load language CSV file directly for files without extension
                try:
                    import csv
                    import os
                    script_dir = os.path.dirname(os.path.abspath(__file__))
                    csv_path = os.path.join(script_dir, 'data', 'language_format.csv')
                    if os.path.exists(csv_path):
                        with open(csv_path, 'r') as csvfile:
                            reader = csv.DictReader(csvfile)
                            for row in reader:
                                # Check if the filename matches (for files without extension)
                                if not row['extension'] and path_obj.name.lower() == row['language'].lower():
                                    return row['language'].lower()
                except (FileNotFoundError, csv.Error):
                    pass

    # 3 – parse from prompt filename suffix
    prompt_path = _candidate_prompt_path(input_file_paths)
    if prompt_path and prompt_path.suffix == ".prompt":
        stem = prompt_path.stem
        if "_" in stem:
            parts = stem.split("_")
            if len(parts) >= 2:
                token = parts[-1]
                # Check if the token is a known language using the new helper
                if _is_known_language(token):
                    return token.lower()

    # 4 - Special handling for detect command - default to prompt for LLM prompts
    if command == "detect" and "change_file" in input_file_paths:
        return "prompt"

    # 5 - If no language determined, raise error
    raise ValueError("Could not determine language from input files or options.")


def _paths_exist(paths: Dict[str, Path]) -> bool: # Value type is Path
    """Return True if any of the given paths is an existing file."""
    # Check specifically for files, not directories
    return any(p.is_file() for p in paths.values())


def construct_paths(
    input_file_paths: Dict[str, str],
    force: bool,
    quiet: bool,
    command: str,
    command_options: Optional[Dict[str, Any]], # Allow None
    create_error_file: bool = True,  # Added parameter to control error file creation
    context_override: Optional[str] = None,  # Added parameter for context override
    confirm_callback: Optional[Callable[[str, str], bool]] = None,  # Callback for interactive confirmation
    path_resolution_mode: Optional[str] = None,  # "cwd" or "config_base" - if None, use command default
) -> Tuple[Dict[str, Any], Dict[str, str], Dict[str, str], str]:
    """
    High‑level orchestrator that loads inputs, determines basename/language,
    computes output locations, and verifies overwrite rules.
    
    Supports .pddrc configuration with context-aware settings and configuration hierarchy:
    CLI options > .pddrc context > environment variables > defaults

    Returns
    -------
    (resolved_config, input_strings, output_file_paths, language)
    """
    command_options = command_options or {} # Ensure command_options is a dict

    # ------------- Load .pddrc configuration -----------------
    pddrc_config = {}
    pddrc_path: Optional[Path] = None
    context = None
    context_config = {}
    original_context_config = {}  # Keep track of original context config for sync discovery
    
    try:
        # Find and load .pddrc file
        pddrc_path = _find_pddrc_file()
        if pddrc_path:
            pddrc_config = _load_pddrc_config(pddrc_path)
            
            # Detect appropriate context
            current_dir = Path.cwd()
            context = _detect_context(current_dir, pddrc_config, context_override)
            
            # Get context-specific configuration
            context_config = _get_context_config(pddrc_config, context)
            original_context_config = context_config.copy()  # Store original before modifications
            
            if not quiet and context:
                console.print(f"[info]Using .pddrc context:[/info] {context}")
        
        # Apply configuration hierarchy
        env_vars = dict(os.environ)
        resolved_config = _resolve_config_hierarchy(command_options, context_config, env_vars)
        
        # Update command_options with resolved configuration for internal use
        for key, value in resolved_config.items():
            if key not in command_options or command_options[key] is None:
                command_options[key] = value
        
        # Also update context_config with resolved environment variables for generate_output_paths
        # This ensures environment variables are available when context config doesn't override them
        for key, value in resolved_config.items():
            if key.endswith('_output_path') and key not in context_config:
                context_config[key] = value
                
    except Exception as e:
        error_msg = f"Configuration error: {e}"
        console.print(f"[error]{error_msg}[/error]", style="error")
        if not quiet:
            console.print("[warning]Continuing with default configuration...[/warning]", style="warning")
        # Initialize resolved_config on error to avoid downstream issues
        resolved_config = command_options.copy()


    # ------------- Handle sync discovery mode ----------------
    if command == "sync" and not input_file_paths:
        basename = command_options.get("basename")
        if not basename:
            raise ValueError("Basename must be provided in command_options for sync discovery mode.")
        
        # For discovery, we only need directory paths. Call generate_output_paths with dummy values.
        try:
            output_paths_str = generate_output_paths(
                command="sync",
                output_locations={},
                basename=basename,
                language="python", # Dummy language
                file_extension=".py", # Dummy extension
                context_config=context_config,
                config_base_dir=str(pddrc_path.parent) if pddrc_path else None,
                path_resolution_mode="cwd",  # Sync resolves paths relative to CWD
            )

            # Infer base directories from a sample output path
            gen_path = Path(output_paths_str.get("generate_output_path", "src"))
            
            # First, check current working directory for prompt files matching the basename pattern
            current_dir = Path.cwd()
            prompt_pattern = f"{basename}_*.prompt"
            if list(current_dir.glob(prompt_pattern)):
                # Found prompt files in current working directory
                resolved_config["prompts_dir"] = str(current_dir)
                resolved_config["code_dir"] = str(current_dir)
                if not quiet:
                    console.print(f"[info]Found prompt files in current directory:[/info] {current_dir}")
            else:
                # Fall back to context-aware logic
                # Use original_context_config to avoid checking augmented config with env vars
                if original_context_config and any(key.endswith('_output_path') for key in original_context_config):
                    # For configured contexts, use prompts_dir from config if provided,
                    # otherwise default to "prompts" at the same level as output dirs
                    resolved_config["prompts_dir"] = original_context_config.get("prompts_dir", "prompts")
                    resolved_config["code_dir"] = str(gen_path.parent)
                else:
                    # For default contexts, maintain relative relationship 
                    # e.g., if code goes to "pi.py", prompts should be at "prompts/" (siblings)
                    resolved_config["prompts_dir"] = str(gen_path.parent / "prompts")
                    resolved_config["code_dir"] = str(gen_path.parent)
            
            resolved_config["tests_dir"] = str(Path(output_paths_str.get("test_output_path", "tests")).parent)
            # example_output_path can be a directory (e.g., "context/") or a file path (e.g., "examples/foo.py")
            # If it ends with / or has no file extension, treat as directory; otherwise use parent
            example_path_str = output_paths_str.get("example_output_path", "examples")
            example_path = Path(example_path_str)
            if example_path_str.endswith('/') or '.' not in example_path.name:
                resolved_config["examples_dir"] = example_path_str.rstrip('/')
            else:
                resolved_config["examples_dir"] = str(example_path.parent)

        except Exception as e:
            console.print(f"[error]Failed to determine initial paths for sync: {e}", style="error")
            raise
        
        # Return early for discovery mode
        return resolved_config, {}, {}, ""


    if not input_file_paths:
        raise ValueError("No input files provided")


    # ------------- normalise & resolve Paths -----------------
    input_paths: Dict[str, Path] = {}
    for key, path_str in input_file_paths.items():
        try:
            path = Path(path_str).expanduser()
            # Resolve non-error files strictly first, but be more lenient for sync command
            if key != "error_file":
                 # For sync command, be more tolerant of non-existent files since we're just determining paths
                 if command == "sync":
                     input_paths[key] = path.resolve()
                 else:
                     # Let FileNotFoundError propagate naturally if path doesn't exist
                     resolved_path = path.resolve(strict=True)
                     input_paths[key] = resolved_path
            else:
                 # Resolve error file non-strictly, existence checked later
                 input_paths[key] = path.resolve()
        except FileNotFoundError as e:
             # Re-raise standard FileNotFoundError, tests will check path within it
             raise e
        except Exception as exc: # Catch other potential path errors like permission issues
            console.print(f"[error]Invalid path provided for {key}: '{path_str}' - {exc}", style="error")
            raise # Re-raise other exceptions


    # ------------- Step 1: load input files ------------------
    input_strings: Dict[str, str] = {}
    for key, path in input_paths.items():
        if key == "error_file":
            if create_error_file:
                _ensure_error_file(path, quiet) # Pass quiet flag
                # Ensure path exists before trying to read
                if not path.exists():
                     # _ensure_error_file should have created it, but check again
                     # If it still doesn't exist, something went wrong
                     raise FileNotFoundError(f"Error file '{path}' could not be created or found.")
            else:
                # When create_error_file is False, error out if the file doesn't exist
                if not path.exists():
                    raise FileNotFoundError(f"Error file '{path}' does not exist.")

        # Check existence again, especially for error_file which might have been created
        if not path.exists():
             # For sync command, be more tolerant of non-existent files since we're just determining paths
             if command == "sync":
                 # Skip reading content for non-existent files in sync mode
                 continue
             else:
                 # This case should ideally be caught by resolve(strict=True) earlier for non-error files
                 # Raise standard FileNotFoundError
                 raise FileNotFoundError(f"{path}")

        if path.is_file(): # Read only if it's a file
             try:
                 input_strings[key] = _read_file(path)
             except Exception as exc:
                 # Re-raise exceptions during reading
                 raise IOError(f"Failed to read input file '{path}' (key='{key}'): {exc}") from exc
        elif path.is_dir():
             # Decide how to handle directories if they are passed unexpectedly
             if not quiet:
                 console.print(f"[warning]Warning: Input path '{path}' for key '{key}' is a directory, not reading content.", style="warning")
             # Store the path string or skip? Let's skip for input_strings.
             # input_strings[key] = "" # Or None? Or skip? Skipping seems best.
        # Handle other path types? (symlinks are resolved by resolve())


    # ------------- Step 2: basename --------------------------
    try:
        # For sync, example, and test commands, prefer the basename from command_options if provided.
        # This preserves subdirectory paths like 'core/cloud' which would otherwise
        # be lost when extracting from the prompt file path.
        if command in ("sync", "example", "test") and command_options.get("basename"):
            basename = command_options["basename"]
        else:
            basename = _extract_basename(command, input_paths)
    except ValueError as exc:
         # Check if it's the specific error from the initial check (now done at start)
         # This try/except might not be needed if initial check is robust
         # Let's keep it simple for now and let initial check handle empty inputs
         console.print(f"[error]Unable to extract basename: {exc}", style="error")
         raise ValueError(f"Failed to determine basename: {exc}") from exc
    except Exception as exc: # Catch other exceptions like potential StopIteration
        console.print(f"[error]Unexpected error during basename extraction: {exc}", style="error")
        raise ValueError(f"Failed to determine basename: {exc}") from exc


    # ------------- Step 3: language & extension --------------
    try:
        # Pass the potentially updated command_options
        language = _determine_language(command_options, input_paths, command)
        
        # Add validation to ensure language is never None
        if language is None:
            # Set a default language based on command, defaulting to 'python' for most commands
            if command == 'bug':
                # The bug command typically defaults to python in bug_main.py
                language = 'python'
            else:
                # General fallback for other commands
                language = 'python'
            
            # Log the issue for debugging
            if not quiet:
                console.print(
                    f"[warning]Warning: Could not determine language for '{command}' command. Using default: {language}[/warning]",
                    style="warning"
                )
    except ValueError as e:
        console.print(f"[error]{e}", style="error")
        raise # Re-raise the ValueError from _determine_language

    # Final safety check before calling get_extension
    if not language or not isinstance(language, str):
        language = 'python'  # Absolute fallback
        if not quiet:
            console.print(
                f"[warning]Warning: Invalid language value. Using default: {language}[/warning]",
                style="warning"
            )

    
    # Try to get extension from CSV; fallback to built-in mapping if PDD_PATH/CSV unavailable
    try:
        file_extension = get_extension(language)  # Pass determined language
        if not file_extension and (language or '').lower() != 'prompt':
            raise ValueError('empty extension')
    except Exception:
        builtin_ext_map = {
            'python': '.py', 'javascript': '.js', 'typescript': '.ts', 'java': '.java',
            'cpp': '.cpp', 'c': '.c', 'go': '.go', 'ruby': '.rb', 'rust': '.rs',
            'kotlin': '.kt', 'swift': '.swift', 'csharp': '.cs', 'php': '.php',
            'scala': '.scala', 'r': '.r', 'lua': '.lua', 'perl': '.pl', 'bash': '.sh',
            'shell': '.sh', 'powershell': '.ps1', 'sql': '.sql', 'html': '.html', 'css': '.css',
            'prompt': '.prompt', 'makefile': '',
            # Common data/config formats
            'json': '.json', 'jsonl': '.jsonl', 'yaml': '.yaml', 'yml': '.yml', 'toml': '.toml', 'ini': '.ini'
        }
        file_extension = builtin_ext_map.get(language.lower(), f".{language.lower()}" if language else '')



    # ------------- Step 3b: build output paths ---------------
    # Filter user‑provided output_* locations from CLI options
    output_location_opts = {
        k: v for k, v in command_options.items()
        if k.startswith("output") and v is not None # Ensure value is not None
    }

    # Determine input file directory for default output path generation
    # Only apply for commands that generate/update files based on specific input files
    # Commands like sync, generate, test, example have their own directory management
    commands_using_input_dir = {'fix', 'crash', 'verify', 'split', 'change', 'update'}
    input_file_dir: Optional[str] = None
    input_file_dirs: Dict[str, Optional[str]] = {}
    if input_paths and command in commands_using_input_dir:
        try:
            # For fix/crash/verify commands, use specific file directories for each output
            if command in {'fix', 'crash', 'verify'}:
                # Map output keys to their corresponding input file keys
                input_key_map = {
                    'fix': {'output_code': 'code_file', 'output_test': 'unit_test_file', 'output_results': 'code_file'},
                    'crash': {'output': 'code_file', 'output_program': 'program_file'},
                    'verify': {'output_code': 'code_file', 'output_program': 'verification_program', 'output_results': 'code_file'},
                }

                for output_key, input_key in input_key_map.get(command, {}).items():
                    if input_key in input_paths:
                        input_file_dirs[output_key] = str(input_paths[input_key].parent)

                # Set default input_file_dir to code_file directory as fallback
                if 'code_file' in input_paths:
                    input_file_dir = str(input_paths['code_file'].parent)
                else:
                    first_input_path = next(iter(input_paths.values()))
                    input_file_dir = str(first_input_path.parent)
            else:
                # For other commands, use first input path
                first_input_path = next(iter(input_paths.values()))
                input_file_dir = str(first_input_path.parent)
        except (StopIteration, AttributeError):
            # If no input paths or path doesn't have parent, use None (falls back to CWD)
            pass

    try:
        # generate_output_paths might return Dict[str, str] or Dict[str, Path]
        # Let's assume it returns Dict[str, str] based on verification error,
        # and convert them to Path objects here.
        # Determine path resolution mode:
        # - If explicitly provided, use it
        # - Otherwise: sync uses "cwd", other commands use "config_base"
        effective_path_resolution_mode = path_resolution_mode
        if effective_path_resolution_mode is None:
            effective_path_resolution_mode = "cwd" if command == "sync" else "config_base"

        output_paths_str: Dict[str, str] = generate_output_paths(
            command=command,
            output_locations=output_location_opts,
            basename=basename,
            language=language,
            file_extension=file_extension,
            context_config=context_config,
            input_file_dir=input_file_dir,
            input_file_dirs=input_file_dirs,
            config_base_dir=str(pddrc_path.parent) if pddrc_path else None,
            path_resolution_mode=effective_path_resolution_mode,
        )

        # Convert to Path objects for internal use
        output_paths_resolved: Dict[str, Path] = {k: Path(v) for k, v in output_paths_str.items()}

    except ValueError as e: # Catch ValueError if generate_output_paths raises it
         console.print(f"[error]Error generating output paths: {e}", style="error")
         raise # Re-raise the ValueError

    # ------------- Step 4: overwrite confirmation ------------
    # Initialize existing_files before the conditional to avoid UnboundLocalError
    existing_files: Dict[str, Path] = {}

    if command in ["test", "bug"] and not force:
        # For test/bug commands without --force, create numbered files instead of overwriting
        for key, path in output_paths_resolved.items():
            if path.is_file():
                base, ext = os.path.splitext(path)
                i = 1
                new_path = Path(f"{base}_{i}{ext}")
                while new_path.exists():
                    i += 1
                    new_path = Path(f"{base}_{i}{ext}")
                output_paths_resolved[key] = new_path
    else:
        # Check if any output *file* exists (operate on Path objects)
        for k, p_obj in output_paths_resolved.items():
            if p_obj.is_file():
                existing_files[k] = p_obj # Store the Path object

    if existing_files and not force:
        paths_list = "\n".join(f"  • {p.resolve()}" for p in existing_files.values())
        if not quiet:
            # Use the Path objects stored in existing_files for resolve()
            # Print without Rich tags for easier testing
            console.print(
                f"Warning: The following output files already exist and may be overwritten:\n{paths_list}",
                style="warning"
            )

        # Use confirm_callback if provided (for TUI environments), otherwise use click.confirm
        if confirm_callback is not None:
            # Use the provided callback for confirmation (e.g., from Textual TUI)
            confirm_message = f"The following files will be overwritten:\n{paths_list}\n\nOverwrite existing files?"
            if not confirm_callback(confirm_message, "Overwrite Confirmation"):
                raise click.Abort()
        else:
            # Use click.confirm for CLI interaction
            try:
                if not click.confirm(
                    click.style("Overwrite existing files?", fg="yellow"), default=True, show_default=True
                ):
                    click.secho("Operation cancelled.", fg="red", err=True)
                    raise click.Abort()
            except click.Abort:
                raise  # Let Abort propagate to be handled by PDDCLI.invoke()
            except Exception as e: # Catch potential errors during confirm (like EOFError in non-interactive)
                if 'EOF' in str(e) or 'end-of-file' in str(e).lower():
                    # Non-interactive environment, default to not overwriting
                    click.secho("Non-interactive environment detected. Use --force to overwrite existing files.", fg="yellow", err=True)
                else:
                    click.secho(f"Confirmation failed: {e}. Aborting.", fg="red", err=True)
                raise click.Abort()


    # ------------- Final reporting ---------------------------
    if not quiet:
        console.print("[info]Input files:[/info]")
        # Print resolved input paths
        for k, p in input_paths.items():
            console.print(f"  [info]{k:<15}[/info] {p.resolve()}") # Use resolve() for consistent absolute paths
        console.print("[info]Output files:[/info]")
        # Print resolved output paths (using the Path objects)
        for k, p in output_paths_resolved.items():
            console.print(f"  [info]{k:<15}[/info] {p.resolve()}") # Use resolve()
        console.print(f"[info]Detected language:[/info] {language}")
        console.print(f"[info]Basename:[/info] {basename}")

    # Return output paths as strings, using the original dict from generate_output_paths
    # if it returned strings, or convert the Path dict back.
    # Since we converted to Path, convert back now.
    output_file_paths_str_return = {k: str(v) for k, v in output_paths_resolved.items()}

    # Add resolved paths to the config that gets returned
    resolved_config.update(output_file_paths_str_return)
    # Also add inferred directory paths
    gen_path = Path(resolved_config.get("generate_output_path", "src"))
    resolved_config["prompts_dir"] = str(next(iter(input_paths.values())).parent)
    resolved_config["code_dir"] = str(gen_path.parent)
    resolved_config["tests_dir"] = str(Path(resolved_config.get("test_output_path", "tests")).parent)
    # example_output_path can be a directory (e.g., "context/") or a file path (e.g., "examples/foo.py")
    # If it ends with / or has no file extension, treat as directory; otherwise use parent
    example_path_str = resolved_config.get("example_output_path", "examples")
    example_path = Path(example_path_str)
    if example_path_str.endswith('/') or '.' not in example_path.name:
        resolved_config["examples_dir"] = example_path_str.rstrip('/')
    else:
        resolved_config["examples_dir"] = str(example_path.parent)


    return resolved_config, input_strings, output_file_paths_str_return, language
