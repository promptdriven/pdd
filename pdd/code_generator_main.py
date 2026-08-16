import ast
import difflib
import glob
import logging
import os
import re
import json
import pathlib
import shlex
import subprocess
import requests
import tempfile
import sys
from typing import Optional, Tuple, Dict, Any, Iterator, List, Set, Mapping

import click
from rich.console import Console
from rich.panel import Panel
from rich.text import Text

# Relative imports for PDD package structure
from . import DEFAULT_STRENGTH, DEFAULT_TIME, EXTRACTION_STRENGTH # Assuming these are in __init__.py
from .config_resolution import resolve_effective_config
from .construct_paths import construct_paths
from .preprocess import preprocess as pdd_preprocess
from .code_generator import code_generator as local_code_generator_func
from .incremental_code_generator import incremental_code_generator as incremental_code_generator_func
from .core.cloud import CloudConfig, get_cloud_timeout, get_cloud_request_timeout
from .python_env_detector import detect_host_python_executable
from .architecture_sync import (
    get_architecture_entry_for_prompt,
    has_pdd_tags,
    generate_tags_from_architecture,
    parse_prompt_tags,
)
from .architecture_registry import extract_modules
from .architecture_include_validation import validate_prompt_contract_context
from .validate_prompt_includes import validate_prompt_includes
from .grounding_provenance import (
    build_grounding_metadata,
    grounding_reviewed_for_manifest,
    review_pinned_examples_before_generation,
    stash_grounding_overrides_on_ctx,
    warn_cloud_examples_not_preapproved,
)
from .compressed_sync_context import compressed_context_is_active, render_for_prompt
from .interface_semantics import (
    DefaultCompatibility,
    annotations_compatible,
    build_module_default_symbols,
    compare_default_sources,
    parse_callable_contract,
    signature_entries_compatible,
)

# Conformance gates live in ``pdd.conformance``; this module orchestrates them.
# The REDUNDANT ALIAS form is deliberate: a plain ``from ... import X`` is not
# public surface under this project's own rules and would read as a symbol
# removal to the very gate defined below (orchestrator R10).
from .conformance.gate_errors import (  # noqa: F401
    ArchitectureConformanceError as ArchitectureConformanceError,
    LanguageMismatchError as LanguageMismatchError,
    PROSE_OUTPUT_REPAIR_DIRECTIVE as PROSE_OUTPUT_REPAIR_DIRECTIVE,
    ProseOutputError as ProseOutputError,
    PublicSurfaceRegressionError as PublicSurfaceRegressionError,
    TestChurnError as TestChurnError,
    _CHURN_NONCE_CACHE as _CHURN_NONCE_CACHE,
    _CHURN_NONCE_ENV as _CHURN_NONCE_ENV,
    _CHURN_NONCE_READ as _CHURN_NONCE_READ,
    _LANGUAGE_TEST_FILE_EXTS as _LANGUAGE_TEST_FILE_EXTS,
    _read_churn_nonce as _read_churn_nonce,
    _verify_language_validity as _verify_language_validity,
)
from .conformance.directives import (  # noqa: F401
    _BREAKING_CHANGE_DIRECTIVE_RE as _BREAKING_CHANGE_DIRECTIVE_RE,
    _DIRECTIVE_SYMBOL_RE as _DIRECTIVE_SYMBOL_RE,
    _YAML_FRONT_MATTER_RE as _YAML_FRONT_MATTER_RE,
    _env_flag_enabled as _env_flag_enabled,
    _iter_breaking_change_directives as _iter_breaking_change_directives,
    _parse_breaking_change_symbols as _parse_breaking_change_symbols,
    _parse_llm_bool as _parse_llm_bool,
    _prompt_allows_breaking_change as _prompt_allows_breaking_change,
    _prompt_breaking_change_removed_symbols as _prompt_breaking_change_removed_symbols,
    _prompt_breaking_change_signature_symbols as _prompt_breaking_change_signature_symbols,
    _prompt_has_breaking_change_marker as _prompt_has_breaking_change_marker,
    _strip_yaml_front_matter as _strip_yaml_front_matter,
)
from .conformance.surface import (  # noqa: F401
    _COMPREHENSION_TYPES as _COMPREHENSION_TYPES,
    _DUNDER_ALL_MUTATOR_METHODS as _DUNDER_ALL_MUTATOR_METHODS,
    _SCOPE_NODE_TYPES as _SCOPE_NODE_TYPES,
    _assign_target_matches as _assign_target_matches,
    _class_constructor_signature as _class_constructor_signature,
    _clean_dunder_all_literal as _clean_dunder_all_literal,
    _collect_bound_module_names as _collect_bound_module_names,
    _collect_dataclass_inherited_parts as _collect_dataclass_inherited_parts,
    _collect_dataclass_own_parts as _collect_dataclass_own_parts,
    _collect_patch_targets as _collect_patch_targets,
    _collect_python_public_surface as _collect_python_public_surface,
    _dataclass_decorator_is_kw_only as _dataclass_decorator_is_kw_only,
    _dataclass_decorator_synthesizes_init as _dataclass_decorator_synthesizes_init,
    _dataclass_field_call_is_init_false as _dataclass_field_call_is_init_false,
    _diff_public_surface as _diff_public_surface,
    _effective_patch_targets as _effective_patch_targets,
    _extract_dunder_all as _extract_dunder_all,
    _format_python_signature as _format_python_signature,
    _is_dataclass_decorator as _is_dataclass_decorator,
    _is_kw_only_sentinel as _is_kw_only_sentinel,
    _node_writes_dunder_all as _node_writes_dunder_all,
    _part_field_name as _part_field_name,
    _patch_target_signature_entry as _patch_target_signature_entry,
    _python_method_binding_kind as _python_method_binding_kind,
    _python_property_accessor_role as _python_property_accessor_role,
    _reexport_binding as _reexport_binding,
    _resolve_class_node as _resolve_class_node,
    _scannable_children as _scannable_children,
    _snapshot_public_signatures as _snapshot_public_signatures,
    _snapshot_public_surface as _snapshot_public_surface,
    _subtree_mutates_dunder_all as _subtree_mutates_dunder_all,
    _symbol_exists_in_module as _symbol_exists_in_module,
    _synthesize_dataclass_init_signature as _synthesize_dataclass_init_signature,
)
from .conformance.test_churn import (  # noqa: F401
    _TEST_CHURN_BRIDGE_BREAK_RE as _TEST_CHURN_BRIDGE_BREAK_RE,
    _TEST_CHURN_OPT_OUT_RE as _TEST_CHURN_OPT_OUT_RE,
    _TEST_CHURN_TARGET_RE as _TEST_CHURN_TARGET_RE,
    _calculate_test_churn_ratio as _calculate_test_churn_ratio,
    _compute_test_churn_ratio as _compute_test_churn_ratio,
    _find_default_test_files as _find_default_test_files,
    _get_test_churn_threshold as _get_test_churn_threshold,
    _is_python_generation as _is_python_generation,
    _is_test_output_path as _is_test_output_path,
    _prompt_allows_test_churn as _prompt_allows_test_churn,
    _verify_test_churn as _verify_test_churn,
)
from .conformance.interface_check import (  # noqa: F401
    ParamSpec as ParamSpec,
    _ast_args_to_specs as _ast_args_to_specs,
    _collect_actual_param_specs as _collect_actual_param_specs,
    _collect_pdd_interface_names as _collect_pdd_interface_names,
    _collect_python_symbols as _collect_python_symbols,
    _extract_pdd_interface_signatures as _extract_pdd_interface_signatures,
    _find_target_function as _find_target_function,
    _parse_declared_param_specs as _parse_declared_param_specs,
    _verify_architecture_conformance as _verify_architecture_conformance,
    _verify_architecture_json_conformance as _verify_architecture_json_conformance,
    _verify_pdd_interface_signatures as _verify_pdd_interface_signatures,
)
from .conformance.declared_surface import (  # noqa: F401
    _annotation_only_edits as _annotation_only_edits,
    _apply_byte_edits as _apply_byte_edits,
    _collect_declared_surface as _collect_declared_surface,
    _declared_patch_targets as _declared_patch_targets,
    _declared_presence_name as _declared_presence_name,
    _declared_signature_to_entry as _declared_signature_to_entry,
    _entry_binding_context as _entry_binding_context,
    _index_function_defs as _index_function_defs,
    _line_start_byte_offsets as _line_start_byte_offsets,
    _node_byte_span as _node_byte_span,
    _parse_declared_def as _parse_declared_def,
    _reconcile_declared_annotation_drift as _reconcile_declared_annotation_drift,
    _signature_slots as _signature_slots,
    _verify_public_surface_regression as _verify_public_surface_regression,
)

console = Console()
logger = logging.getLogger(__name__)


def _should_wire_generated_exports(output_path: str) -> bool:
    """Return True when generated Python exports should be wired to __init__.py.

    Wiring mutates a sibling file, so the safe default is off. Users can opt in
    with PDD_ENABLE_WIRING=1; PDD_SKIP_WIRING remains a backward-compatible
    override for automation that already relies on it.
    """
    if not str(output_path).endswith('.py'):
        return False
    if _env_flag_enabled("PDD_SKIP_WIRING"):
        return False
    return _env_flag_enabled("PDD_ENABLE_WIRING")


def _find_prompt_contract_project_root(prompt_path: str, output_path: Optional[str]) -> pathlib.Path:
    """Find the project root used for prompt contract preflight resolution."""
    starts: List[pathlib.Path] = []
    try:
        starts.append(pathlib.Path(prompt_path).resolve().parent)
    except Exception:
        pass
    if output_path:
        try:
            starts.append(pathlib.Path(output_path).resolve().parent)
        except Exception:
            pass
    starts.append(pathlib.Path.cwd().resolve())

    seen: set[pathlib.Path] = set()
    for start in starts:
        if start in seen:
            continue
        seen.add(start)
        current = start
        while True:
            if (current / "architecture.json").exists():
                return current
            if current.parent == current:
                break
            current = current.parent

    try:
        current = pathlib.Path(prompt_path).resolve().parent
        while True:
            if current.name == "prompts":
                return current.parent
            if current.parent == current:
                break
            current = current.parent
    except Exception:
        pass

    return pathlib.Path.cwd().resolve()

# --- Git Helper Functions ---
def _run_git_command(command: List[str], cwd: Optional[str] = None) -> Tuple[int, str, str]:
    """Runs a git command and returns (return_code, stdout, stderr)."""
    try:
        process = subprocess.run(command, capture_output=True, text=True, check=False, cwd=cwd, encoding='utf-8')
        return process.returncode, process.stdout.strip(), process.stderr.strip()
    except FileNotFoundError:
        return -1, "", "Git command not found. Ensure git is installed and in your PATH."
    except Exception as e:
        return -2, "", f"Error running git command {' '.join(command)}: {e}"

def is_git_repository(path: Optional[str] = None) -> bool:
    """Checks if the given path (or current dir) is a git repository."""
    start_path = pathlib.Path(path).resolve() if path else pathlib.Path.cwd()
    # Check for .git in current or any parent directory
    current_path = start_path
    while True:
        if (current_path / ".git").is_dir():
            # Verify it's the root of the work tree or inside it
            returncode, stdout, _ = _run_git_command(["git", "rev-parse", "--is-inside-work-tree"], cwd=str(start_path))
            return returncode == 0 and stdout == "true"
        parent = current_path.parent
        if parent == current_path: # Reached root directory
            break
        current_path = parent
    return False


def _expand_vars(text: str, vars_map: Optional[Dict[str, str]]) -> str:
    """Replace $KEY and ${KEY} in text when KEY exists in vars_map. Leave others unchanged."""
    if not text or not vars_map:
        return text

    def repl_braced(m: re.Match) -> str:
        key = m.group(1)
        return vars_map.get(key, m.group(0))

    def repl_simple(m: re.Match) -> str:
        key = m.group(1)
        return vars_map.get(key, m.group(0))

    # Replace ${KEY} first, then $KEY
    text = re.sub(r"\$\{([A-Za-z_][A-Za-z0-9_]*)\}", repl_braced, text)
    text = re.sub(r"\$([A-Za-z_][A-Za-z0-9_]*)", repl_simple, text)
    return text


def _parse_front_matter(text: str) -> Tuple[Optional[Dict[str, Any]], str]:
    """Parse YAML front matter at the start of a prompt and return (meta, body).

    Accepts LF, CRLF, or mixed line endings and a leading UTF-8 BOM (#1276) —
    Windows editors frequently save prompts with CRLF and/or BOM, either of
    which the previous string-prefix check rejected. Trailing whitespace on
    the fence lines is tolerated to match ``template_registry._parse_front_matter``.

    Only the malformed-YAML path is logged — that condition requires BOTH
    fences to be present, so it is unambiguous user intent. The unclosed-fence
    case is silent because ``---\\nProse...`` is also a valid markdown
    horizontal rule and we cannot distinguish "intended front matter, forgot
    to close" from "markdown HR" without false positives.
    """
    # Strip a leading UTF-8 BOM (U+FEFF) if present — Windows editors that
    # save as UTF-8-with-BOM would otherwise make the anchor fail silently.
    if text.startswith("﻿"):
        text = text[1:]
    m = re.match(r"^---[ \t]*\r?\n(.*?)\r?\n---[ \t]*(?:\r?\n|\Z)", text, re.DOTALL)
    if not m:
        return None, text
    fm_body = m.group(1)
    rest = text[m.end():]
    import yaml as _yaml
    try:
        meta = _yaml.safe_load(fm_body) or {}
    except _yaml.YAMLError as exc:
        logger.warning(
            "Failed to parse YAML front matter: %s. Treating entire prompt as body.",
            exc,
        )
        return None, text
    if not isinstance(meta, dict):
        meta = {}
    return meta, rest


def _is_architecture_template(meta: Optional[Dict[str, Any]]) -> bool:
    """Detect the packaged architecture JSON template via its front matter name."""
    return isinstance(meta, dict) and meta.get("name") == "architecture/architecture_json"


def _repair_architecture_interface_types(payload: Any) -> Tuple[Any, bool]:
    """
    Patch common LLM slip-ups for the architecture template where interface.type
    occasionally returns an unsupported value like "object". Only normalizes the
    interface.type field and leaves other schema issues untouched so validation
    still fails for genuinely malformed outputs.
    """
    allowed_types = {
        "component",
        "page",
        "module",
        "api",
        "graphql",
        "cli",
        "job",
        "message",
        "config",
        "entrypoint",
    }
    changed = False
    if not isinstance(payload, list):
        return payload, changed

    for entry in payload:
        if not isinstance(entry, dict):
            continue
        interface = entry.get("interface")
        if not isinstance(interface, dict):
            continue
        raw_type = interface.get("type")
        normalized = raw_type.lower() if isinstance(raw_type, str) else None
        if normalized in allowed_types:
            if normalized != raw_type:
                interface["type"] = normalized
                changed = True
            continue

        inferred_type = None
        for key in (
            "page",
            "component",
            "module",
            "api",
            "graphql",
            "cli",
            "job",
            "message",
            "config",
            "entrypoint",
        ):
            if isinstance(interface.get(key), dict):
                inferred_type = key
                break
        if inferred_type is None:
            inferred_type = "module"

        if raw_type != inferred_type:
            interface["type"] = inferred_type
            changed = True

    return payload, changed


def _parse_declared_param_names(signature: str) -> Optional[List[str]]:
    """Parse a ``(arg, arg2=default, ...)`` signature string into parameter names.

    Returns the ordered list of parameter names (positional-only, positional,
    keyword-only) — variadic ``*args``/``**kwargs`` are intentionally excluded
    because a variadic catch-all does not satisfy a contract that declares a
    specific named parameter (a caller passing ``sync_metadata=False`` expects
    the callee to have that name in its signature).

    Returns ``None`` if the signature is not a parseable paren-list (e.g. a
    class header like ``class Foo(BaseModel)``); the caller should skip the
    signature check in that case.
    """
    if not signature or not isinstance(signature, str):
        return None
    sig = signature.strip()
    # Real architecture entries sometimes use class headers as "signatures"
    # (e.g. ``class Order(BaseModel)``). Only treat strings that start with
    # ``(`` as parameter lists.
    if not sig.startswith("("):
        return None
    try:
        tree = ast.parse(f"def _f{sig}: pass")
    except SyntaxError:
        return None
    fn = tree.body[0]
    if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    args = fn.args
    names: List[str] = []
    names.extend(a.arg for a in args.posonlyargs)
    names.extend(a.arg for a in args.args)
    names.extend(a.arg for a in args.kwonlyargs)
    return names


def _collect_actual_param_names(func_node: ast.AST) -> List[str]:
    """Return positional + keyword-only parameter names for a FunctionDef-like AST node.

    ``*args`` and ``**kwargs`` are deliberately excluded: a variadic catch-all
    does not satisfy a declared named parameter for conformance purposes.
    """
    if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return []
    args = func_node.args
    names: List[str] = []
    names.extend(a.arg for a in args.posonlyargs)
    names.extend(a.arg for a in args.args)
    names.extend(a.arg for a in args.kwonlyargs)
    return names


def get_git_content_at_ref(file_path: str, git_ref: str = "HEAD") -> Optional[str]:
    """Gets the content of the file as it was at the specified git_ref."""
    abs_file_path = pathlib.Path(file_path).resolve()
    if not is_git_repository(str(abs_file_path.parent)):
        return None
    
    returncode_rev, git_root_str, stderr_rev = _run_git_command(["git", "rev-parse", "--show-toplevel"], cwd=str(abs_file_path.parent))
    if returncode_rev != 0:
        # console.print(f"[yellow]Git (rev-parse) warning for {file_path}: {stderr_rev}[/yellow]")
        return None
    
    git_root = pathlib.Path(git_root_str)
    try:
        relative_path = abs_file_path.relative_to(git_root)
    except ValueError:
        # console.print(f"[yellow]File {file_path} is not under git root {git_root}.[/yellow]")
        return None

    returncode, stdout, stderr = _run_git_command(["git", "show", f"{git_ref}:{relative_path.as_posix()}"], cwd=str(git_root))
    if returncode == 0:
        return stdout
    else:
        # File might not exist at that ref, or other git error.
        # if "does not exist" not in stderr and "exists on disk, but not in" not in stderr and console.is_terminal: # Be less noisy for common cases
        #     console.print(f"[yellow]Git (show) warning for {file_path} at {git_ref}: {stderr}[/yellow]")
        return None

def get_file_git_status(file_path: str) -> str:
    """Gets the git status of a single file (e.g., ' M', '??', 'A '). Empty if clean."""
    abs_file_path = pathlib.Path(file_path).resolve()
    if not is_git_repository(str(abs_file_path.parent)) or not abs_file_path.exists():
        return ""
    returncode, stdout, _ = _run_git_command(["git", "status", "--porcelain", str(abs_file_path)], cwd=str(abs_file_path.parent))
    if returncode == 0:
        # stdout might be " M path/to/file" or "?? path/to/file"
        # We only want the status codes part
        status_part = stdout.split(str(abs_file_path.name))[0].strip() if str(abs_file_path.name) in stdout else stdout.strip()
        return status_part
    return ""

def git_add_files(file_paths: List[str], verbose: bool = False) -> bool:
    """Stages the given files using 'git add'."""
    if not file_paths:
        return True
    
    # Resolve paths and ensure they are absolute for git command
    abs_paths = [str(pathlib.Path(fp).resolve()) for fp in file_paths]
    
    # Determine common parent directory to run git command from, or git root
    # For simplicity, assume they are in the same repo and run from one of their parents
    if not is_git_repository(str(pathlib.Path(abs_paths[0]).parent)):
        if verbose:
            console.print(f"[yellow]Cannot stage files: {abs_paths[0]} is not in a git repository.[/yellow]")
        return False
        
    returncode, _, stderr = _run_git_command(["git", "add"] + abs_paths, cwd=str(pathlib.Path(abs_paths[0]).parent))
    if returncode == 0:
        if verbose:
            console.print(f"Successfully staged: [cyan]{', '.join(abs_paths)}[/cyan]")
        return True
    else:
        console.print(f"[red]Error staging files with git:[/red] {stderr}")
        return False
# --- End Git Helper Functions ---


def _detect_wireable_exports(code: str, file_path: str) -> list[str]:
    """Extract public function/class names from generated Python code."""
    if not file_path.endswith('.py'):
        return []
    try:
        tree = ast.parse(code)
        exports: list[str] = []
        for node in ast.iter_child_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if not node.name.startswith('_'):
                    exports.append(node.name)
            elif isinstance(node, ast.ClassDef):
                if not node.name.startswith('_'):
                    exports.append(node.name)
        return exports
    except SyntaxError:
        return []


def _wire_to_parent_init(output_path: str, exports: list[str], verbose: bool = False) -> bool:
    """Add import line for generated module to parent __init__.py if it exists.

    If an import line for this module already exists, merge any missing exports
    into that line instead of skipping wiring.
    """
    output_p = pathlib.Path(output_path)
    init_path = output_p.parent / '__init__.py'
    if not init_path.exists():
        return False
    module_name = output_p.stem
    existing = init_path.read_text(encoding='utf-8')

    # Look for an existing "from .{module_name} import ..." line
    pattern = rf"^from \.{re.escape(module_name)} import (.+)$"
    match = re.search(pattern, existing, flags=re.MULTILINE)

    if match:
        # Parse existing names and merge with new exports
        existing_names = [
            name.strip()
            for name in match.group(1).split(",")
            if name.strip()
        ]
        updated = False
        for name in exports:
            if name not in existing_names:
                existing_names.append(name)
                updated = True

        if not updated:
            return False

        import_line = f"from .{module_name} import {', '.join(existing_names)}"
        new_content = (
            existing[: match.start()]
            + import_line
            + existing[match.end():]
        )
    else:
        import_line = f"from .{module_name} import {', '.join(exports)}"
        new_content = existing.rstrip() + '\n' + import_line + '\n'

    init_path.write_text(new_content, encoding='utf-8')
    if verbose:
        console.print(f"[info]Wired exports to {init_path}: {import_line}[/info]")
    return True


def code_generator_main(
    ctx: click.Context,
    prompt_file: str,
    output: Optional[str],
    original_prompt_file_path: Optional[str],
    force_incremental_flag: bool,
    env_vars: Optional[Dict[str, str]] = None,
    unit_test_file: Optional[str] = None,
    exclude_tests: bool = False,
    language: Optional[str] = None,
    output_from_config: bool = False,
    compress: bool = False,
    snapshot_context: bool = False,
    compressed_context: Optional[Mapping[str, Any]] = None,
) -> Tuple[str, bool, float, str]:
    """
    CLI wrapper for generating code from prompts. Handles full and incremental generation,
    local vs. cloud execution, and output.

    Args:
        ctx: Click context carrying CLI flags (strength, temperature, verbose, force, etc.).
        prompt_file: Path to the .prompt file to generate from.
        output: Resolved output path. ``None`` means no caller-supplied path; the
            front-matter ``output:`` (or .pddrc default) will be used instead.
        original_prompt_file_path: Optional pinned reference for incremental diff.
        force_incremental_flag: Force incremental generation when possible.
        env_vars: Extra environment variables for template expansion.
        unit_test_file: Optional unit test path used by the cloud generator.
        exclude_tests: Whether to skip tests in the cloud payload.
        language: Optional explicit target language override.
        output_from_config: ``True`` when ``output`` was derived from
            ``.pddrc`` (``generate_output_path``) rather than an explicit
            ``--output`` CLI flag. When ``True``, a front-matter ``output:``
            value (if present) takes precedence over the .pddrc default.
            When ``False`` (CLI flag), the explicit path always wins. This
            preserves the documented precedence: CLI > front-matter > .pddrc.
            Defaults to ``False`` so existing callers stay backward compatible.
        snapshot_context: When True, persist a replayable context snapshot for
            the expanded prompt used by this generation.

    Returns:
        Tuple of (generated_code, was_incremental, total_cost, model_name).
    """
    cli_params = ctx.obj or {}
    is_local_execution_preferred = cli_params.get('local', False)
    strength = cli_params.get('strength', DEFAULT_STRENGTH)
    temperature = cli_params.get('temperature', 0.0)
    time_budget = cli_params.get('time', DEFAULT_TIME)
    verbose = cli_params.get('verbose', False)
    force_overwrite = cli_params.get('force', False)
    quiet = cli_params.get('quiet', False)

    generated_code_content: Optional[str] = None
    was_incremental_operation = False
    total_cost = 0.0
    model_name = "unknown"
    snapshot_recorder = None
    snapshot_expanded_prompt: Optional[str] = None
    current_execution_is_local = is_local_execution_preferred

    input_file_paths_dict: Dict[str, str] = {"prompt_file": prompt_file}
    if original_prompt_file_path:
        input_file_paths_dict["original_prompt_file"] = original_prompt_file_path
    
    command_options: Dict[str, Any] = {"output": output}
    if language:
        command_options["language"] = language

    try:
        # Read prompt content once to determine LLM state and for construct_paths
        with open(prompt_file, 'r', encoding='utf-8') as f:
            raw_prompt_content = f.read()
        
        # Phase-2 templates: parse front matter metadata
        fm_meta, body = _parse_front_matter(raw_prompt_content)
        if fm_meta:
            prompt_content = body
        else:
            prompt_content = raw_prompt_content

        if isinstance(ctx.obj, dict):
            stash_grounding_overrides_on_ctx(ctx.obj, prompt_content)

        if snapshot_context:
            from .context_snapshot import start_snapshot_run

            snapshot_recorder = start_snapshot_run(prompt_file, command="pdd generate")
            snapshot_recorder.record_prompt_source(prompt_content)

        # Determine LLM state early to avoid unnecessary overwrite prompts
        llm_enabled: bool = True
        env_llm_raw = None
        try:
            if env_vars and 'llm' in env_vars:
                env_llm_raw = str(env_vars.get('llm'))
            elif os.environ.get('llm') is not None:
                env_llm_raw = os.environ.get('llm')
            elif os.environ.get('LLM') is not None:
                env_llm_raw = os.environ.get('LLM')
        except Exception:
            env_llm_raw = None

        # Environment variables should override front matter
        if env_llm_raw is not None:
            llm_enabled = _parse_llm_bool(env_llm_raw)
        elif fm_meta and isinstance(fm_meta, dict) and 'llm' in fm_meta:
            llm_enabled = bool(fm_meta.get('llm', True))
        # else: keep default True
        
        # If LLM is disabled, we're only doing post-processing, so skip overwrite confirmation
        effective_force = force_overwrite or not llm_enabled
        
        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths_dict,
            force=effective_force,
            quiet=quiet,
            command="generate",
            command_options=command_options,
            context_override=ctx.obj.get('context'),
            confirm_callback=cli_params.get('confirm_callback')
        )
        resolve_effective_config(ctx, resolved_config)
        # Determine final output path: if user passed a directory, use resolved file path
        resolved_output = output_file_paths.get("output")
        if output is None:
            output_path = resolved_output
        else:
            try:
                is_dir_hint = output.endswith(os.path.sep) or output.endswith("/")
            except Exception:
                is_dir_hint = False
            if is_dir_hint or os.path.isdir(output):
                output_path = resolved_output
            else:
                output_path = output

        # --- Unit Test Inclusion Logic ---
        # When compressed sync context is active, tests are supplied via the
        # bounded package instead of full <unit_test_content> expansion (#878).
        test_files_to_include: List[str] = []
        if not compressed_context_is_active(compressed_context):
            if unit_test_file:
                test_files_to_include.append(unit_test_file)
            elif not exclude_tests:
                tests_dir = resolved_config.get("tests_dir")
                found_tests = _find_default_test_files(tests_dir, output_path)
                if found_tests:
                    if verbose:
                        console.print(f"[info]Found default test files: {', '.join(found_tests)}[/info]")
                    test_files_to_include.extend(found_tests)

        if test_files_to_include:
            prompt_content += "\n\n<unit_test_content>\n"
            prompt_content += (
                "Study these test files carefully before generating code. "
                "Pay special attention to:\n"
                "- What specific types and data structures the assertions reveal "
                "(e.g., if a test asserts `x == (1.0, 2.0)`, the value is a tuple, not a dict)\n"
                "- What mock patterns show about the real interfaces being called "
                "(e.g., `mock_config.get_jwt_token.return_value` reveals the auth API)\n"
                "- What import paths are used for internal modules\n"
                "- What fixture setup reveals about expected data formats "
                "(e.g., DataFrame column names, namedtuple fields)\n\n"
                "The generated code must pass these tests, but also match the "
                "implementation patterns they imply.\n"
            )
            for tf in test_files_to_include:
                try:
                    with open(tf, 'r', encoding='utf-8') as f:
                        content = f.read()
                    prompt_content += f"\nFile: {pathlib.Path(tf).name}\n```python\n{content}\n```\n"
                except Exception as e:
                    console.print(f"[yellow]Warning: Could not read unit test file {tf}: {e}[/yellow]")
            prompt_content += "</unit_test_content>\n"
        # ---------------------------------

        # Architecture-conformance repair directive (set by retrying callers
        # such as agentic_sync_runner / sync_main when a prior generation
        # failed conformance). Append to the prompt so the model sees the
        # missing-export instruction on the next attempt. Without this, the
        # subprocess retry would be an identical generation request and the
        # repair loop would not actually repair anything (#866).
        repair_directive_env = os.environ.get("PDD_REPAIR_DIRECTIVE")
        if repair_directive_env and repair_directive_env.strip():
            prompt_content += (
                "\n\n<architecture_repair_directive>\n"
                f"{repair_directive_env.strip()}\n"
                "</architecture_repair_directive>\n"
            )
        rendered_compressed_context = render_for_prompt(compressed_context)
        if rendered_compressed_context:
            prompt_content += "\n\n" + rendered_compressed_context

    except FileNotFoundError as e:
        console.print(f"[red]Error: Input file not found: {e.filename}[/red]")
        return "", False, 0.0, "error"
    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        console.print(f"[red]Error during path construction: {e}[/red]")
        return "", False, 0.0, "error"

    can_attempt_incremental = False
    existing_code_content: Optional[str] = None
    original_prompt_content_for_incremental: Optional[str] = None

    # Merge -e vars with front-matter defaults; validate required
    if env_vars is None:
        env_vars = {}
    explicit_env_keys = set(env_vars.keys())  # Track which vars came from explicit -e
    if fm_meta and isinstance(fm_meta.get("variables"), dict):
        for k, spec in (fm_meta["variables"].items()):
            if isinstance(spec, dict):
                if k not in env_vars and "default" in spec:
                    env_vars[k] = str(spec["default"])
            # if scalar default allowed, ignore for now
        missing = [k for k, spec in fm_meta["variables"].items() if isinstance(spec, dict) and spec.get("required") and k not in env_vars]
        if missing:
            console.print(f"[error]Missing required variables: {', '.join(missing)}")
            return "", False, 0.0, "error"

    # Execute optional discovery from front matter to populate env_vars without overriding explicit -e values
    def _run_discovery(discover_cfg: Dict[str, Any]) -> Dict[str, str]:
        results: Dict[str, str] = {}
        try:
            if not discover_cfg:
                return results
            enabled = discover_cfg.get("enabled", False)
            if not enabled:
                return results
            root = discover_cfg.get("root", ".")
            patterns = discover_cfg.get("patterns", []) or []
            exclude = discover_cfg.get("exclude", []) or []
            max_per = int(discover_cfg.get("max_per_pattern", 0) or 0)
            max_total = int(discover_cfg.get("max_total", 0) or 0)
            root_path = pathlib.Path(root).resolve()
            seen: List[str] = []
            def _match_one(patterns_list: List[str]) -> List[str]:
                matches: List[str] = []
                for pat in patterns_list:
                    globbed = list(root_path.rglob(pat))
                    for p in globbed:
                        if any(p.match(ex) for ex in exclude):
                            continue
                        sp = str(p.resolve())
                        if sp not in matches:
                            matches.append(sp)
                    if max_per and len(matches) >= max_per:
                        matches = matches[:max_per]
                        break
                return matches
            # If a mapping 'set' is provided, compute per-variable results
            set_map = discover_cfg.get("set") or {}
            if isinstance(set_map, dict) and set_map:
                for var_name, spec in set_map.items():
                    if var_name in env_vars:
                        continue  # don't override explicit -e
                    v_patterns = spec.get("patterns", []) if isinstance(spec, dict) else []
                    v_exclude = spec.get("exclude", []) if isinstance(spec, dict) else []
                    save_exclude = exclude
                    try:
                        if v_exclude:
                            exclude = v_exclude
                        matches = _match_one(v_patterns or patterns)
                    finally:
                        exclude = save_exclude
                    if matches:
                        results[var_name] = ",".join(matches)
                        seen.extend(matches)
            # Fallback: populate SCAN_FILES and SCAN metadata
            if not results:
                files = _match_one(patterns)
                if max_total and len(files) > max_total:
                    files = files[:max_total]
                if files:
                    results["SCAN_FILES"] = ",".join(files)
            # Always set root/patterns helpers
            if root:
                results.setdefault("SCAN_ROOT", str(root_path))
            if patterns:
                results.setdefault("SCAN_PATTERNS", ",".join(patterns))
        except Exception as e:
            if verbose and not quiet:
                console.print(f"[yellow]Discovery skipped due to error: {e}[/yellow]")
        return results

    if fm_meta and isinstance(fm_meta.get("discover"), dict):
        discovered = _run_discovery(fm_meta.get("discover") or {})
        for k, v in discovered.items():
            if k not in env_vars:
                env_vars[k] = v

    # Inject EXAMPLE_OUTPUT_PATH for templates that reference ${EXAMPLE_OUTPUT_PATH}.
    # Precedence: explicit -e > resolved_config['example_output_path'] (#687)
    # > resolved_config['examples_dir'] (the SSOT helper's value, covering
    # greenfield + legacy context/ projects, #616) > template front-matter default.
    if "EXAMPLE_OUTPUT_PATH" not in explicit_env_keys and resolved_config:
        eop = resolved_config.get("example_output_path")
        if eop:
            env_vars["EXAMPLE_OUTPUT_PATH"] = str(eop).rstrip("/\\")
        elif resolved_config.get("examples_dir"):
            env_vars["EXAMPLE_OUTPUT_PATH"] = str(resolved_config["examples_dir"]).rstrip("/\\")

    # Expand variables in output path if provided
    if output_path:
        output_path = _expand_vars(output_path, env_vars)

    # Honor front-matter output when no explicit --output CLI flag was passed.
    # Front-matter overrides .pddrc generate_output_path (config default) but
    # NOT an explicit CLI --output flag. Precedence: CLI > front-matter > .pddrc.
    if (output is None or output_from_config) and fm_meta and isinstance(fm_meta.get("output"), str):
        try:
            meta_out = _expand_vars(fm_meta["output"], env_vars)
            if meta_out:
                output_path = str(pathlib.Path(meta_out).resolve())
        except Exception as fm_output_err:
            # Resolving the front-matter `output:` failed (bad path,
            # permission error, broken expansion, etc.). Fall back to the
            # caller-supplied path, but warn loudly so users notice — silent
            # fallback writes code to the wrong location.
            if not quiet:
                console.print(
                    f"[yellow]Warning: Could not resolve front-matter output path "
                    f"'{fm_meta.get('output')}': {fm_output_err}. "
                    f"Falling back to default output path.[/yellow]"
                )

    # Honor front-matter language if provided (overrides detection for both local and cloud)
    if fm_meta and isinstance(fm_meta.get("language"), str) and fm_meta.get("language"):
        language = fm_meta.get("language")

    if (
        llm_enabled
        and output_path
        and not _env_flag_enabled("PDD_SKIP_PROMPT_CONTRACT_PREFLIGHT")
    ):
        contract_root = _find_prompt_contract_project_root(prompt_file, output_path)
        contract_arch_path = contract_root / "architecture.json"
        contract_errors = validate_prompt_contract_context(
            prompt_path=pathlib.Path(prompt_file),
            output_path=pathlib.Path(output_path),
            project_root=contract_root,
            architecture_path=contract_arch_path if contract_arch_path.exists() else None,
            prompt_content=prompt_content,
        )
        if contract_errors:
            raise click.UsageError(
                "Prompt contract preflight failed:\n- " + "\n- ".join(contract_errors)
            )

    if output_path and pathlib.Path(output_path).exists():
        try:
            existing_code_content = pathlib.Path(output_path).read_text(encoding="utf-8")
        except Exception as e:
            console.print(f"[yellow]Warning: Could not read existing output file {output_path}: {e}[/yellow]")
            existing_code_content = None

        # Treat empty/whitespace-only files as absent — no code to incrementally patch
        if existing_code_content is not None and not existing_code_content.strip():
            existing_code_content = None

        if existing_code_content is not None:
            if "original_prompt_file" in input_strings:
                original_prompt_content_for_incremental = input_strings["original_prompt_file"]
                can_attempt_incremental = True
                if verbose:
                    console.print(f"Using specified original prompt: [cyan]{original_prompt_file_path}[/cyan]")
            elif is_git_repository(str(pathlib.Path(prompt_file).parent)):
                # prompt_content is the current on-disk version
                head_prompt_content = get_git_content_at_ref(prompt_file, git_ref="HEAD")

                if head_prompt_content is not None:
                    # Compare on-disk content (prompt_content) with HEAD content
                    if prompt_content.strip() != head_prompt_content.strip():
                        # Uncommitted changes exist. Original is HEAD, new is on-disk.
                        original_prompt_content_for_incremental = head_prompt_content
                        can_attempt_incremental = True
                        if verbose:
                            console.print(f"On-disk [cyan]{prompt_file}[/cyan] has uncommitted changes. Using HEAD version as original prompt.")
                    else:
                        # On-disk is identical to HEAD. Search for a prior *different* version.
                        if verbose:
                            console.print(f"On-disk [cyan]{prompt_file}[/cyan] matches HEAD. Searching for a prior *different* version as original prompt.")

                        new_prompt_candidate = head_prompt_content # This is also prompt_content (on-disk)
                        found_different_prior = False
                        
                        git_root_path_obj: Optional[pathlib.Path] = None
                        prompt_file_rel_to_root_str: Optional[str] = None

                        try:
                            abs_prompt_file_path = pathlib.Path(prompt_file).resolve()
                            temp_git_root_rc, temp_git_root_str, temp_git_root_stderr = _run_git_command(
                                ["git", "rev-parse", "--show-toplevel"], 
                                cwd=str(abs_prompt_file_path.parent)
                            )
                            if temp_git_root_rc == 0:
                                git_root_path_obj = pathlib.Path(temp_git_root_str)
                                prompt_file_rel_to_root_str = abs_prompt_file_path.relative_to(git_root_path_obj).as_posix()
                            elif verbose:
                                console.print(f"[yellow]Git (rev-parse) failed for {prompt_file}: {temp_git_root_stderr}. Cannot search history for prior different version.[/yellow]")
                        
                        except ValueError: # If file is not under git root
                             if verbose:
                                console.print(f"[yellow]File {prompt_file} not under a detected git root. Cannot search history.[/yellow]")
                        except Exception as e_git_setup:
                            if verbose:
                                console.print(f"[yellow]Error setting up git info for {prompt_file}: {e_git_setup}. Cannot search history.[/yellow]")

                        if git_root_path_obj and prompt_file_rel_to_root_str:
                            MAX_COMMITS_TO_SEARCH = 10  # How far back to look
                            log_cmd = ["git", "log", f"--pretty=format:%H", f"-n{MAX_COMMITS_TO_SEARCH}", "--", prompt_file_rel_to_root_str]
                            
                            log_rc, log_stdout, log_stderr = _run_git_command(log_cmd, cwd=str(git_root_path_obj))

                            if log_rc == 0 and log_stdout.strip():
                                shas = log_stdout.strip().split('\\n')
                                if verbose:
                                     console.print(f"Found {len(shas)} commits for [cyan]{prompt_file_rel_to_root_str}[/cyan] in recent history (up to {MAX_COMMITS_TO_SEARCH}).")

                                if len(shas) > 1: # Need at least one commit before the one matching head_prompt_content
                                    for prior_sha in shas[1:]: # Iterate starting from the commit *before* HEAD's version of the file
                                        if verbose:
                                            console.print(f"  Checking commit {prior_sha[:7]} for content of [cyan]{prompt_file}[/cyan]...")
                                        
                                        # get_git_content_at_ref uses the original prompt_file path, 
                                        # which it resolves internally relative to the git root.
                                        prior_content = get_git_content_at_ref(prompt_file, prior_sha) 
                                        
                                        if prior_content is not None:
                                            if prior_content.strip() != new_prompt_candidate.strip():
                                                original_prompt_content_for_incremental = prior_content
                                                can_attempt_incremental = True
                                                found_different_prior = True
                                                if verbose:
                                                    console.print(f"    [green]Found prior different version at commit {prior_sha[:7]}. Using as original prompt.[/green]")
                                                break 
                                            elif verbose:
                                                 console.print(f"    Content at {prior_sha[:7]} is identical to current HEAD. Skipping.")
                                        elif verbose:
                                            console.print(f"    Could not retrieve content for [cyan]{prompt_file}[/cyan] at commit {prior_sha[:7]}.")
                                else: 
                                    if verbose:
                                        console.print(f"  File [cyan]{prompt_file_rel_to_root_str}[/cyan] has less than 2 versions in recent history at this path.")
                            elif verbose:
                                console.print(f"[yellow]Git (log) failed for {prompt_file_rel_to_root_str} or no history found: {log_stderr}[/yellow]")
                        
                        # Last resort: resolve the "original" prompt from the base branch.
                        # In the cloud sync-after-change flow the prompt edit is already
                        # committed on this branch (on-disk == HEAD) and no distinct prior
                        # version is found in local history, so without this we silently
                        # fall back to full regeneration and re-drop declared symbols
                        # (#1938/#1940, test_repo#4232). Configurable via PDD_SYNC_BASE_REF
                        # (defaults to origin/main). Only used when it differs from the
                        # current prompt; otherwise leave can_attempt_incremental False so an
                        # honest full regeneration runs (surfaced loudly below).
                        if not found_different_prior:
                            base_ref = os.environ.get("PDD_SYNC_BASE_REF", "origin/main")
                            base_content = get_git_content_at_ref(prompt_file, git_ref=base_ref)
                            if base_content is not None and base_content.strip() != prompt_content.strip():
                                original_prompt_content_for_incremental = base_content
                                can_attempt_incremental = True
                                found_different_prior = True
                                if verbose:
                                    console.print(f"[cyan]Using base-branch ({base_ref}) prompt as incremental original.[/cyan]")
                            elif verbose:
                                console.print(
                                    f"[yellow]Warning: Could not find a prior *different* version of {prompt_file} "
                                    f"within the last {MAX_COMMITS_TO_SEARCH if git_root_path_obj else 'N/A'} relevant commits, "
                                    f"and base-branch ({base_ref}) did not provide a distinct original. "
                                    f"Performing full regeneration.[/yellow]"
                                )
                else:
                    # File not in HEAD, cannot determine git-based original prompt.
                    if verbose:
                        console.print(f"[yellow]Warning: Could not find committed version of {prompt_file} in git (HEAD) for incremental generation.[/yellow]")
            
            if force_incremental_flag and existing_code_content:
                if not (original_prompt_content_for_incremental or "original_prompt_file" in input_strings): # Check if original prompt is actually available
                     console.print(
                        "[yellow]Warning: --incremental flag used, but original prompt could not be determined. "
                        "Falling back to full generation.[/yellow]"
                    )
                else:
                    can_attempt_incremental = True 
    
    if force_incremental_flag and (not output_path or not pathlib.Path(output_path).exists()):
        console.print(
            "[yellow]Warning: --incremental flag used, but output file does not exist or path not specified. "
            "Performing full generation.[/yellow]"
        )
        can_attempt_incremental = False

    # Conformance repair must bypass incremental generation. When
    # PDD_REPAIR_DIRECTIVE is active, the directive was appended to
    # prompt_content above, which makes the in-memory prompt look "changed"
    # relative to HEAD and would otherwise satisfy the incremental-eligibility
    # logic. Routing a repair retry through incremental_code_generator's
    # diff-analysis (patch-vs-regenerate) step can silently swallow the named
    # repair if that analysis fails or misclassifies. Force a clean full
    # regeneration so the <architecture_repair_directive> block reaches the
    # full generator directly. Normal incremental generation is unaffected when
    # no repair directive is set (#1724).
    repair_directive_active = bool(repair_directive_env and repair_directive_env.strip())
    if repair_directive_active and can_attempt_incremental:
        if verbose:
            console.print(
                "[blue]PDD_REPAIR_DIRECTIVE active: bypassing incremental generation "
                "and performing full generation with the repair directive.[/blue]"
            )
        can_attempt_incremental = False

    # Loud (non-verbose) degradation notice: a mature module (existing non-empty
    # code on disk) is about to be fully regenerated because no "original" prompt
    # could be resolved for surgical/incremental generation. This is the silent
    # failure mode that re-drops declared symbols on sync (#1938/#1940,
    # test_repo#4232) — surface it once so operators aren't blind. New/empty
    # modules doing a legitimate first generation and repair-directive full
    # regenerations are intentionally excluded.
    if (llm_enabled
            and existing_code_content is not None
            and not can_attempt_incremental
            and not repair_directive_active):
        console.print(
            "[yellow]Surgical/incremental generation unavailable (no original prompt "
            "resolved) — performing full regeneration.[/yellow]"
        )

    try:
        # Resolve post-process script from env/CLI override, then front matter, then sensible default per template
        post_process_script: Optional[str] = None
        prompt_body_for_script: str = prompt_content
        
        if verbose:
            console.print(f"[blue]LLM enabled:[/blue] {llm_enabled}")
        try:
            post_process_script = None
            script_override = None
            if env_vars:
                script_override = env_vars.get('POST_PROCESS_PYTHON') or env_vars.get('post_process_python')
            if not script_override:
                script_override = os.environ.get('POST_PROCESS_PYTHON') or os.environ.get('post_process_python')
            if script_override and str(script_override).strip():
                expanded = _expand_vars(str(script_override), env_vars)
                pkg_dir = pathlib.Path(__file__).parent.resolve()
                repo_root = pathlib.Path.cwd().resolve()
                repo_pdd_dir = (repo_root / 'pdd').resolve()
                candidate = pathlib.Path(expanded)
                if not candidate.is_absolute():
                    # 1) As provided, relative to CWD
                    as_is = (repo_root / candidate)
                    # 2) Under repo pdd/
                    under_repo_pdd = (repo_pdd_dir / candidate.name) if not as_is.exists() else as_is
                    # 3) Under installed package dir
                    under_pkg = (pkg_dir / candidate.name) if not as_is.exists() and not under_repo_pdd.exists() else as_is
                    if as_is.exists():
                        candidate = as_is
                    elif under_repo_pdd.exists():
                        candidate = under_repo_pdd
                    elif under_pkg.exists():
                        candidate = under_pkg
                    else:
                        candidate = as_is  # will fail later with not found
                post_process_script = str(candidate.resolve())
            elif fm_meta and isinstance(fm_meta, dict):
                raw_script = fm_meta.get('post_process_python')
                if isinstance(raw_script, str) and raw_script.strip():
                    # Expand variables like $VAR and ${VAR}
                    expanded = _expand_vars(raw_script, env_vars)
                    pkg_dir = pathlib.Path(__file__).parent.resolve()
                    repo_root = pathlib.Path.cwd().resolve()
                    repo_pdd_dir = (repo_root / 'pdd').resolve()
                    candidate = pathlib.Path(expanded)
                    if not candidate.is_absolute():
                        as_is = (repo_root / candidate)
                        under_repo_pdd = (repo_pdd_dir / candidate.name) if not as_is.exists() else as_is
                        under_pkg = (pkg_dir / candidate.name) if not as_is.exists() and not under_repo_pdd.exists() else as_is
                        if as_is.exists():
                            candidate = as_is
                        elif under_repo_pdd.exists():
                            candidate = under_repo_pdd
                        elif under_pkg.exists():
                            candidate = under_pkg
                        else:
                            candidate = as_is
                    post_process_script = str(candidate.resolve())
            # Fallback default: for architecture template, use built-in render_mermaid.py
            if not post_process_script:
                try:
                    prompt_str = str(prompt_file)
                    looks_like_arch_template = (
                        (isinstance(prompt_file, str) and (
                            prompt_str.endswith("architecture/architecture_json.prompt") or
                            prompt_str.endswith("architecture/architecture_json") or
                            "architecture_json.prompt" in prompt_str or
                            "architecture/architecture_json" in prompt_str
                        ))
                    )
                    looks_like_arch_output = (
                        bool(output_path) and pathlib.Path(str(output_path)).name == 'architecture.json'
                    )
                    if looks_like_arch_template or looks_like_arch_output:
                        pkg_dir = pathlib.Path(__file__).parent
                        repo_pdd_dir = pathlib.Path.cwd() / 'pdd'
                        if (pkg_dir / 'render_mermaid.py').exists():
                            post_process_script = str((pkg_dir / 'render_mermaid.py').resolve())
                        elif (repo_pdd_dir / 'render_mermaid.py').exists():
                            post_process_script = str((repo_pdd_dir / 'render_mermaid.py').resolve())
                except Exception:
                    post_process_script = None
            if verbose:
                console.print(f"[blue]Post-process script resolved to:[/blue] {post_process_script if post_process_script else 'None'}")
        except Exception:
            post_process_script = None
        # If LLM is disabled but no post-process script is provided, surface a helpful error
        if not llm_enabled and not post_process_script:
            console.print("[red]Error: llm: false requires 'post_process_python' to be specified in front matter.[/red]")
            return "", was_incremental_operation, total_cost, "error"
        if llm_enabled and can_attempt_incremental and existing_code_content is not None and original_prompt_content_for_incremental is not None:
            if verbose:
                console.print(Panel("Attempting incremental code generation...", title="[blue]Mode[/blue]", expand=False))

            if is_git_repository(str(pathlib.Path(prompt_file).parent)):
                files_to_stage_for_rollback: List[str] = []
                paths_to_check = [pathlib.Path(prompt_file).resolve()]
                if output_path and pathlib.Path(output_path).exists():
                    paths_to_check.append(pathlib.Path(output_path).resolve())

                for p_to_check in paths_to_check:
                    if not p_to_check.exists(): continue
                    
                    is_untracked = get_file_git_status(str(p_to_check)).startswith("??")
                    # Check if different from HEAD or untracked
                    is_different_from_head_rc = 1 if is_untracked else _run_git_command(["git", "diff", "--quiet", "HEAD", "--", str(p_to_check)], cwd=str(p_to_check.parent))[0]
                    
                    if is_different_from_head_rc != 0: # Different from HEAD or untracked
                        files_to_stage_for_rollback.append(str(p_to_check))
                
                if files_to_stage_for_rollback:
                    git_add_files(files_to_stage_for_rollback, verbose=verbose)
            
            # Preprocess both prompts: expand includes, substitute vars, then double.
            # Snapshot user-intent include paths from the ORIGINAL prompt (and the
            # post-`_expand_vars` variants for `${VAR}`-derived paths) so pass 2 can
            # gate the unresolved-include warning on real intent — pass 2 cannot
            # otherwise distinguish a literal `<include>` example in an expanded
            # source file's docstring from a real failed include (#1354 codex pass-3).
            from .preprocess import compute_user_intent_paths as _cuip
            orig_intent = _cuip(original_prompt_content_for_incremental) | _cuip(_expand_vars(original_prompt_content_for_incremental, env_vars))
            orig_proc = pdd_preprocess(original_prompt_content_for_incremental, recursive=True, double_curly_brackets=False, snapshot_recorder=snapshot_recorder)
            orig_proc = _expand_vars(orig_proc, env_vars)
            orig_proc = pdd_preprocess(orig_proc, recursive=False, double_curly_brackets=True, _user_intent_paths=orig_intent, snapshot_recorder=snapshot_recorder)

            new_intent = _cuip(prompt_content) | _cuip(_expand_vars(prompt_content, env_vars))
            new_proc = pdd_preprocess(prompt_content, recursive=True, double_curly_brackets=False, snapshot_recorder=snapshot_recorder)
            new_proc = _expand_vars(new_proc, env_vars)
            new_proc = pdd_preprocess(new_proc, recursive=False, double_curly_brackets=True, _user_intent_paths=new_intent, snapshot_recorder=snapshot_recorder)
            snapshot_expanded_prompt = json.dumps(
                {
                    "mode": "incremental",
                    "original_prompt": orig_proc,
                    "new_prompt": new_proc,
                },
                indent=2,
                sort_keys=True,
            )

            generated_code_content, was_incremental_operation, total_cost, model_name = incremental_code_generator_func(
                original_prompt=orig_proc,
                new_prompt=new_proc,
                existing_code=existing_code_content,
                language=language,
                strength=strength,
                temperature=temperature,
                time=time_budget,
                force_incremental=force_incremental_flag,
                verbose=verbose,
                preprocess_prompt=False
            )

            # Safety net: if incremental returned identical code, fall back to full generation.
            # The root-cause check lives in incremental_code_generator itself; this is
            # defense-in-depth in case a caller passes a different generator function.
            if (was_incremental_operation
                    and generated_code_content is not None
                    and existing_code_content is not None
                    and generated_code_content == existing_code_content):
                was_incremental_operation = False
                if verbose:
                    console.print("[yellow]Incremental patch produced no changes. Falling back to full generation.[/yellow]")

            if not was_incremental_operation:
                if verbose:
                    console.print(Panel("Incremental generator suggested full regeneration. Falling back.", title="[yellow]Fallback[/yellow]", expand=False))
            elif verbose:
                console.print(Panel(f"Incremental update successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Incremental Success[/green]", expand=False))

        if llm_enabled and not was_incremental_operation: # Full generation path
            if verbose:
                console.print(Panel("Performing full code generation...", title="[blue]Mode[/blue]", expand=False))
            
            cloud_only = _env_flag_enabled("PDD_CLOUD_ONLY") or _env_flag_enabled("PDD_NO_LOCAL_FALLBACK")
            current_execution_is_local = is_local_execution_preferred and not cloud_only
            
            # Cloud auth cannot succeed in headless worker environments (no JWT
            # cache, no interactive device flow). Skip directly to local execution
            # to avoid warning messages that cause LLM agent bailout (issue #596).
            if not current_execution_is_local and CloudConfig.is_running_in_cloud():
                current_execution_is_local = True

            if not current_execution_is_local:
                if verbose: console.print("Attempting cloud code generation...")
                # Expand includes, substitute vars, then double. Pre-compute
                # user-intent include paths from the ORIGINAL prompt + post-
                # `_expand_vars` variants so pass 2 can gate the unresolved-
                # include warning against real intent (see #1354 codex pass-3).
                from .preprocess import compute_user_intent_paths as _cuip
                _cloud_intent = _cuip(prompt_content) | _cuip(_expand_vars(prompt_content, env_vars))
                processed_prompt_for_cloud = pdd_preprocess(
                    prompt_content,
                    recursive=True,
                    double_curly_brackets=False,
                    exclude_keys=[],
                    compress=compress,
                    snapshot_recorder=snapshot_recorder,
                )
                processed_prompt_for_cloud = _expand_vars(processed_prompt_for_cloud, env_vars)
                processed_prompt_for_cloud = pdd_preprocess(
                    processed_prompt_for_cloud,
                    recursive=False,
                    double_curly_brackets=True,
                    exclude_keys=[],
                    compress=compress,
                    _user_intent_paths=_cloud_intent,
                    snapshot_recorder=snapshot_recorder,
                )
                snapshot_expanded_prompt = processed_prompt_for_cloud
                if verbose: console.print(Panel(Text(processed_prompt_for_cloud, overflow="fold"), title="[cyan]Preprocessed Prompt for Cloud[/cyan]", expand=False))

                # Extract and display pinned example ID if present in prompt
                pin_match = re.search(r'<pin>([^<]+)</pin>', processed_prompt_for_cloud)
                if pin_match and verbose:
                    pinned_example_id = pin_match.group(1).strip()
                    console.print(f"[cyan]Using pinned example:[/cyan] {pinned_example_id}")

                # Get JWT token via CloudConfig (handles both injected tokens and device flow)
                jwt_token = CloudConfig.get_jwt_token(verbose=verbose)

                if not jwt_token:
                    if cloud_only:
                        console.print("[red]Cloud authentication failed.[/red]")
                        raise click.UsageError("Cloud authentication failed")
                    console.print("[yellow]Cloud authentication failed. Falling back to local execution.[/yellow]")
                    current_execution_is_local = True

                if jwt_token and not current_execution_is_local:
                    payload = {
                        "promptContent": processed_prompt_for_cloud,
                        "searchInput": prompt_content,
                        "language": language,
                        "strength": strength,
                        "temperature": temperature,
                        "verbose": verbose,
                        "compress": compress,
                    }
                    requested_model = None
                    if isinstance(ctx.obj, dict):
                        requested_model = ctx.obj.get("model")
                    requested_model = requested_model or os.environ.get(
                        "PDD_MODEL_DEFAULT"
                    )
                    if requested_model and str(requested_model).strip():
                        payload["model"] = str(requested_model).strip()
                    headers = {"Authorization": f"Bearer {jwt_token}", "Content-Type": "application/json"}
                    cloud_url = CloudConfig.get_endpoint_url("generateCode")
                    try:
                        ctx_obj = ctx.obj if isinstance(ctx.obj, dict) else None
                        if ctx_obj is None:
                            ctx.obj = {}
                            ctx_obj = ctx.obj
                        overrides = stash_grounding_overrides_on_ctx(ctx_obj, prompt_content)
                        if cli_params.get("review_examples"):
                            review_pinned_examples_before_generation(
                                ctx_obj,
                                prompt_content,
                                force=force_overwrite,
                                quiet=quiet,
                            )
                        response = requests.post(cloud_url, json=payload, headers=headers, timeout=get_cloud_request_timeout())
                        response.raise_for_status()
                        
                        response_data = response.json()
                        generated_code_content = response_data.get("generatedCode")
                        total_cost = float(response_data.get("totalCost", 0.0))
                        model_name = response_data.get("modelName", "cloud_model")

                        # Extract example information from examplesUsed array (cloud returns this)
                        examples_used = response_data.get("examplesUsed", [])
                        if cli_params.get("review_examples"):
                            warn_cloud_examples_not_preapproved(
                                examples_used,
                                cli_params.get("grounding_review_decisions"),
                                quiet=quiet,
                            )
                        grounding_meta = build_grounding_metadata(
                            mode="cloud",
                            examples_used=examples_used,
                            grounding_overrides=overrides,
                            reviewed=grounding_reviewed_for_manifest(
                                cli_params,
                                examples_used,
                            ),
                        )
                        if ctx.obj is None:
                            ctx.obj = {}
                        if isinstance(ctx.obj, dict):
                            ctx.obj["last_grounding"] = grounding_meta

                        if examples_used:
                            selected_example_id = examples_used[0].get("id")
                            selected_example_title = examples_used[0].get("title")
                            if snapshot_recorder:
                                snapshot_recorder.record_grounding_examples(examples_used)
                        else:
                            selected_example_id = None
                            selected_example_title = None
                            if snapshot_recorder:
                                snapshot_recorder.record_grounding_unavailable("cloud_returned_no_examples")

                        # Strip markdown code fences if present (cloud API returns fenced JSON)
                        if generated_code_content and isinstance(language, str) and language.strip().lower() == "json":
                            cleaned = generated_code_content.strip()
                            if cleaned.startswith("```json"):
                                cleaned = cleaned[7:]
                            elif cleaned.startswith("```"):
                                cleaned = cleaned[3:]
                            if cleaned.endswith("```"):
                                cleaned = cleaned[:-3]
                            generated_code_content = cleaned.strip()
                        if not generated_code_content:
                            if cloud_only:
                                console.print("[red]Cloud execution returned no code.[/red]")
                                language_name = str(language or "").strip().lower()
                                if (
                                    not _env_flag_enabled("PDD_ALLOW_EMPTY_GENERATION")
                                    and language_name != "prompt"
                                ):
                                    raise ProseOutputError(
                                        prompt_name=pathlib.Path(prompt_file).name,
                                        output_path=output_path or "",
                                        language=language or "unknown",
                                        model_name=model_name or "unknown",
                                        total_cost=float(total_cost or 0.0),
                                        raw_output=generated_code_content or "",
                                        extractor_result="empty",
                                    )
                                raise click.UsageError("Cloud execution returned no code")
                            console.print("[yellow]Cloud execution returned no code. Falling back to local.[/yellow]")
                            current_execution_is_local = True
                        elif verbose:
                             # Display example info if available
                             if selected_example_id:
                                 example_info = f" | Example: {selected_example_id}"
                                 if selected_example_title:
                                     example_info += f" ({selected_example_title})"
                                 console.print(Panel(f"Cloud generation successful. Model: {model_name}, Cost: ${total_cost:.6f}{example_info}", title="[green]Cloud Success[/green]", expand=False))
                             else:
                                 console.print(Panel(f"Cloud generation successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Cloud Success[/green]", expand=False))
                             if grounding_meta.get("selected_examples"):
                                 console.print("[cyan]Grounding examples selected:[/cyan]")
                                 for example in grounding_meta["selected_examples"]:
                                     console.print(f"  - {example.get('module', 'unknown')}")
                    except requests.exceptions.Timeout:
                        if cloud_only:
                            console.print(f"[red]Cloud execution timed out ({get_cloud_timeout()}s).[/red]")
                            raise click.UsageError("Cloud execution timed out")
                        console.print(f"[yellow]Cloud execution timed out ({get_cloud_timeout()}s). Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    except requests.exceptions.HTTPError as e:
                        status_code = e.response.status_code if e.response else 0
                        err_content = e.response.text[:200] if e.response else "No response content"

                        # Non-recoverable errors: do NOT fall back to local
                        if status_code == 402:  # Insufficient credits
                            try:
                                error_data = e.response.json()
                                current_balance = error_data.get("currentBalance", "unknown")
                                estimated_cost = error_data.get("estimatedCost", "unknown")
                                console.print(f"[red]Insufficient credits. Current balance: {current_balance}, estimated cost: {estimated_cost}[/red]")
                            except Exception:
                                console.print(f"[red]Insufficient credits: {err_content}[/red]")
                            raise click.UsageError("Insufficient credits for cloud code generation")
                        elif status_code == 401:  # Authentication error
                            console.print(f"[red]Authentication failed: {err_content}[/red]")
                            raise click.UsageError("Cloud authentication failed")
                        elif status_code == 403:  # Authorization error (not approved)
                            console.print(f"[red]Access denied: {err_content}[/red]")
                            raise click.UsageError("Access denied - user not approved")
                        elif status_code == 400:  # Validation error (e.g., empty prompt)
                            console.print(f"[red]Invalid request: {err_content}[/red]")
                            raise click.UsageError(f"Invalid request: {err_content}")
                        else:
                            # Recoverable errors (5xx, unexpected errors): fall back to local
                            if cloud_only:
                                console.print(f"[red]Cloud HTTP error ({status_code}): {err_content}[/red]")
                                raise click.UsageError(f"Cloud HTTP error ({status_code}): {err_content}")
                            console.print(f"[yellow]Cloud HTTP error ({status_code}): {err_content}. Falling back to local.[/yellow]")
                            current_execution_is_local = True
                    except requests.exceptions.RequestException as e:
                        if cloud_only:
                            console.print(f"[red]Cloud network error: {e}[/red]")
                            raise click.UsageError(f"Cloud network error: {e}")
                        console.print(f"[yellow]Cloud network error: {e}. Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    except json.JSONDecodeError:
                        if cloud_only:
                            console.print("[red]Cloud returned invalid JSON.[/red]")
                            raise click.UsageError("Cloud returned invalid JSON")
                        console.print("[yellow]Cloud returned invalid JSON. Falling back to local.[/yellow]")
                        current_execution_is_local = True
            
            if current_execution_is_local:
                if verbose: console.print("Executing code generator locally...")
                # Expand includes, substitute vars, then double; pass to local
                # generator with preprocess_prompt=False. Pre-compute user-intent
                # include paths from the ORIGINAL prompt + post-`_expand_vars`
                # variants so pass 2 can gate the unresolved-include warning
                # against real intent (see #1354 codex pass-3).
                from .preprocess import compute_user_intent_paths as _cuip
                _local_intent = _cuip(prompt_content) | _cuip(_expand_vars(prompt_content, env_vars))
                local_prompt = pdd_preprocess(
                    prompt_content,
                    recursive=True,
                    double_curly_brackets=False,
                    exclude_keys=[],
                    compress=compress,
                    snapshot_recorder=snapshot_recorder,
                )
                local_prompt = _expand_vars(local_prompt, env_vars)
                local_prompt = pdd_preprocess(
                    local_prompt,
                    recursive=False,
                    double_curly_brackets=True,
                    exclude_keys=[],
                    compress=compress,
                    _user_intent_paths=_local_intent,
                    snapshot_recorder=snapshot_recorder,
                )
                snapshot_expanded_prompt = local_prompt
                if snapshot_recorder:
                    snapshot_recorder.record_grounding_unavailable("local_generation")
                # Language already resolved (front matter overrides detection if present)
                gen_language = language
                
                # Extract output schema from front matter if available
                output_schema = fm_meta.get("output_schema") if fm_meta else None
                
                generated_code_content, total_cost, model_name = local_code_generator_func(
                    prompt=local_prompt,
                    language=gen_language,
                    strength=strength,
                    temperature=temperature,
                    time=time_budget,
                    verbose=verbose,
                    preprocess_prompt=False,
                    output_schema=output_schema,
                    compress=compress,
                )
                was_incremental_operation = False
                if verbose:
                    console.print(Panel(f"Full generation successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Local Success[/green]", expand=False))

        # Optional post-process Python hook (runs after LLM when enabled, or standalone when LLM is disabled)
        if post_process_script:
            try:
                python_executable = detect_host_python_executable()
                # Choose stdin for the script: LLM output if available and enabled, else prompt body
                stdin_payload = generated_code_content if (llm_enabled and generated_code_content is not None) else prompt_body_for_script
                env = os.environ.copy()
                env['PDD_LANGUAGE'] = str(language or '')
                env['PDD_OUTPUT_PATH'] = str(output_path or '')
                env['PDD_PROMPT_FILE'] = str(pathlib.Path(prompt_file).resolve())
                env['PDD_LLM'] = '1' if llm_enabled else '0'
                try:
                    env['PDD_ENV_VARS'] = json.dumps(env_vars or {})
                except Exception:
                    env['PDD_ENV_VARS'] = '{}'
                # If front matter provides args, run in argv mode with a temp input file
                fm_args = None
                try:
                    # Env/CLI override for args (comma-separated or JSON list)
                    raw_args_env = None
                    if env_vars:
                        raw_args_env = env_vars.get('POST_PROCESS_ARGS') or env_vars.get('post_process_args')
                    if not raw_args_env:
                        raw_args_env = os.environ.get('POST_PROCESS_ARGS') or os.environ.get('post_process_args')
                    if raw_args_env:
                        s = str(raw_args_env).strip()
                        parsed_list = None
                        if s.startswith('[') and s.endswith(']'):
                            try:
                                parsed = json.loads(s)
                                if isinstance(parsed, list):
                                    parsed_list = [str(a) for a in parsed]
                            except Exception:
                                parsed_list = None
                        if parsed_list is None:
                            if ',' in s:
                                parsed_list = [part.strip() for part in s.split(',') if part.strip()]
                            else:
                                parsed_list = [part for part in s.split() if part]
                        fm_args = parsed_list or None
                    if fm_args is None:
                        raw_args = fm_meta.get('post_process_args') if isinstance(fm_meta, dict) else None
                        if isinstance(raw_args, list):
                            fm_args = [str(a) for a in raw_args]
                except Exception:
                    fm_args = None
                proc = None
                temp_input_path = None
                try:
                    if fm_args is None:
                        # Provide sensible default args for architecture template with render_mermaid.py
                        try:
                            if post_process_script and pathlib.Path(post_process_script).name == 'render_mermaid.py':
                                if isinstance(prompt_file, str) and prompt_file.endswith('architecture/architecture_json.prompt'):
                                    fm_args = ["{INPUT_FILE}", "{APP_NAME}", "{OUTPUT_HTML}"]
                        except Exception:
                            pass
                    if fm_args:
                        # When LLM is disabled, use the existing output file instead of creating a temp file
                        if not llm_enabled and output_path and pathlib.Path(output_path).exists():
                            temp_input_path = str(pathlib.Path(output_path).resolve())
                            env['PDD_POSTPROCESS_INPUT_FILE'] = temp_input_path
                        else:
                            # Write payload to a temp file for scripts expecting a file path input.
                            # LLM output must not touch output_path until conformance gates pass.
                            suffix = '.json' if (isinstance(language, str) and str(language).lower().strip() == 'json') or (output_path and str(output_path).lower().endswith('.json')) else '.txt'
                            with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix=suffix, encoding='utf-8') as tf:
                                tf.write(stdin_payload or '')
                                temp_input_path = tf.name
                            env['PDD_POSTPROCESS_INPUT_FILE'] = temp_input_path
                        # Compute placeholder values
                        app_name_val = (env_vars or {}).get('APP_NAME') if env_vars else None
                        if not app_name_val:
                            app_name_val = 'System Architecture'
                        output_html_default = None
                        if output_path and str(output_path).lower().endswith('.json'):
                            output_html_default = str(pathlib.Path(output_path).with_name(f"{pathlib.Path(output_path).stem}_diagram.html").resolve())
                        placeholder_map = {
                            'INPUT_FILE': temp_input_path or '',
                            'OUTPUT': str(output_path or ''),
                            'PROMPT_FILE': str(pathlib.Path(prompt_file).resolve()),
                            'APP_NAME': str(app_name_val),
                            'OUTPUT_HTML': str(output_html_default or ''),
                        }
                        def _subst_arg(arg: str) -> str:
                            # First expand $VARS using existing helper, then {TOKENS}
                            expanded = _expand_vars(arg, env_vars)
                            for key, val in placeholder_map.items():
                                expanded = expanded.replace('{' + key + '}', val)
                            return expanded
                        args_list = [_subst_arg(a) for a in fm_args]
                        if verbose:
                            console.print(Panel(f"Post-process hook (argv)\nScript: {post_process_script}\nArgs: {args_list}", title="[blue]Post-process[/blue]", expand=False))
                        proc = subprocess.run(
                            [python_executable, post_process_script] + args_list,
                            text=True,
                            capture_output=True,
                            timeout=300,
                            cwd=str(pathlib.Path(post_process_script).parent),
                            env=env
                        )
                    else:
                        # Run the script with stdin payload, capture stdout as final content
                        if verbose:
                            console.print(Panel(f"Post-process hook (stdin)\nScript: {post_process_script}", title="[blue]Post-process[/blue]", expand=False))
                        proc = subprocess.run(
                            [python_executable, post_process_script],
                            input=stdin_payload or '',
                            text=True,
                            capture_output=True,
                            timeout=300,
                            cwd=str(pathlib.Path(post_process_script).parent),
                            env=env
                        )
                finally:
                    if temp_input_path:
                        try:
                            # Only delete temp files, not the actual output file when llm=false.
                            is_resolved_output = bool(
                                output_path
                                and temp_input_path == str(pathlib.Path(output_path).resolve())
                            )
                            if (
                                proc
                                and proc.returncode == 0
                                and llm_enabled
                                and generated_code_content is not None
                                and not is_resolved_output
                            ):
                                generated_code_content = pathlib.Path(temp_input_path).read_text(
                                    encoding="utf-8"
                                )
                            if not is_resolved_output:
                                os.unlink(temp_input_path)
                        except Exception:
                            pass
                if proc and proc.returncode == 0:
                    if verbose:
                        console.print(Panel(f"Post-process success (rc=0)\nstdout: {proc.stdout[:150]}\nstderr: {proc.stderr[:150]}", title="[green]Post-process[/green]", expand=False))
                    # Do not modify generated_code_content to preserve architecture.json
                else:
                    rc = getattr(proc, 'returncode', 'N/A')
                    err = getattr(proc, 'stderr', '')
                    console.print(f"[yellow]Post-process failed (rc={rc}). Stderr:\n{err[:500]}[/yellow]")
            except FileNotFoundError:
                console.print(f"[yellow]Post-process script not found: {post_process_script}. Skipping.[/yellow]")
            except subprocess.TimeoutExpired:
                console.print("[yellow]Post-process script timed out. Skipping.[/yellow]")
            except Exception as e:
                console.print(f"[yellow]Post-process script error: {e}. Skipping.[/yellow]")
        if generated_code_content is not None:
            prompt_name = pathlib.Path(prompt_file).name
            language_name = str(language or "").strip().lower()
            if (
                not _env_flag_enabled("PDD_ALLOW_EMPTY_GENERATION")
                and language_name != "prompt"
                and not generated_code_content.strip()
            ):
                raise ProseOutputError(
                    prompt_name=prompt_name,
                    output_path=output_path or "",
                    language=language or "unknown",
                    model_name=model_name or "unknown",
                    total_cost=float(total_cost or 0.0),
                    raw_output=generated_code_content,
                    extractor_result="empty",
                )

            syntax_err, generated_code_content = _verify_language_validity(
                generated_code_content, language or ""
            )
            if syntax_err is not None:
                raise LanguageMismatchError(
                    prompt_name=prompt_name,
                    output_path=output_path or "",
                    language=language or "unknown",
                    model_name=model_name or "unknown",
                    total_cost=float(total_cost or 0.0),
                    raw_output=generated_code_content,
                    syntax_error=(
                        f"{syntax_err.msg} (line {syntax_err.lineno}, "
                        f"offset {syntax_err.offset})"
                    ),
                )

            # Optional output_schema JSON validation before writing (only when LLM ran)
            if llm_enabled:
                try:
                    if fm_meta and isinstance(fm_meta.get("output_schema"), dict):
                        is_json_output = False
                        if isinstance(language, str) and str(language).lower().strip() == "json":
                            is_json_output = True
                        elif output_path and str(output_path).lower().endswith(".json"):
                            is_json_output = True
                        if is_json_output:
                            # Check if the generated content is an error message from llm_invoke
                            if generated_code_content.strip().startswith("ERROR:"):
                                raise click.UsageError(f"LLM generation failed: {generated_code_content}")
                                
                            parsed = json.loads(generated_code_content)

                            # Fix common LLM mistake: unwrap arrays wrapped in objects
                            # LLMs often return {"items": [...]} or {"type": "array", "items": [...]}
                            # when the schema expects a plain array [...]
                            output_schema = fm_meta.get("output_schema", {})
                            if output_schema.get("type") == "array" and isinstance(parsed, dict):
                                # Check for common wrapper patterns
                                if "items" in parsed and isinstance(parsed["items"], list):
                                    parsed = parsed["items"]
                                    generated_code_content = json.dumps(parsed, indent=2)
                                elif "data" in parsed and isinstance(parsed["data"], list):
                                    parsed = parsed["data"]
                                    generated_code_content = json.dumps(parsed, indent=2)
                                elif "results" in parsed and isinstance(parsed["results"], list):
                                    parsed = parsed["results"]
                                    generated_code_content = json.dumps(parsed, indent=2)

                            if _is_architecture_template(fm_meta):
                                parsed, repaired = _repair_architecture_interface_types(parsed)
                                if repaired:
                                    generated_code_content = json.dumps(parsed, indent=2)
                                # Issue #617: filename mirrors filepath (directory structure preserved)
                                if isinstance(parsed, list):
                                    from pdd.architecture_sync import normalize_architecture_filenames
                                    normalize_architecture_filenames(parsed)
                                generated_code_content = json.dumps(parsed, indent=2)
                            try:
                                import jsonschema
                                jsonschema.validate(instance=parsed, schema=fm_meta.get("output_schema"))
                            except ModuleNotFoundError:
                                if verbose and not quiet:
                                    console.print("[yellow]jsonschema not installed; skipping schema validation.[/yellow]")
                            except Exception as ve:
                                raise click.UsageError(f"Generated JSON does not match output_schema: {ve}")
                except json.JSONDecodeError as jde:
                    raise click.UsageError(f"Generated output is not valid JSON: {jde}")

            # Architecture conformance check: verify generated code exports match
            # the interface declarations in architecture.json (hard failure on mismatch).
            # Gate on `is not None` rather than a truthy check so an empty generation
            # over an existing module still fires the conformance gate — without this
            # an empty body silently slipped past every gate and the writer below
            # truncated the existing file to 0 bytes (external review iter-13 follow-up).
            if not _env_flag_enabled("PDD_SKIP_CONFORMANCE") and generated_code_content is not None:
                try:
                    _verify_architecture_conformance(
                        generated_code=generated_code_content,
                        prompt_name=pathlib.Path(prompt_file).name,
                        arch_path=None,  # Uses default architecture.json
                        language=language,
                        verbose=verbose,
                        output_path=output_path,
                        prompt_content=prompt_content,
                    )
                except ArchitectureConformanceError as conform_err:
                    conform_err.total_cost = float(total_cost or 0.0)
                    conform_err.model_name = model_name or "unknown"
                    raise  # Re-raise conformance errors as hard failures
                except click.UsageError:
                    raise  # Re-raise conformance errors as hard failures
                except Exception as conform_err:
                    if verbose and not quiet:
                        console.print(f"[yellow]Warning: Architecture conformance check failed: {conform_err}[/yellow]")

            if (
                not _env_flag_enabled("PDD_SKIP_CONFORMANCE")
                and generated_code_content is not None
                and existing_code_content is not None
            ):
                # Gate on `is not None` rather than a truthy check so an
                # empty generation over an existing module still fires the
                # public-surface and test-churn gates. The truthy form
                # previously skipped both gates whenever the provider
                # returned "", and the writer below then truncated the
                # existing file to 0 bytes — silent erasure of mature
                # public APIs and test coverage (external review iter-13
                # follow-up; reproduced with mocked local generation).
                #
                # Deterministic annotation reconciliation (issue #1968): when a
                # regeneration drifts a declared signature ONLY in annotation
                # spelling (declared `object` vs emitted `Any`, or a broadened
                # union), rewrite the emitted annotation back to the declared text
                # BEFORE the gate re-checks so the sync converges without another
                # generation attempt. The pass is a no-op unless it finds such
                # drift, so it never alters an otherwise-passing generation.
                reconciled_code = _reconcile_declared_annotation_drift(
                    existing_code=existing_code_content,
                    generated_code=generated_code_content,
                    prompt_name=prompt_name,
                    output_path=output_path,
                    language=language,
                    prompt_content=prompt_content,
                )
                if reconciled_code is not None:
                    generated_code_content = reconciled_code
                try:
                    _verify_public_surface_regression(
                        existing_code=existing_code_content,
                        generated_code=generated_code_content,
                        prompt_name=prompt_name,
                        output_path=output_path,
                        language=language,
                        prompt_content=prompt_content,
                    )
                    _verify_test_churn(
                        existing_code=existing_code_content,
                        generated_code=generated_code_content,
                        prompt_name=prompt_name,
                        output_path=output_path,
                        prompt_content=prompt_content,
                    )
                except (PublicSurfaceRegressionError, TestChurnError) as compat_err:
                    if output_path and existing_code_content is not None:
                        try:
                            pathlib.Path(output_path).write_text(
                                existing_code_content,
                                encoding="utf-8",
                            )
                        except Exception as restore_err:
                            if verbose and not quiet:
                                console.print(
                                    f"[yellow]Warning: Could not restore {output_path} "
                                    f"after compatibility gate failure: {restore_err}[/yellow]"
                                )
                    compat_err.total_cost = float(total_cost or 0.0)
                    compat_err.model_name = model_name or "unknown"
                    raise

            if output_path:
                p_output = pathlib.Path(output_path)
                p_output.parent.mkdir(parents=True, exist_ok=True)

                # Safety net for file types the public-surface / test-churn
                # gates cannot inspect (non-Python source, JSON, YAML,
                # prompt files, etc.): refuse to overwrite a non-empty
                # existing file with empty / whitespace-only generated
                # content. An empty body over an existing artifact is
                # almost always an upstream provider/parse failure, and
                # silently truncating to 0 bytes loses real work.
                # `PDD_ALLOW_EMPTY_GENERATION=1` is the explicit escape
                # hatch for the rare intentional case.
                if (
                    existing_code_content
                    and existing_code_content.strip()
                    and (
                        generated_code_content is None
                        or not generated_code_content.strip()
                    )
                    and not _env_flag_enabled("PDD_ALLOW_EMPTY_GENERATION")
                ):
                    raise click.UsageError(
                        f"Refusing to overwrite {output_path} with empty "
                        f"generated content (existing file has "
                        f"{len(existing_code_content)} chars). Empty output "
                        f"typically indicates an upstream provider or parse "
                        f"failure. Set PDD_ALLOW_EMPTY_GENERATION=1 to bypass."
                    )

                final_content = generated_code_content

                # Validate <include> tags in generated prompt files (Issue #225 PR #286)
                if p_output.suffix == '.prompt' or language == 'prompt':
                    validated_content, invalid_includes = validate_prompt_includes(
                        final_content,
                        base_dir=str(p_output.parent),
                        remove_invalid=False,
                    )
                    final_content = validated_content
                    if invalid_includes:
                        if verbose or not quiet:
                            console.print(
                                f"[yellow]Warning: Found {len(invalid_includes)} invalid <include> tag(s) "
                                f"referencing non-existent files. Replaced with comments.[/yellow]"
                            )
                            for inv_path in invalid_includes:
                                console.print(f"  [dim]- {inv_path}[/dim]")

                # Inject architecture metadata tags for .prompt files (reverse sync)
                if p_output.suffix == '.prompt':
                    try:
                        # Check if this prompt has an architecture entry
                        arch_entry = get_architecture_entry_for_prompt(p_output.name)

                        # Only inject tags if:
                        # 1. Architecture entry exists
                        # 2. Content doesn't already have PDD tags (preserve manual edits)
                        if arch_entry and not has_pdd_tags(final_content):
                            tags = generate_tags_from_architecture(arch_entry)
                            if tags:
                                # Prepend tags to the generated content
                                final_content = tags + '\n\n' + final_content
                                if verbose:
                                    console.print("[info]Injected architecture metadata tags from architecture.json[/info]")
                    except Exception as e:
                        # Don't fail generation if tag injection fails
                        if verbose:
                            console.print(f"[yellow]Warning: Could not inject architecture tags: {e}[/yellow]")

                p_output.write_text(final_content, encoding="utf-8")
                if snapshot_recorder:
                    snapshot_manifest = snapshot_recorder.finalize(
                        expanded_prompt=snapshot_expanded_prompt or prompt_content,
                        prompt_text=prompt_content,
                        output_files=[p_output],
                        model=model_name,
                        provider="local" if current_execution_is_local else "cloud",
                    )
                    ctx.ensure_object(dict)
                    ctx.obj["context_snapshot"] = {
                        "run_id": snapshot_manifest.get("run_id"),
                        "manifest_path": snapshot_manifest.get("manifest_path"),
                        "snapshot_dir": snapshot_manifest.get("snapshot_dir"),
                        "expanded_prompt": snapshot_manifest.get("expanded_prompt"),
                        "uses_nondeterministic_context": snapshot_manifest.get(
                            "uses_nondeterministic_context"
                        ),
                        "dynamic_tags": snapshot_manifest.get("dynamic_tags", []),
                        "declared_dynamic_tags": snapshot_manifest.get("declared_dynamic_tags", []),
                        "redaction_applied": snapshot_manifest.get("redaction", {}).get(
                            "applied", False
                        ),
                        "redaction": snapshot_manifest.get("redaction"),
                        "artifacts": snapshot_manifest.get("artifacts", []),
                        "grounding_examples": snapshot_manifest.get("generation", {}).get(
                            "grounding_examples", []
                        ),
                    }
                if verbose or not quiet:
                    console.print(f"Generated code saved to: [green]{p_output.resolve()}[/green]")
                # Post-write: optionally wire exports to parent __init__.py.
                if _should_wire_generated_exports(str(p_output)):
                    try:
                        wiring_exports = _detect_wireable_exports(final_content, str(p_output))
                        if wiring_exports:
                            wired = _wire_to_parent_init(str(p_output), wiring_exports, verbose=verbose)
                            if wired and verbose and not quiet:
                                console.print(f"[green]Auto-wired {len(wiring_exports)} export(s) to parent __init__.py[/green]")
                    except Exception as wire_err:
                        if verbose:
                            console.print(f"[yellow]Warning: Auto-wiring failed: {wire_err}[/yellow]")
                # Safety net: ensure architecture HTML is generated post-write if applicable
                try:
                    # Prefer resolved script if available; else default for architecture outputs
                    script_path2 = post_process_script
                    if not script_path2:
                        looks_like_arch_output2 = pathlib.Path(str(p_output)).name == 'architecture.json'
                        if looks_like_arch_output2:
                            pkg_dir2 = pathlib.Path(__file__).parent
                            repo_pdd_dir2 = pathlib.Path.cwd() / 'pdd'
                            if (pkg_dir2 / 'render_mermaid.py').exists():
                                script_path2 = str((pkg_dir2 / 'render_mermaid.py').resolve())
                            elif (repo_pdd_dir2 / 'render_mermaid.py').exists():
                                script_path2 = str((repo_pdd_dir2 / 'render_mermaid.py').resolve())
                    if script_path2 and pathlib.Path(script_path2).exists():
                        app_name2 = os.environ.get('APP_NAME') or (env_vars or {}).get('APP_NAME') or 'System Architecture'
                        out_html2 = os.environ.get('POST_PROCESS_OUTPUT') or str(p_output.with_name(f"{p_output.stem}_diagram.html").resolve())
                        html_missing = not pathlib.Path(out_html2).exists()
                        always_run_for_arch = pathlib.Path(str(p_output)).name == 'architecture.json'
                        if always_run_for_arch or html_missing:
                            try:
                                py_exec2 = detect_host_python_executable()
                            except Exception:
                                py_exec2 = sys.executable
                            if verbose:
                                console.print(Panel(f"Safety net post-process\nScript: {script_path2}\nArgs: {[str(p_output.resolve()), app_name2, out_html2]}", title="[blue]Post-process[/blue]", expand=False))
                            sp2 = subprocess.run([py_exec2, script_path2, str(p_output.resolve()), app_name2, out_html2],
                                                 capture_output=True, text=True, cwd=str(pathlib.Path(script_path2).parent))
                            if sp2.returncode == 0 and not quiet:
                                print(f"✅ Generated: {out_html2}")
                            elif verbose:
                                console.print(f"[yellow]Safety net failed (rc={sp2.returncode}). stderr:\n{sp2.stderr[:300]}[/yellow]")
                except Exception:
                    pass
                # Post-step now runs regardless of LLM value via the general post-process hook above.
            elif not quiet:
                # No destination resolved; surface the generated code directly to the console.
                console.print(Panel(Text(generated_code_content, overflow="fold"), title="[cyan]Generated Code[/cyan]", expand=False))
                console.print("[yellow]No output path resolved; skipping file write and stdout print.[/yellow]")
        else:
            # If LLM was disabled and post-process ran, that's a success (no error)
            if not llm_enabled and post_process_script:
                if verbose or not quiet:
                    console.print("[green]Post-process completed successfully (LLM was disabled).[/green]")
            else:
                console.print("[red]Error: Code generation failed. No code was produced.[/red]")
                return "", was_incremental_operation, total_cost, model_name or "error"

    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        if (
            e.__class__.__name__ == "EstimateOnlyResult"
            and isinstance(getattr(e, "estimate", None), dict)
        ):
            raise
        if isinstance(e, click.UsageError):
            raise

        # For any other unexpected error, we should fail hard so the CLI exits non-zero
        # Log the detailed traceback first if verbose
        if verbose:
            import traceback
            console.print(traceback.format_exc())

        raise click.UsageError(f"An unexpected error occurred: {e}")

    if isinstance(ctx.obj, dict) and "last_grounding" not in ctx.obj:
        overrides = ctx.obj.get("grounding_overrides") or stash_grounding_overrides_on_ctx(
            ctx.obj, prompt_content
        )
        ctx.obj["last_grounding"] = build_grounding_metadata(
            mode="unavailable",
            grounding_overrides=overrides,
            reviewed=grounding_reviewed_for_manifest(cli_params, []),
        )

    return generated_code_content or "", was_incremental_operation, total_cost, model_name
