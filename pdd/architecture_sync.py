"""
Architecture sync module for bidirectional sync between architecture.json and prompt files.

This module provides functionality to:
1. Parse PDD metadata tags (<pdd-reason>, <pdd-interface>, <pdd-dependency>) from prompt files
2. Update architecture.json from prompt file tags (prompt → architecture.json)
3. Validate dependencies and detect issues

Philosophy: Prompts are the source of truth, architecture.json is derived from prompts.
Validation: Lenient - missing tags are OK, only update fields that have tags present.
"""

import ast
import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional

from lxml import etree

from .architecture_registry import (
    extract_modules,
    find_project_root,
)

from .architecture_sync_helper import filepath_to_prompt_filename

# --- Issue #617: filename mirrors filepath ---

# Extension (with dot, lowercased) -> PascalCase language for architecture.json
_EXT_TO_LANGUAGE: Dict[str, str] = {
    ".py": "Python",
    ".ts": "TypeScript",
    ".tsx": "TypeScriptReact",
    ".js": "JavaScript",
    ".jsx": "JavaScriptReact",
    ".prisma": "Prisma",
    ".go": "Go",
    ".rs": "Rust",
    ".java": "Java",
    ".rb": "Ruby",
    ".php": "PHP",
    ".swift": "Swift",
    ".kt": "Kotlin",
    ".cs": "C#",
    ".sql": "SQL",
    ".html": "HTML",
    ".css": "CSS",
    ".scala": "Scala",
    ".cpp": "C++",
    ".c": "C",
    ".sh": "Shell",
    ".yaml": "YAML",
    ".yml": "YAML",
    ".json": "JSON",
    ".md": "Markdown",
}


def _language_from_filepath(filepath: str) -> Optional[str]:
    """Infer PascalCase language from output filepath extension (Issue #617).

    Returns None for extensionless files (e.g. Makefile, Dockerfile) so callers
    can skip normalization rather than incorrectly defaulting to Python.
    """
    ext = Path(filepath).suffix.lower()
    if ext and ext.startswith("."):
        return _EXT_TO_LANGUAGE.get(ext, "Python")  # safe default for known-extension files
    return None


def normalize_architecture_filenames(arch_data: List[Dict[str, Any]]) -> None:
    """
    Set each module's filename from filepath so it mirrors directory structure (Issue #617).
    Rewrites each module's dependencies list so they reference the new normalized filenames.
    Mutates arch_data in place. Use after parsing architecture.json from LLM or template.
    """
    old_to_new: Dict[str, str] = {}
    for entry in arch_data:
        filepath = entry.get("filepath")
        if not filepath or not isinstance(filepath, str):
            continue
        old_fn = entry.get("filename") or ""
        language = _language_from_filepath(filepath)
        if language is None:
            # Extensionless file (e.g. Makefile) — leave filename unchanged
            continue
        new_fn = filepath_to_prompt_filename(filepath, language)
        if old_fn:
            old_to_new[old_fn] = new_fn
        entry["filename"] = new_fn
    for entry in arch_data:
        deps = entry.get("dependencies")
        if not isinstance(deps, list):
            continue
        entry["dependencies"] = [old_to_new.get(d, d) for d in deps]

# --- Constants ---
# Use Path.cwd() instead of __file__ so it works with the user's project directory,
# not the PDD package installation directory
ARCHITECTURE_JSON_PATH = Path.cwd() / "architecture.json"
PROMPTS_DIR = Path.cwd() / "prompts"


def _resolve_sync_paths(
    prompts_dir: Optional[Path],
    architecture_path: Optional[Path],
) -> tuple[Path, Path]:
    """Resolve prompts/architecture from the nearest cwd-anchored sync root."""
    cwd = Path.cwd().resolve()

    def resolve_explicit(path: Path) -> Path:
        return path if path.is_absolute() else (cwd / path)

    if prompts_dir is not None:
        resolved_prompts_dir = resolve_explicit(prompts_dir)
    else:
        project_root = find_project_root(cwd)
        current = cwd
        sync_root = project_root

        while True:
            if (current / "architecture.json").exists() or (current / "prompts").exists():
                sync_root = current
                break
            if current == project_root or current.parent == current:
                break
            current = current.parent

        resolved_prompts_dir = sync_root / "prompts"

    if architecture_path is not None:
        return resolved_prompts_dir, resolve_explicit(architecture_path)

    resolved_architecture_path = resolved_prompts_dir.parent / "architecture.json"
    return resolved_prompts_dir, resolved_architecture_path


def _normalize_prompt_filename(filename: str) -> str:
    """Accept prompt-relative paths while storing architecture keys as prompt filenames."""
    normalized = filename.replace("\\", "/").strip()
    if normalized.startswith("./"):
        normalized = normalized[2:]
    if normalized.startswith("prompts/"):
        normalized = normalized[len("prompts/"):]
    return normalized


# --- Tag Extraction ---

def parse_prompt_tags(prompt_content: str) -> Dict[str, Any]:
    """
    Extract PDD metadata tags from prompt content using lxml.

    Extracts the following tags:
    - <pdd-reason>: Brief description of module's purpose
    - <pdd-interface>: JSON interface specification
    - <pdd-dependency>: Module dependencies (multiple tags allowed)

    Args:
        prompt_content: Raw content of .prompt file

    Returns:
        Dict with keys:
        - reason: str | None (single line description)
        - interface: dict | None (parsed JSON interface structure)
        - dependencies: List[str] (prompt filenames, empty if none)

    Lenient behavior:
    - Malformed XML: Returns empty dict without crashing
    - Invalid JSON in interface: Returns None for interface, continues with other fields
    - Missing tags: Returns None/empty for missing fields

    Example:
        >>> content = '''
        ... <pdd-reason>Provides unified LLM invocation</pdd-reason>
        ... <pdd-interface>{"type": "module", "module": {"functions": []}}</pdd-interface>
        ... <pdd-dependency>path_resolution_python.prompt</pdd-dependency>
        ... '''
        >>> result = parse_prompt_tags(content)
        >>> result['reason']
        'Provides unified LLM invocation'
        >>> result['dependencies']
        ['path_resolution_python.prompt']
    """
    result = {
        'reason': None,
        'interface': None,
        'dependencies': [],
        'has_dependency_tags': False,  # Track if <pdd-dependency> tags were present
    }

    try:
        # Only parse the metadata header. Valid prompts may start with leading
        # `%` preamble lines, prompt comments, or XML-style helper tags such as
        # `<include>...` before the real pdd-* tags, so tolerate those. Once we
        # see the first real tag, keep collecting until the first later `%`
        # section marker.
        # If ordinary prose appears before any tag-ish header content, treat the
        # file as having no metadata header so example tags in the body are
        # ignored.
        header_lines = []
        started_header = False
        in_erb_comment = False
        in_xml_comment = False
        for line in prompt_content.splitlines(keepends=True):
            stripped = line.lstrip()
            if not started_header:
                if in_erb_comment:
                    if '--%>' in stripped:
                        in_erb_comment = False
                    continue
                if in_xml_comment:
                    if '-->' in stripped:
                        in_xml_comment = False
                    continue
                if not stripped.strip():
                    if header_lines:
                        header_lines.append(line)
                    continue
                if stripped.startswith('<%--'):
                    in_erb_comment = '--%>' not in stripped
                    continue
                if stripped.startswith('<!--'):
                    in_xml_comment = '-->' not in stripped
                    continue
                if stripped.startswith('%'):
                    continue
                if stripped.startswith('<'):
                    header_lines.append(line)
                    if stripped.startswith('<pdd-'):
                        started_header = True
                    continue
                break

            if stripped.startswith('%'):
                break
            header_lines.append(line)
        header = ''.join(header_lines)

        # Wrap content in root element for XML parsing
        xml_content = f"<root>{header}</root>"

        # Parse with lxml (lenient on encoding)
        parser = etree.XMLParser(recover=True)  # Lenient parser
        root = etree.fromstring(xml_content.encode('utf-8'), parser=parser)

        # Extract <pdd-reason>
        reason_elem = root.find('.//pdd-reason')
        if reason_elem is not None and reason_elem.text:
            result['reason'] = reason_elem.text.strip()

        # Extract <pdd-interface> (parse as JSON)
        interface_elem = root.find('.//pdd-interface')
        if interface_elem is not None and interface_elem.text:
            interface_text = interface_elem.text.strip()
            try:
                # Try parsing as-is first (valid JSON with single braces)
                result['interface'] = json.loads(interface_text)
            except json.JSONDecodeError:
                # Try unescaping double braces (used in LLM prompts for Python .format())
                try:
                    unescaped = interface_text.replace('{{', '{').replace('}}', '}')
                    result['interface'] = json.loads(unescaped)
                except json.JSONDecodeError as e:
                    # Invalid JSON even after unescaping, skip interface field (lenient)
                    result['interface_parse_error'] = f"Invalid JSON in <pdd-interface>: {str(e)}"

        # Extract <pdd-dependency> tags (multiple allowed)
        dep_elems = root.findall('.//pdd-dependency')
        # Track if any dependency tags were present (even if empty)
        # This distinguishes "no tags" (don't update) from "tags removed" (update to empty)
        result['has_dependency_tags'] = len(dep_elems) > 0 or '<pdd-dependency>' in header
        result['dependencies'] = [
            dep
            for elem in dep_elems
            if elem.text
            for dep in [elem.text.strip()]
            if dep and dep.endswith('.prompt') and '\n' not in dep and len(dep) <= 100
        ]

    except (etree.XMLSyntaxError, etree.ParserError):
        # Malformed XML, return empty result (lenient)
        pass

    return result


# --- Auto-rename / Auto-register Helpers ---

def _find_renamed_prompt_file(filename: str, prompts_dir: Path) -> Optional[Path]:
    """
    Find a renamed prompt file when the exact filename doesn't exist.

    Handles the case where a step number has changed, e.g.:
    'agentic_arch_step4_design_LLM.prompt' → 'agentic_arch_step5_design_LLM.prompt'

    Only matches if exactly one candidate file is found (no ambiguity).

    Args:
        filename: Prompt filename that doesn't exist on disk
        prompts_dir: Directory to search for renamed files

    Returns:
        Path to the single matching file, or None if no unique match found
    """
    match = re.match(r'^(.+?_step)\d+(_.*\.prompt)$', Path(filename).name)
    if not match:
        return None
    prefix, suffix = match.group(1), match.group(2)
    name_pattern = re.compile(re.escape(prefix) + r'\d+' + re.escape(suffix))

    # Path-aware: search subdirs and exclude by normalized relative path (Issue #617)
    filename_norm = Path(filename).as_posix()
    candidates = [
        p for p in prompts_dir.rglob('*.prompt')
        if name_pattern.fullmatch(p.name) and p.relative_to(prompts_dir).as_posix() != filename_norm
    ]
    return candidates[0] if len(candidates) == 1 else None


def _infer_filepath(filename: str) -> str:
    """
    Infer output filepath from prompt filename using naming conventions.

    Args:
        filename: Prompt filename (e.g., 'cli_detector_python.prompt')

    Returns:
        Inferred filepath string
    """
    stem = filename[:-len('.prompt')]
    if stem.endswith('_python'):
        module_name = stem[:-len('_python')]
        return f'pdd/{module_name}.py'
    return f'prompts/{filename}'


def _infer_module_tags(filename: str) -> List[str]:
    """
    Infer module tags from prompt filename using naming conventions.

    Args:
        filename: Prompt filename (e.g., 'cli_detector_python.prompt')

    Returns:
        List of tag strings
    """
    if filename.endswith('_python.prompt'):
        return ['module', 'python']
    if filename.endswith('_LLM.prompt'):
        return ['llm']
    return ['module']


def register_untracked_prompts(
    prompts_dir: Path = PROMPTS_DIR,
    architecture_path: Path = ARCHITECTURE_JSON_PATH,
    dry_run: bool = False,
    only_files: Optional[set] = None,
) -> Dict[str, Any]:
    """
    Discover prompt files that have PDD tags but no architecture.json entry,
    and auto-register them with a minimal entry.

    Used as a pre-pass in sync_all_prompts_to_architecture to ensure all
    prompt files with PDD metadata are tracked before validation.

    Args:
        prompts_dir: Directory containing prompt files
        architecture_path: Path to architecture.json
        dry_run: If True, return results without writing to file
        only_files: Optional set of filenames (relative to prompts_dir, as
            POSIX paths — e.g., {"commands/modify_python.prompt"}) to
            restrict which prompts are considered for registration. When
            provided, prompts outside this set are left untouched — even
            if they have valid PDD tags and no arch.json entry. When
            ``None`` (the default), all prompts under ``prompts_dir`` are
            eligible (full-scan behavior, suitable for standalone cleanup
            runs). In-workflow callers (e.g., ``agentic_change_orchestrator``
            Step 10) should pass a narrow set containing only the prompts
            touched by the current workflow, so a single ``pdd change`` run
            cannot silently sweep unrelated repo-wide drift into the PR.

    Returns:
        Dict with keys:
        - registered: List[str] (filenames added to architecture.json)
        - skipped: List[str] (filenames without PDD tags, or filtered out
          by ``only_files`` scope)
        - errors: List[str] (error messages)
    """
    if not architecture_path.exists():
        return {'registered': [], 'skipped': [], 'errors': ['Architecture file not found']}

    raw_arch = json.loads(architecture_path.read_text(encoding='utf-8'))
    arch_data = extract_modules(raw_arch)
    existing_filenames = {m.get('filename') for m in arch_data}
    max_priority = max((m.get('priority', 0) for m in arch_data), default=0)

    registered = []
    skipped = []
    errors = []

    for prompt_file in sorted(prompts_dir.rglob('*.prompt')):
        try:
            filename = prompt_file.relative_to(prompts_dir).as_posix()
        except ValueError:
            continue
        if filename in existing_filenames:
            continue

        # Scope gate: if only_files is provided, skip prompts outside the
        # workflow's scope so an in-workflow call cannot silently register
        # unrelated drift.
        if only_files is not None and filename not in only_files:
            skipped.append(filename)
            continue

        content = prompt_file.read_text(encoding='utf-8')
        tags = parse_prompt_tags(content)

        if not (tags['reason'] or tags['interface'] or tags.get('has_dependency_tags')):
            skipped.append(filename)
            continue

        filepath = _infer_filepath(filename)
        module_tags = _infer_module_tags(filename)
        reason = tags['reason'] or f'Auto-registered module: {filename}'

        max_priority += 1
        entry = {
            'reason': reason,
            'description': reason,
            'dependencies': tags['dependencies'],
            'priority': max_priority,
            'filename': filename,
            'filepath': filepath,
            'tags': module_tags,
            'interface': tags['interface'] or {'type': 'module'},
        }
        arch_data.append(entry)
        existing_filenames.add(filename)
        registered.append(filename)

    if registered and not dry_run:
        if isinstance(raw_arch, dict) and isinstance(raw_arch.get("modules"), list):
            raw_arch["modules"] = arch_data
            write_data = raw_arch
        else:
            write_data = arch_data
        architecture_path.write_text(
            json.dumps(write_data, indent=2, ensure_ascii=False) + '\n',
            encoding='utf-8'
        )

    return {'registered': registered, 'skipped': skipped, 'errors': errors}


# --- Architecture Update ---

def _format_signature_param(
    arg_node: ast.arg,
    default_node: Optional[ast.expr] = None,
    *,
    prefix: str = '',
) -> str:
    """Render a single parsed Python parameter back to a signature fragment."""
    text = f"{prefix}{arg_node.arg}"
    if arg_node.annotation is not None:
        text += f": {ast.unparse(arg_node.annotation)}"
    if default_node is not None:
        text += f" = {ast.unparse(default_node)}"
    return text


def _parse_signature_parameters(signature: str) -> Optional[Dict[str, Any]]:
    """Parse a Python signature string into ordered parameter and style metadata."""
    signature = signature.strip()
    try:
        if signature.startswith('def ') or signature.startswith('async def '):
            func_def = ast.parse(f"{signature}: pass").body[0]
            style = 'full'
        else:
            func_def = ast.parse(f"def _pdd_sync{signature}: pass").body[0]
            style = 'bare'
    except SyntaxError:
        return None

    if not isinstance(func_def, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None

    args = func_def.args
    parameters: List[Dict[str, str]] = []

    positional = list(args.posonlyargs) + list(args.args)
    defaults = [None] * (len(positional) - len(args.defaults)) + list(args.defaults)

    for index, arg_node in enumerate(args.posonlyargs):
        parameters.append({
            'name': arg_node.arg,
            'kind': 'posonly',
            'text': _format_signature_param(arg_node, defaults[index]),
        })

    offset = len(args.posonlyargs)
    for rel_index, arg_node in enumerate(args.args):
        parameters.append({
            'name': arg_node.arg,
            'kind': 'arg',
            'text': _format_signature_param(arg_node, defaults[offset + rel_index]),
        })

    if args.vararg is not None:
        parameters.append({
            'name': args.vararg.arg,
            'kind': 'vararg',
            'text': _format_signature_param(args.vararg, prefix='*'),
        })

    for arg_node, default_node in zip(args.kwonlyargs, args.kw_defaults):
        parameters.append({
            'name': arg_node.arg,
            'kind': 'kwonly',
            'text': _format_signature_param(arg_node, default_node),
        })

    if args.kwarg is not None:
        parameters.append({
            'name': args.kwarg.arg,
            'kind': 'kwarg',
            'text': _format_signature_param(args.kwarg, prefix='**'),
        })

    return {
        'parameters': parameters,
        'return_annotation': ast.unparse(func_def.returns) if func_def.returns is not None else None,
        'style': style,
        'is_async': isinstance(func_def, ast.AsyncFunctionDef),
        'name': func_def.name,
    }


def _build_signature_from_parameters(
    parameters: List[Dict[str, str]],
    signature_info: Dict[str, Any],
    function_name: str,
) -> str:
    """Serialize ordered parameter metadata back to a Python signature string."""
    posonly = [p['text'] for p in parameters if p['kind'] == 'posonly']
    args = [p['text'] for p in parameters if p['kind'] == 'arg']
    vararg = next((p['text'] for p in parameters if p['kind'] == 'vararg'), None)
    kwonly = [p['text'] for p in parameters if p['kind'] == 'kwonly']
    kwarg = next((p['text'] for p in parameters if p['kind'] == 'kwarg'), None)

    pieces: List[str] = []
    pieces.extend(posonly)
    if posonly:
        pieces.append('/')
    pieces.extend(args)
    if vararg is not None:
        pieces.append(vararg)
    elif kwonly:
        pieces.append('*')
    pieces.extend(kwonly)
    if kwarg is not None:
        pieces.append(kwarg)

    signature = f"({', '.join(pieces)})"
    if signature_info.get('return_annotation'):
        signature += f" -> {signature_info['return_annotation']}"

    if signature_info.get('style') == 'full':
        prefix = 'async def' if signature_info.get('is_async') else 'def'
        name = signature_info.get('name') or function_name
        return f"{prefix} {name}{signature}"
    return signature


def _merge_function_signature(
    old_signature: str,
    new_signature: str,
    function_name: str,
) -> tuple[str, List[str]]:
    """Merge a new function signature with the existing one, preserving old params."""
    old_info = _parse_signature_parameters(old_signature)
    new_info = _parse_signature_parameters(new_signature)
    if new_info is None and old_info is not None:
        return old_signature, [
            f"Kept existing signature for function '{function_name}' because the new signature could not be parsed during interface merge."
        ]
    if old_info is None and new_info is not None:
        return new_signature, [
            f"Used new signature for function '{function_name}' without merge because the existing signature could not be parsed."
        ]
    if old_info is None and new_info is None:
        return new_signature, [
            f"Used new signature for function '{function_name}' because neither signature could be parsed for merge."
        ]

    old_params = old_info['parameters']
    new_params = new_info['parameters']

    old_by_name = {param['name']: param for param in old_params}
    new_by_name = {param['name']: param for param in new_params}

    # Guard: reject merge when signatures are from completely different classes.
    # If the only shared parameter names are common ones like 'self'/'cls',
    # the new signature is likely from a different class entirely (LLM error).
    trivial_params = {'self', 'cls'}
    old_names = {p['name'] for p in old_params} - trivial_params
    new_names = {p['name'] for p in new_params} - trivial_params
    if old_names and new_names and not (old_names & new_names):
        return old_signature, [
            f"Rejected incompatible signature for function '{function_name}': "
            f"old params {sorted(old_names)} share no names with new params {sorted(new_names)}. "
            f"Keeping existing signature to prevent cross-class contamination."
        ]

    dropped = [param['name'] for param in old_params if param['name'] not in new_by_name]
    if not dropped:
        return new_signature, []

    merged_order = [param['name'] for param in old_params]
    merged_order.extend(
        param['name']
        for param in new_params
        if param['name'] not in old_by_name
    )

    merged_params = [
        new_by_name[name] if name in new_by_name else old_by_name[name]
        for name in merged_order
    ]
    warnings = [
        f"Preserved existing parameter '{name}' in function '{function_name}' while merging interface signature."
        for name in dropped
    ]
    merged_signature_info = dict(new_info)
    if not merged_signature_info.get('return_annotation'):
        merged_signature_info['return_annotation'] = old_info.get('return_annotation')
    return _build_signature_from_parameters(
        merged_params,
        merged_signature_info,
        function_name,
    ), warnings


def _merge_interface_signatures(
    old_interface: Optional[Dict[str, Any]],
    new_interface: Dict[str, Any],
) -> tuple[Dict[str, Any], List[str]]:
    """Merge module function signatures while leaving the new interface authoritative."""
    if (
        not isinstance(old_interface, dict)
        or old_interface.get('type') != 'module'
        or new_interface.get('type') != 'module'
    ):
        return new_interface, []

    old_module = old_interface.get('module')
    new_module = new_interface.get('module')
    if not isinstance(old_module, dict) or not isinstance(new_module, dict):
        return new_interface, []

    old_functions = old_module.get('functions')
    new_functions = new_module.get('functions')
    if not isinstance(old_functions, list) or not isinstance(new_functions, list):
        return new_interface, []

    old_by_name = {
        func.get('name'): func
        for func in old_functions
        if isinstance(func, dict) and func.get('name')
    }

    merged_functions: List[Dict[str, Any]] = []
    warnings: List[str] = []

    for func in new_functions:
        if not isinstance(func, dict):
            merged_functions.append(func)
            continue

        func_name = func.get('name')
        old_func = old_by_name.get(func_name)
        if (
            func_name
            and old_func is not None
            and isinstance(old_func, dict)
            and isinstance(old_func.get('signature'), str)
            and isinstance(func.get('signature'), str)
        ):
            merged_func = dict(func)
            merged_signature, merge_warnings = _merge_function_signature(
                old_func['signature'],
                func['signature'],
                func_name,
            )
            merged_func['signature'] = merged_signature
            warnings.extend(merge_warnings)
            merged_functions.append(merged_func)
            continue

        merged_functions.append(func)

    merged_interface = json.loads(json.dumps(new_interface))
    merged_interface['module']['functions'] = merged_functions
    return merged_interface, warnings

def update_architecture_from_prompt(
    prompt_filename: str,
    prompts_dir: Path = PROMPTS_DIR,
    architecture_path: Path = ARCHITECTURE_JSON_PATH,
    dry_run: bool = False
) -> Dict[str, Any]:
    """
    Update a single architecture.json entry from its prompt file tags.

    This function:
    1. Reads the prompt file and extracts PDD metadata tags
    2. Loads architecture.json and finds the matching module entry
    3. Updates only fields that have tags present (lenient)
    4. Tracks changes for diff display
    5. Writes back to architecture.json (unless dry_run=True)

    Args:
        prompt_filename: Name of prompt file (e.g., "llm_invoke_python.prompt")
        prompts_dir: Directory containing prompt files (default: ./prompts/)
        architecture_path: Path to architecture.json (default: ./architecture.json)
        dry_run: If True, return changes without writing to file

    Returns:
        Dict with keys:
        - success: bool (True if operation succeeded)
        - updated: bool (True if any fields changed)
        - changes: Dict mapping field names to {'old': ..., 'new': ...}
        - error: Optional[str] (error message if success=False)

    Example:
        >>> result = update_architecture_from_prompt("llm_invoke_python.prompt")
        >>> if result['success'] and result['updated']:
        ...     print(f"Updated fields: {list(result['changes'].keys())}")
        Updated fields: ['reason', 'dependencies']
    """
    try:
        # 1. Read prompt file
        prompt_path = prompts_dir / prompt_filename
        preloaded_arch_data = None  # Set when arch_data is loaded during rename
        if not prompt_path.exists():
            renamed_path = _find_renamed_prompt_file(prompt_filename, prompts_dir)
            if renamed_path is None:
                return {
                    'success': False,
                    'updated': False,
                    'changes': {},
                    'error': f'Prompt file not found: {prompt_filename}'
                }
            # Auto-update architecture.json entry to use the found filename (path-aware for #617)
            new_filename = renamed_path.relative_to(prompts_dir).as_posix()
            if not architecture_path.exists():
                return {
                    'success': False,
                    'updated': False,
                    'changes': {},
                    'error': f'Architecture file not found: {architecture_path}'
                }
            raw_rename = json.loads(architecture_path.read_text(encoding='utf-8'))
            arch_data_for_rename = extract_modules(raw_rename)
            for mod in arch_data_for_rename:
                if mod.get('filename') == prompt_filename:
                    old_filepath = mod.get('filepath', '')
                    if old_filepath == f'prompts/{prompt_filename}':
                        mod['filepath'] = f'prompts/{new_filename}'
                    mod['filename'] = new_filename
                    if not dry_run:
                        if isinstance(raw_rename, dict) and isinstance(raw_rename.get("modules"), list):
                            raw_rename["modules"] = arch_data_for_rename
                            rename_write = raw_rename
                        else:
                            rename_write = arch_data_for_rename
                        architecture_path.write_text(
                            json.dumps(rename_write, indent=2, ensure_ascii=False) + '\n',
                            encoding='utf-8'
                        )
                    prompt_filename = new_filename
                    prompt_path = renamed_path
                    # Keep the already-modified in-memory data to avoid re-loading from disk
                    preloaded_arch_data = arch_data_for_rename
                    break
            else:
                return {
                    'success': False,
                    'updated': False,
                    'changes': {},
                    'error': f'Prompt file not found: {prompt_filename}'
                }

        prompt_content = prompt_path.read_text(encoding='utf-8')

        # 2. Extract tags
        tags = parse_prompt_tags(prompt_content)

        # 3. Load architecture.json (reuse preloaded data if available from rename step)
        if preloaded_arch_data is not None:
            arch_data = preloaded_arch_data
        else:
            if not architecture_path.exists():
                return {
                    'success': False,
                    'updated': False,
                    'changes': {},
                    'error': f'Architecture file not found: {architecture_path}'
                }
            arch_data = extract_modules(json.loads(architecture_path.read_text(encoding='utf-8')))

        # 4. Find matching module by filename
        module_entry = None
        module_index = None
        for i, mod in enumerate(arch_data):
            if mod.get('filename') == prompt_filename:
                module_entry = mod
                module_index = i
                break

        if module_entry is None:
            return {
                'success': False,
                'updated': False,
                'changes': {},
                'error': f'No architecture entry found for: {prompt_filename}'
            }

        # 5. Track changes (only update fields with tags present - lenient)
        changes = {}
        updated = False
        warnings = []

        # Update reason if tag present
        if tags['reason'] is not None:
            old_reason = module_entry.get('reason')
            if old_reason != tags['reason']:
                changes['reason'] = {'old': old_reason, 'new': tags['reason']}
                module_entry['reason'] = tags['reason']
                updated = True

        # Update interface if tag present
        if tags['interface'] is not None:
            old_interface = module_entry.get('interface')
            merged_interface, merge_warnings = _merge_interface_signatures(
                old_interface,
                tags['interface'],
            )
            warnings.extend(merge_warnings)
            if old_interface != merged_interface:
                changes['interface'] = {'old': old_interface, 'new': merged_interface}
                module_entry['interface'] = merged_interface
                updated = True

        # Update dependencies only when <pdd-dependency> metadata is present in the prompt.
        # Reason/interface-only updates must not clear architecture.json dependencies (those may
        # still reflect include-based or manually curated edges).
        # Empty <pdd-dependency></pdd-dependency> still counts (has_dependency_tags) and clears deps.
        should_update_deps = (
            tags.get('has_dependency_tags', False) or bool(tags['dependencies'])
        )
        if should_update_deps:
            old_deps = module_entry.get('dependencies', [])
            # Compare as sets to detect changes (order-independent)
            if set(old_deps) != set(tags['dependencies']):
                changes['dependencies'] = {'old': old_deps, 'new': tags['dependencies']}
                module_entry['dependencies'] = tags['dependencies']
                updated = True

        # 6. Write back to architecture.json (if updated and not dry run)
        if updated and not dry_run:
            arch_data[module_index] = module_entry
            raw_on_disk = json.loads(architecture_path.read_text(encoding='utf-8'))
            if isinstance(raw_on_disk, dict) and isinstance(raw_on_disk.get("modules"), list):
                raw_on_disk["modules"] = arch_data
                write_data = raw_on_disk
            else:
                write_data = arch_data
            architecture_path.write_text(
                json.dumps(write_data, indent=2, ensure_ascii=False) + '\n',
                encoding='utf-8'
            )

        # Include any parse warnings
        if tags.get('interface_parse_error'):
            warnings.append(tags['interface_parse_error'])

        return {
            'success': True,
            'updated': updated,
            'changes': changes,
            'error': None,
            'warnings': warnings
        }

    except Exception as e:
        return {
            'success': False,
            'updated': False,
            'changes': {},
            'error': f'Unexpected error: {str(e)}'
        }


def sync_all_prompts_to_architecture(
    prompts_dir: Path = PROMPTS_DIR,
    architecture_path: Path = ARCHITECTURE_JSON_PATH,
    dry_run: bool = False
) -> Dict[str, Any]:
    """
    Sync ALL prompt files to architecture.json.

    Iterates through all modules in architecture.json and updates each from
    its corresponding prompt file (if it exists and has tags).

    Args:
        prompts_dir: Directory containing prompt files
        architecture_path: Path to architecture.json
        dry_run: If True, perform validation without writing changes

    Returns:
        Dict with keys:
        - success: bool (True if no errors occurred)
        - updated_count: int (number of modules updated)
        - skipped_count: int (number of modules without prompt files)
        - results: List[Dict] (detailed results for each module)
        - errors: List[str] (error messages)

    Example:
        >>> result = sync_all_prompts_to_architecture(dry_run=True)
        >>> print(f"Would update {result['updated_count']} modules")
        Would update 15 modules
    """
    # Pre-pass: auto-register any prompt files with PDD tags not in architecture.json
    reg_result = register_untracked_prompts(prompts_dir, architecture_path, dry_run)

    # Load architecture.json to get all prompt filenames
    if not architecture_path.exists():
        return {
            'success': False,
            'updated_count': 0,
            'skipped_count': 0,
            'results': [],
            'errors': [f'Architecture file not found: {architecture_path}'],
            'registered': reg_result['registered'],
        }

    arch_data = extract_modules(json.loads(architecture_path.read_text(encoding='utf-8')))

    results = []
    errors = []
    updated_count = 0
    skipped_count = 0

    for module in arch_data:
        filename = module.get('filename')

        # Skip entries without filename or non-prompt files
        if not filename or not filename.endswith('.prompt'):
            skipped_count += 1
            continue

        # Update from prompt
        result = update_architecture_from_prompt(
            filename,
            prompts_dir,
            architecture_path,
            dry_run
        )

        # Track statistics
        if result['success'] and result['updated']:
            updated_count += 1
        elif not result['success']:
            errors.append(f"{filename}: {result['error']}")

        # Store detailed result
        results.append({
            'filename': filename,
            'success': result['success'],
            'updated': result['updated'],
            'changes': result['changes'],
            'error': result.get('error')
        })

    return {
        'success': len(errors) == 0,
        'updated_count': updated_count,
        'skipped_count': skipped_count,
        'results': results,
        'errors': errors,
        'registered': reg_result['registered'],
    }


def _detect_circular_dependencies(modules: List[Dict[str, Any]]) -> List[List[str]]:
    """Detect circular dependencies using DFS over prompt filenames."""
    graph: Dict[str, set[str]] = {}
    all_filenames: set[str] = set()

    for module in modules:
        filename = module.get("filename")
        if not filename:
            continue
        all_filenames.add(filename)
        dependencies = module.get("dependencies", [])
        if isinstance(dependencies, list):
            graph[filename] = {dep for dep in dependencies if isinstance(dep, str)}
        else:
            graph[filename] = set()

    cycles: List[List[str]] = []
    visited: set[str] = set()
    rec_stack: set[str] = set()

    def dfs(node: str, path: List[str]) -> None:
        if node in rec_stack:
            try:
                cycle_start = path.index(node)
                cycles.append(path[cycle_start:] + [node])
            except ValueError:
                pass
            return

        if node in visited or node not in graph:
            return

        visited.add(node)
        rec_stack.add(node)
        path.append(node)

        for dependency in graph.get(node, set()):
            if dependency in all_filenames:
                dfs(dependency, path)

        path.pop()
        rec_stack.remove(node)

    for filename in all_filenames:
        if filename not in visited:
            dfs(filename, [])

    return cycles


def validate_architecture_modules(modules: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Validate architecture modules and return route-compatible result dicts."""
    errors: List[Dict[str, Any]] = []
    warnings: List[Dict[str, Any]] = []

    all_filenames = {
        module.get("filename")
        for module in modules
        if isinstance(module.get("filename"), str) and module.get("filename")
    }

    for cycle in _detect_circular_dependencies(modules):
        errors.append(
            {
                "type": "circular_dependency",
                "message": f"Circular dependency detected: {' -> '.join(cycle)}",
                "modules": cycle,
            }
        )

    for module in modules:
        filename = module.get("filename", "")
        dependencies = module.get("dependencies", [])
        if not isinstance(dependencies, list):
            dependencies = []

        for dependency in dependencies:
            if dependency not in all_filenames:
                errors.append(
                    {
                        "type": "missing_dependency",
                        "message": (
                            f"Module '{filename}' depends on non-existent module "
                            f"'{dependency}'"
                        ),
                        "modules": [filename, dependency],
                    }
                )

        if not isinstance(filename, str) or not filename.strip():
            errors.append(
                {
                    "type": "invalid_field",
                    "message": "Module has empty filename",
                    "modules": [filename or "(unnamed)"],
                }
            )

        filepath = module.get("filepath", "")
        if not isinstance(filepath, str) or not filepath.strip():
            errors.append(
                {
                    "type": "invalid_field",
                    "message": f"Module '{filename}' has empty filepath",
                    "modules": [filename or "(unnamed)"],
                }
            )

        description = module.get("description", "")
        if not isinstance(description, str) or not description.strip():
            errors.append(
                {
                    "type": "invalid_field",
                    "message": f"Module '{filename}' has empty description",
                    "modules": [filename or "(unnamed)"],
                }
            )

        if len(dependencies) != len(set(dependencies)):
            seen: set[str] = set()
            duplicates: List[str] = []
            for dependency in dependencies:
                if dependency in seen:
                    duplicates.append(dependency)
                seen.add(dependency)
            warnings.append(
                {
                    "type": "duplicate_dependency",
                    "message": (
                        f"Module '{filename}' has duplicate dependencies: "
                        f"{', '.join(duplicates)}"
                    ),
                    "modules": [filename],
                }
            )

    depended_upon: set[str] = set()
    for module in modules:
        dependencies = module.get("dependencies", [])
        if isinstance(dependencies, list):
            depended_upon.update(dep for dep in dependencies if isinstance(dep, str))

    for module in modules:
        filename = module.get("filename", "")
        dependencies = module.get("dependencies", [])
        if isinstance(dependencies, list) and not dependencies and filename not in depended_upon:
            warnings.append(
                {
                    "type": "orphan_module",
                    "message": (
                        f"Module '{filename}' has no dependencies and is not depended upon "
                        "by any other module"
                    ),
                    "modules": [filename],
                }
            )

    return {
        "valid": len(errors) == 0,
        "errors": errors,
        "warnings": warnings,
    }


def sync_prompts_to_architecture(
    filenames: Optional[List[str]] = None,
    prompts_dir: Optional[Path] = None,
    architecture_path: Optional[Path] = None,
    dry_run: bool = False,
) -> Dict[str, Any]:
    """Shared architecture sync entry point used by the CLI and connect UI."""
    resolved_prompts_dir, resolved_architecture_path = _resolve_sync_paths(
        prompts_dir,
        architecture_path,
    )

    try:
        if filenames is None:
            sync_result = sync_all_prompts_to_architecture(
                prompts_dir=resolved_prompts_dir,
                architecture_path=resolved_architecture_path,
                dry_run=dry_run,
            )
        else:
            results = []
            updated_count = 0
            errors: List[str] = []

            for filename in filenames:
                normalized_filename = _normalize_prompt_filename(filename)
                result = update_architecture_from_prompt(
                    normalized_filename,
                    prompts_dir=resolved_prompts_dir,
                    architecture_path=resolved_architecture_path,
                    dry_run=dry_run,
                )
                results.append(
                    {
                        "filename": normalized_filename,
                        "success": result["success"],
                        "updated": result["updated"],
                        "changes": result["changes"],
                        "error": result.get("error"),
                    }
                )
                if result["success"] and result["updated"]:
                    updated_count += 1
                elif not result["success"]:
                    errors.append(f"{normalized_filename}: {result['error']}")

            sync_result = {
                "success": len(errors) == 0,
                "updated_count": updated_count,
                "skipped_count": 0,
                "results": results,
                "errors": errors,
            }

        if resolved_architecture_path.exists():
            arch_data = extract_modules(
                json.loads(resolved_architecture_path.read_text(encoding="utf-8"))
            )
            validation = validate_architecture_modules(arch_data)
        else:
            validation = {"valid": True, "errors": [], "warnings": []}

        return {
            "success": sync_result["success"] and validation["valid"],
            "updated_count": sync_result["updated_count"],
            "skipped_count": sync_result.get("skipped_count", 0),
            "results": sync_result["results"],
            "validation": validation,
            "errors": sync_result.get("errors", []),
        }
    except Exception as exc:
        return {
            "success": False,
            "updated_count": 0,
            "skipped_count": 0,
            "results": [],
            "validation": {"valid": True, "errors": [], "warnings": []},
            "errors": [f"Unexpected error: {exc}"],
        }


# --- Validation ---

def validate_dependencies(
    dependencies: List[str],
    prompts_dir: Path = PROMPTS_DIR
) -> Dict[str, Any]:
    """
    Validate dependency list for a module.

    Checks:
    1. All referenced prompt files exist in prompts_dir
    2. No duplicate dependencies

    Args:
        dependencies: List of prompt filenames (e.g., ["llm_invoke_python.prompt"])
        prompts_dir: Directory to check for prompt file existence

    Returns:
        Dict with keys:
        - valid: bool (True if all validations pass)
        - missing: List[str] (prompt files that don't exist)
        - duplicates: List[str] (duplicate entries)

    Example:
        >>> deps = ["llm_invoke_python.prompt", "missing.prompt"]
        >>> result = validate_dependencies(deps)
        >>> result['valid']
        False
        >>> result['missing']
        ['missing.prompt']
    """
    missing = []
    duplicates = []

    # Check for missing files
    for dep in dependencies:
        dep_path = prompts_dir / dep
        if not dep_path.exists():
            missing.append(dep)

    # Check for duplicates
    seen = set()
    for dep in dependencies:
        if dep in seen:
            if dep not in duplicates:  # Avoid duplicate duplicates
                duplicates.append(dep)
        seen.add(dep)

    return {
        'valid': len(missing) == 0 and len(duplicates) == 0,
        'missing': missing,
        'duplicates': duplicates
    }


def validate_interface_structure(interface: Dict[str, Any]) -> Dict[str, Any]:
    """
    Validate interface JSON structure.

    Interface must have:
    - 'type' field with value: 'module' | 'cli' | 'command' | 'frontend'
    - Corresponding nested object with appropriate structure

    Args:
        interface: Parsed interface JSON dict

    Returns:
        Dict with keys:
        - valid: bool (True if structure is valid)
        - errors: List[str] (validation error messages)

    Example:
        >>> interface = {"type": "module", "module": {"functions": []}}
        >>> result = validate_interface_structure(interface)
        >>> result['valid']
        True
    """
    errors = []

    if not isinstance(interface, dict):
        return {'valid': False, 'errors': ['Interface must be a JSON object']}

    # Check type field
    itype = interface.get('type')
    if itype not in ['module', 'cli', 'command', 'frontend']:
        errors.append(f"Invalid type: '{itype}'. Must be: module, cli, command, or frontend")
        return {'valid': False, 'errors': errors}

    # Check corresponding nested key exists
    if itype not in interface:
        errors.append(f"Missing '{itype}' key for type='{itype}'")
        return {'valid': False, 'errors': errors}

    # Type-specific validation
    nested_obj = interface[itype]
    if not isinstance(nested_obj, dict):
        errors.append(f"'{itype}' must be an object")

    if itype == 'module':
        if 'functions' not in nested_obj:
            errors.append("module.functions is required")
    elif itype in ['cli', 'command']:
        if 'commands' not in nested_obj:
            errors.append(f"{itype}.commands is required")
    elif itype == 'frontend':
        if 'pages' not in nested_obj:
            errors.append("frontend.pages is required")

    return {
        'valid': len(errors) == 0,
        'errors': errors
    }


# --- Helper Functions for Reverse Direction (architecture.json → prompt) ---

def get_architecture_entry_for_prompt(
    prompt_filename: str,
    architecture_path: Path = ARCHITECTURE_JSON_PATH
) -> Optional[Dict[str, Any]]:
    """
    Load architecture entry matching a prompt filename.

    Args:
        prompt_filename: Name of prompt file (e.g., "llm_invoke_python.prompt")
        architecture_path: Path to architecture.json

    Returns:
        Architecture entry dict or None if not found

    Example:
        >>> entry = get_architecture_entry_for_prompt("llm_invoke_python.prompt")
        >>> entry['reason']
        'Provides unified LLM invocation across all PDD operations.'
    """
    if not architecture_path.exists():
        return None

    arch_data = extract_modules(json.loads(architecture_path.read_text(encoding='utf-8')))

    # Normalize to forward-slash path for comparison (Issue #617: filename may include subdirs)
    normalized = Path(prompt_filename).as_posix()
    if normalized.startswith('./'):
        normalized = normalized[2:]

    # Exact path match first
    for entry in arch_data:
        if entry.get('filename') == normalized:
            return entry

    # Basename fallback: call sites may pass just the filename without subdirectory
    basename = Path(normalized).name
    candidates = [e for e in arch_data if Path(e.get('filename', '')).name == basename]
    if len(candidates) == 1:
        return candidates[0]

    return None


def has_pdd_tags(prompt_content: str) -> bool:
    """
    Check if prompt already has PDD metadata tags.

    Used to preserve manual edits - don't inject tags if they already exist.

    Args:
        prompt_content: Raw prompt file content

    Returns:
        True if any PDD tags are present

    Example:
        >>> has_pdd_tags("<pdd-reason>Test</pdd-reason>")
        True
        >>> has_pdd_tags("No tags here")
        False
    """
    return (
        '<pdd-reason>' in prompt_content or
        '<pdd-interface>' in prompt_content or
        '<pdd-dependency>' in prompt_content
    )


def generate_tags_from_architecture(arch_entry: Dict[str, Any]) -> str:
    """
    Generate XML tags string from architecture entry.

    Used when generating new prompts - inject tags from architecture.json.

    Args:
        arch_entry: Architecture.json module entry

    Returns:
        XML tags as string (ready to prepend to prompt)

    Example:
        >>> entry = {"reason": "Test module", "dependencies": ["dep.prompt"]}
        >>> tags = generate_tags_from_architecture(entry)
        >>> print(tags)
        <pdd-reason>Test module</pdd-reason>
        <pdd-dependency>dep.prompt</pdd-dependency>
    """
    tags = []

    # Generate <pdd-reason> tag
    if arch_entry.get('reason'):
        reason = arch_entry['reason']
        tags.append(f"<pdd-reason>{reason}</pdd-reason>")

    # Generate <pdd-interface> tag (pretty-printed JSON)
    if arch_entry.get('interface'):
        interface_json = json.dumps(arch_entry['interface'], indent=2)
        tags.append(f"<pdd-interface>\n{interface_json}\n</pdd-interface>")

    # Generate <pdd-dependency> tags (one per dependency)
    for dep in arch_entry.get('dependencies', []):
        tags.append(f"<pdd-dependency>{dep}</pdd-dependency>")

    return '\n'.join(tags)
