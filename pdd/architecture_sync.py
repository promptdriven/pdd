"""
Architecture sync module for bidirectional sync between architecture.json and prompt files.

This module provides functionality to:
1. Parse PDD metadata tags (<pdd-reason>, <pdd-interface>, <pdd-dependency>) from prompt files
2. Update architecture.json from prompt file tags (prompt → architecture.json)
3. Validate dependencies and detect issues

Philosophy: Prompts are the source of truth, architecture.json is derived from prompts.
Validation: Lenient - missing tags are OK, only update fields that have tags present.
"""

import json
from pathlib import Path
from typing import Any, Dict, List, Optional

from lxml import etree


# --- Constants ---
# Use Path.cwd() instead of __file__ so it works with the user's project directory,
# not the PDD package installation directory
ARCHITECTURE_JSON_PATH = Path.cwd() / "architecture.json"
PROMPTS_DIR = Path.cwd() / "prompts"


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
        # Wrap content in root element for XML parsing
        # Replace CDATA markers if present to handle JSON with special chars
        xml_content = f"<root>{prompt_content}</root>"

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
        result['has_dependency_tags'] = len(dep_elems) > 0 or '<pdd-dependency>' in prompt_content
        result['dependencies'] = [
            elem.text.strip()
            for elem in dep_elems
            if elem.text and elem.text.strip()
        ]

    except (etree.XMLSyntaxError, etree.ParserError):
        # Malformed XML, return empty result (lenient)
        pass

    return result


# --- Architecture Update ---

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
        if not prompt_path.exists():
            return {
                'success': False,
                'updated': False,
                'changes': {},
                'error': f'Prompt file not found: {prompt_filename}'
            }

        prompt_content = prompt_path.read_text(encoding='utf-8')

        # 2. Extract tags
        tags = parse_prompt_tags(prompt_content)

        # 3. Load architecture.json
        if not architecture_path.exists():
            return {
                'success': False,
                'updated': False,
                'changes': {},
                'error': f'Architecture file not found: {architecture_path}'
            }

        arch_data = json.loads(architecture_path.read_text(encoding='utf-8'))

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

        # Check if prompt has ANY PDD tags (used to determine if dependencies should be cleared)
        has_any_pdd_tags = (
            tags['reason'] is not None or
            tags['interface'] is not None or
            tags.get('has_dependency_tags', False) or
            tags['dependencies']
        )

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
            if old_interface != tags['interface']:
                changes['interface'] = {'old': old_interface, 'new': tags['interface']}
                module_entry['interface'] = tags['interface']
                updated = True

        # Update dependencies if:
        # 1. Dependency tags were present in the prompt (even if empty), OR
        # 2. Prompt has OTHER pdd tags (reason/interface) but no dependency tags = clear dependencies
        # This ensures removing all <pdd-dependency> tags will clear dependencies in architecture.json
        should_update_deps = (
            tags.get('has_dependency_tags', False) or  # Has dependency tags (even if empty)
            tags['dependencies'] or  # Has dependencies
            has_any_pdd_tags  # Has any PDD tags = manage all fields including deps
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
            architecture_path.write_text(
                json.dumps(arch_data, indent=2, ensure_ascii=False) + '\n',
                encoding='utf-8'
            )

        # Include any parse warnings
        warnings = []
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
    # Load architecture.json to get all prompt filenames
    if not architecture_path.exists():
        return {
            'success': False,
            'updated_count': 0,
            'skipped_count': 0,
            'results': [],
            'errors': [f'Architecture file not found: {architecture_path}']
        }

    arch_data = json.loads(architecture_path.read_text(encoding='utf-8'))

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
        'errors': errors
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

    arch_data = json.loads(architecture_path.read_text(encoding='utf-8'))

    # Extract just filename if full path provided
    filename = Path(prompt_filename).name

    for entry in arch_data:
        if entry.get('filename') == filename:
            return entry

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
