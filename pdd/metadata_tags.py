from __future__ import annotations

import difflib
import hashlib
import json
import re
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from rich.console import Console
from rich.table import Table

from .architecture_sync import (
    has_pdd_tags,
    generate_tags_from_architecture,
    validate_interface_structure,
    get_architecture_entry_for_prompt,
)

console = Console()

# Regex patterns for extracting existing tags
_REASON_RE = re.compile(r"<pdd-reason>(.*?)</pdd-reason>", re.DOTALL)
_INTERFACE_RE = re.compile(r"<pdd-interface>(.*?)</pdd-interface>", re.DOTALL)
_DEPENDENCY_RE = re.compile(r"<pdd-dependency>(.*?)</pdd-dependency>", re.DOTALL)
_ANY_PDD_TAG_RE = re.compile(
    r"<pdd-(?:reason|interface|dependency)>.*?</pdd-(?:reason|interface|dependency)>",
    re.DOTALL,
)

_LANGUAGE_TO_SUFFIX = {
    "python": ".py",
    "javascript": ".js",
    "typescript": ".ts",
    "java": ".java",
    "go": ".go",
    "rust": ".rs",
    "cpp": ".cpp",
    "c": ".c",
    "ruby": ".rb",
    "bash": ".sh",
    "shell": ".sh",
}


def _infer_code_path(prompt_path: Path) -> Optional[Path]:
    """Infer the code file path from a prompt path using BASENAME_LANGUAGE.prompt convention."""
    name = prompt_path.stem  # strip .prompt
    if "_" not in name:
        return None
    basename, language = name.rsplit("_", 1)
    suffix = _LANGUAGE_TO_SUFFIX.get(language.lower())
    if not suffix:
        return None
    # PDD convention: pdd/<basename><suffix>
    candidates = [
        prompt_path.parent.parent / "pdd" / f"{basename}{suffix}",
        prompt_path.parent / f"{basename}{suffix}",
        Path("pdd") / f"{basename}{suffix}",
    ]
    for c in candidates:
        if c.exists():
            return c
    return None


def _truncate_reason(reason: str, max_len: int = 120, verbose: bool = False) -> str:
    if len(reason) <= max_len:
        return reason
    if verbose:
        console.print(f"[yellow]Reason exceeds {max_len} chars; truncating.[/yellow]")
    truncated = reason[:max_len].rsplit(" ", 1)[0]
    return truncated + "…"


def _extract_existing_tags(content: str) -> Dict[str, Any]:
    """Extract existing tags. Returns dict with keys reason, interface, dependencies."""
    out: Dict[str, Any] = {"reason": None, "interface": None, "dependencies": []}
    rm = _REASON_RE.search(content)
    if rm:
        out["reason"] = rm.group(1).strip()
    im = _INTERFACE_RE.search(content)
    if im:
        try:
            out["interface"] = json.loads(im.group(1).strip())
        except (json.JSONDecodeError, ValueError):
            out["interface"] = None
    deps = []
    for dm in _DEPENDENCY_RE.finditer(content):
        deps.append(dm.group(1).strip())
    out["dependencies"] = deps
    return out


def _validate_existing_reason(reason: Optional[str]) -> bool:
    if not reason:
        return False
    if len(reason) < 20 or len(reason) > 200:
        return False
    try:
        ET.fromstring(f"<pdd-reason>{reason}</pdd-reason>")
    except ET.ParseError:
        return False
    return True


def _validate_existing_interface(interface: Optional[Dict[str, Any]]) -> bool:
    if not interface:
        return False
    try:
        res = validate_interface_structure(interface)
    except Exception:
        return False
    if isinstance(res, dict):
        return bool(res.get("valid"))
    return bool(res)


def _validate_existing_dependency(dep: str) -> bool:
    if not dep or not dep.strip():
        return False
    try:
        ET.fromstring(f"<pdd-dependency>{dep}</pdd-dependency>")
    except ET.ParseError:
        return False
    return True


def _strip_pdd_tags(content: str) -> str:
    """Remove all <pdd-*>...</pdd-*> blocks for invariant comparison."""
    stripped = _ANY_PDD_TAG_RE.sub("", content)
    # collapse blank lines
    stripped = re.sub(r"\n{3,}", "\n\n", stripped)
    return stripped.strip()


def _content_invariant_hash(content: str) -> str:
    return hashlib.sha256(_strip_pdd_tags(content).encode("utf-8")).hexdigest()


def _format_reason_tag(reason: str) -> str:
    return f"<pdd-reason>{reason}</pdd-reason>"


def _format_interface_tag(interface: Dict[str, Any]) -> str:
    body = json.dumps(interface, indent=2)
    return f"<pdd-interface>\n{body}\n</pdd-interface>"


def _format_dependency_tag(dep: str) -> str:
    return f"<pdd-dependency>{dep}</pdd-dependency>"


def _replace_or_prepend_tag(
    content: str, pattern: re.Pattern, new_tag: str, prepend_buffer: List[str]
) -> str:
    """Replace existing tag in place, or queue for prepending."""
    if pattern.search(content):
        return pattern.sub(lambda m: new_tag, content, count=1)
    prepend_buffer.append(new_tag)
    return content


def _merge_tags_into_content(
    original: str,
    new_reason: Optional[str],
    new_interface: Optional[Dict[str, Any]],
    new_dependencies: Optional[List[str]],
    replace_dependencies: bool,
) -> str:
    """Merge tags into content, preserving positions where possible."""
    content = original
    prepend: List[str] = []

    if new_reason is not None:
        content = _replace_or_prepend_tag(
            content, _REASON_RE, _format_reason_tag(new_reason), prepend
        )

    if new_interface is not None:
        content = _replace_or_prepend_tag(
            content, _INTERFACE_RE, _format_interface_tag(new_interface), prepend
        )

    if new_dependencies is not None:
        if replace_dependencies:
            # Remove all existing dependency tags
            content = _DEPENDENCY_RE.sub("", content)
            # Clean up consecutive blank lines
            content = re.sub(r"\n{3,}", "\n\n", content)
            for dep in new_dependencies:
                prepend.append(_format_dependency_tag(dep))
        else:
            for dep in new_dependencies:
                prepend.append(_format_dependency_tag(dep))

    if prepend:
        # Insert before first non-tag, non-blank line (but allow tag block at top)
        lines = content.split("\n")
        insert_idx = 0
        # Skip leading blank lines
        while insert_idx < len(lines) and not lines[insert_idx].strip():
            insert_idx += 1
        # If existing pdd tags at top, insert after them
        # Find end of leading pdd-tag block
        i = insert_idx
        while i < len(lines):
            line = lines[i].strip()
            if line.startswith("<pdd-"):
                # find closing
                close_match = re.match(r"<pdd-(reason|interface|dependency)", line)
                if close_match:
                    tag_name = close_match.group(1)
                    end_marker = f"</pdd-{tag_name}>"
                    while i < len(lines) and end_marker not in lines[i]:
                        i += 1
                    i += 1  # past closing line
                    # skip blank
                    while i < len(lines) and not lines[i].strip():
                        i += 1
                    insert_idx = i
                    continue
            break

        prepend_block = "\n".join(prepend) + "\n\n"
        new_lines = lines[:insert_idx] + [prepend_block.rstrip("\n")] + [""] + lines[insert_idx:]
        content = "\n".join(new_lines)

    # Normalize excessive blank lines
    content = re.sub(r"\n{4,}", "\n\n\n", content)
    return content


def _validate_final_tags(content: str) -> List[str]:
    """Validate tags in the final merged content. Returns list of error messages."""
    errors: List[str] = []

    rm = _REASON_RE.search(content)
    if rm:
        try:
            ET.fromstring(f"<pdd-reason>{rm.group(1).strip()}</pdd-reason>")
        except ET.ParseError as e:
            errors.append(f"<pdd-reason> failed XML validation: {e}")

    im = _INTERFACE_RE.search(content)
    if im:
        body = im.group(1).strip()
        try:
            iface_obj = json.loads(body)
        except json.JSONDecodeError as e:
            errors.append(f"<pdd-interface> JSON parse failed: {e}")
        else:
            try:
                vres = validate_interface_structure(iface_obj)
            except Exception as e:
                errors.append(f"<pdd-interface> schema validation failed: {e}")
            else:
                if isinstance(vres, dict) and not vres.get("valid"):
                    msgs = "; ".join(vres.get("errors", [])) or "invalid interface"
                    errors.append(f"<pdd-interface> schema validation failed: {msgs}")

    for dm in _DEPENDENCY_RE.finditer(content):
        dep_body = dm.group(1).strip()
        try:
            ET.fromstring(f"<pdd-dependency>{dep_body}</pdd-dependency>")
        except ET.ParseError as e:
            errors.append(f"<pdd-dependency> failed XML validation: {e}")

    return errors


def _synthesize_tags_from_prompt_code(
    prompt_text: str,
    code_text: Optional[str],
    existing_tags: Dict[str, Any],
    needs: Dict[str, bool],
    strength: float,
    temperature: float,
    verbose: bool,
) -> Tuple[Optional[Dict[str, Any]], float, List[str]]:
    """Invoke LLM to synthesize tags. Returns (payload_dict_or_None, cost, errors)."""
    from pydantic import BaseModel, Field, ValidationError
    from .llm_invoke import llm_invoke

    class TagPayload(BaseModel):
        reason: str = Field(..., min_length=20, max_length=200)
        interface: Dict[str, Any]
        dependencies: List[str] = Field(default_factory=list)

    # Truncate code if too long
    if code_text:
        code_lines = code_text.splitlines()
        if len(code_lines) > 800:
            code_text = "\n".join(code_lines[:800]) + "\n# ... (truncated)"

    needs_desc = ", ".join([k for k, v in needs.items() if v]) or "all"

    base_prompt = """You are an expert at analyzing Python prompts and code to generate PDD metadata tags.

Given the prompt text and (optionally) the corresponding code, produce a JSON object with three fields:

1. `reason`: A concise one-line description (20-200 chars, ideally <= 120) of what this module does.
2. `interface`: A JSON object describing the public interface. Schema:
   - `type`: "module" | "class" | "function"
   - For "module": include `module.functions` (list of {name, signature, returns}) and optionally `module.classes`.
   - For "class": include `class.name`, `class.methods` (list of {name, signature, returns}).
   - For "function": include `function.name`, `function.signature`, `function.returns`.
3. `dependencies`: List of prompt-file dependencies (other PDD prompt names this depends on, e.g. "llm_invoke_python.prompt").

Currently needed tags: {{needs_desc}}

Existing tags (preserve semantics if regenerating):
{{existing_tags_json}}

Prompt text:
---
{{prompt_text}}
---

Code (may be empty):
---
{{code_text}}
---

{{retry_feedback}}

Return ONLY the JSON object matching the TagPayload schema."""

    input_json = {
        "needs_desc": needs_desc,
        "existing_tags_json": json.dumps(existing_tags, indent=2, default=str),
        "prompt_text": prompt_text[:20000],
        "code_text": code_text or "(no code file found)",
        "retry_feedback": "",
    }

    total_cost = 0.0
    errors: List[str] = []
    last_validator_error: Optional[str] = None

    for attempt in range(2):
        if attempt == 1 and last_validator_error:
            input_json["retry_feedback"] = (
                f"PREVIOUS ATTEMPT FAILED VALIDATION: {last_validator_error}\n"
                "Fix the issues and return a corrected JSON object."
            )

        try:
            response = llm_invoke(
                prompt=base_prompt,
                input_json=input_json,
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                output_pydantic=TagPayload,
            )
        except Exception as e:
            errors.append(f"llm_invoke failed: {e}")
            return None, total_cost, errors

        total_cost += float(response.get("cost", 0.0) or 0.0)
        result = response.get("result")

        if result is None:
            last_validator_error = "LLM returned no result"
            continue

        # result may be a Pydantic instance or dict
        if isinstance(result, BaseModel):
            payload_dict = result.model_dump()
        elif isinstance(result, dict):
            try:
                payload = TagPayload.model_validate(result)
                payload_dict = payload.model_dump()
            except ValidationError as e:
                last_validator_error = str(e)
                continue
        else:
            last_validator_error = f"Unexpected result type: {type(result)}"
            continue

        # Validate interface structure
        try:
            vres = validate_interface_structure(payload_dict["interface"])
        except Exception as e:
            last_validator_error = f"interface structure invalid: {e}"
            continue
        if isinstance(vres, dict) and not vres.get("valid"):
            last_validator_error = (
                "interface structure invalid: " + "; ".join(vres.get("errors", []))
            )
            continue

        # Truncate reason
        payload_dict["reason"] = _truncate_reason(payload_dict["reason"], verbose=verbose)

        return payload_dict, total_cost, errors

    errors.append(f"LLM failed validation after 2 attempts: {last_validator_error}")
    return None, total_cost, errors


def generate_metadata_tags(
    prompt_path: str,
    source: str = "prompt-code",
    force: bool = False,
    dry_run: bool = False,
    output: Optional[str] = None,
    strength: float = 0.5,
    temperature: float = 0.0,
    verbose: bool = False,
) -> Dict[str, Any]:
    """Generate or refresh PDD metadata tags in a prompt file."""
    result: Dict[str, Any] = {
        "success": False,
        "prompt_path": prompt_path,
        "tags_added": [],
        "tags_preserved": [],
        "cost": 0.0,
        "diff": "",
        "errors": [],
    }

    if source not in ("prompt-code", "architecture"):
        raise ValueError(
            f"Invalid source '{source}'. Must be 'prompt-code' or 'architecture'."
        )

    prompt_p = Path(prompt_path)
    if not prompt_p.exists():
        result["errors"].append(f"prompt file not found: {prompt_path}")
        return result

    try:
        original_content = prompt_p.read_text(encoding="utf-8")
    except Exception as e:
        result["errors"].append(f"failed to read prompt file: {e}")
        return result

    existing = _extract_existing_tags(original_content)
    has_existing = has_pdd_tags(original_content)

    # Determine which tags need synthesis
    if force:
        needs = {"reason": True, "interface": True, "dependency": True}
        preserved: List[str] = []
    else:
        needs = {
            "reason": not _validate_existing_reason(existing["reason"]),
            "interface": not _validate_existing_interface(existing["interface"]),
            "dependency": False,  # dependencies are additive; only synthesize if none
        }
        if not existing["dependencies"]:
            needs["dependency"] = True
        preserved = []
        if not needs["reason"] and existing["reason"]:
            preserved.append("reason")
        if not needs["interface"] and existing["interface"]:
            preserved.append("interface")
        if not needs["dependency"] and existing["dependencies"]:
            preserved.append("dependency")

    new_reason: Optional[str] = None
    new_interface: Optional[Dict[str, Any]] = None
    new_dependencies: Optional[List[str]] = None
    replace_dependencies = False
    tags_added: List[str] = []
    cost = 0.0

    if source == "architecture":
        prompt_filename = prompt_p.name
        try:
            entry = get_architecture_entry_for_prompt(prompt_filename)
        except Exception as e:
            result["errors"].append(f"architecture lookup failed: {e}")
            return result

        if not entry:
            result["errors"].append(
                f"architecture entry not found for {prompt_filename}"
            )
            return result

        # Call helper to validate/produce tag string (spec requirement),
        # then use entry's structured fields for the in-place merge.
        try:
            _ = generate_tags_from_architecture(entry)
        except Exception as e:
            result["errors"].append(f"failed to generate tags from architecture: {e}")
            return result

        if needs["reason"]:
            r = entry.get("reason")
            if r:
                new_reason = _truncate_reason(r, verbose=verbose)
                tags_added.append("reason")
        if needs["interface"]:
            iface = entry.get("interface")
            if iface:
                new_interface = iface
                tags_added.append("interface")
        if needs["dependency"]:
            deps = entry.get("dependencies") or []
            if deps:
                new_dependencies = deps
                replace_dependencies = force
                tags_added.append("dependency")

    else:  # prompt-code
        if not any(needs.values()):
            # nothing to do
            result["success"] = True
            result["tags_preserved"] = preserved
            if verbose:
                _print_summary(result)
            return result

        code_path = _infer_code_path(prompt_p)
        code_text: Optional[str] = None
        if code_path and code_path.exists():
            try:
                code_text = code_path.read_text(encoding="utf-8")
            except Exception as e:
                if verbose:
                    console.print(f"[yellow]Could not read code file: {e}[/yellow]")

        payload, llm_cost, llm_errors = _synthesize_tags_from_prompt_code(
            prompt_text=original_content,
            code_text=code_text,
            existing_tags=existing,
            needs=needs,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
        )
        cost += llm_cost
        if payload is None:
            result["errors"].extend(llm_errors)
            result["cost"] = cost
            return result

        if needs["reason"]:
            new_reason = payload["reason"]
            tags_added.append("reason")
        if needs["interface"]:
            new_interface = payload["interface"]
            tags_added.append("interface")
        if needs["dependency"]:
            deps = payload.get("dependencies") or []
            if deps:
                new_dependencies = deps
                replace_dependencies = force
                tags_added.append("dependency")

    # Merge into content
    merged = _merge_tags_into_content(
        original_content,
        new_reason=new_reason,
        new_interface=new_interface,
        new_dependencies=new_dependencies,
        replace_dependencies=replace_dependencies,
    )

    # Invariant check: non-PDD content unchanged
    orig_hash = _content_invariant_hash(original_content)
    new_hash = _content_invariant_hash(merged)
    if orig_hash != new_hash:
        result["errors"].append(
            "non-PDD content was modified during merge; aborting write"
        )
        result["cost"] = cost
        return result

    # Validate final tags
    validation_errors = _validate_final_tags(merged)
    if validation_errors:
        result["errors"].extend(validation_errors)
        result["cost"] = cost
        return result

    # Generate diff for dry-run
    if dry_run:
        diff_lines = list(
            difflib.unified_diff(
                original_content.splitlines(keepends=True),
                merged.splitlines(keepends=True),
                fromfile=str(prompt_p),
                tofile=str(prompt_p) + " (proposed)",
            )
        )
        result["diff"] = "".join(diff_lines)
    else:
        target = Path(output) if output else prompt_p
        try:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(merged, encoding="utf-8")
        except Exception as e:
            result["errors"].append(f"failed to write output: {e}")
            result["cost"] = cost
            return result

    result["success"] = True
    result["tags_added"] = tags_added
    result["tags_preserved"] = preserved
    result["cost"] = cost

    if verbose:
        _print_summary(result)

    return result


def _print_summary(result: Dict[str, Any]) -> None:
    table = Table(title="PDD Metadata Tags Summary")
    table.add_column("Field", style="cyan")
    table.add_column("Value", style="white")
    table.add_row("prompt_path", str(result.get("prompt_path", "")))
    table.add_row("success", str(result.get("success")))
    table.add_row("tags_added", ", ".join(result.get("tags_added") or []) or "(none)")
    table.add_row(
        "tags_preserved", ", ".join(result.get("tags_preserved") or []) or "(none)"
    )
    table.add_row("cost", f"${result.get('cost', 0.0):.6f}")
    if result.get("errors"):
        table.add_row("errors", "; ".join(result["errors"]))
    console.print(table)