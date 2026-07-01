from __future__ import annotations

import json
import os
import re
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Union, Tuple

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .llm_invoke import llm_invoke

def _detect_language(path: Path) -> str:
    """Return language string from file extension."""
    ext = path.suffix.lower()
    if ext == ".py":
        return "python"
    elif ext in (".ts", ".tsx"):
        return "typescript"
    elif ext in (".js", ".jsx", ".cjs", ".mjs"):
        return "javascript"
    return "unknown"

def _extract_symbols(path: Path, content: str) -> List[Dict[str, Any]]:
    """
    Regex-based symbol extraction returning call/import/env/write/network/log hits
    with line numbers and excerpts.
    """
    symbols = []
    lines = content.splitlines()
    
    # Combined regexes for different kinds of operations
    patterns = {
        "import": re.compile(r"^(?:import|from)\s+.*|require\s*\("),
        "call": re.compile(r"\b[A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)+\s*\("),
        "env": re.compile(r"process\.env\.[a-zA-Z0-9_]+|os\.environ(?:\.get|\[)"),
        "write": re.compile(r"open\s*\(\s*[^,]+,\s*['\"]w['\"]|fs\.write(?:FileSync|File)?\s*\("),
        "network": re.compile(r"fetch\s*\(|requests\.(?:get|post|put|delete|patch)|axios|urllib"),
        "log": re.compile(r"console\.(?:log|error|warn|info)|logger\.(?:info|debug|error|warn)|logging\.(?:info|debug|error|warn)")
    }
    
    for i, line in enumerate(lines):
        line_num = i + 1
        for kind, pattern in patterns.items():
            for match in pattern.finditer(line):
                symbols.append({
                    "symbol": match.group(0),
                    "kind": kind,
                    "line": line_num,
                    "excerpt": line.strip()[:200]
                })
    return symbols

def _resolve_local_import(current_file: Path, import_path: str, project_root: Path) -> Optional[Path]:
    """
    Resolve a relative import path to an existing file on disk; try multiple candidate extensions; 
    reject paths outside project root.
    """
    # Remove quotes and basic cleanup
    import_path = import_path.strip("'\"")
    if not (import_path.startswith("./") or import_path.startswith("../")):
        return None
        
    base_dir = current_file.parent
    try:
        resolved_base = (base_dir / import_path).resolve()
    except Exception:
        return None

    # Path safety: reject if it escapes project root
    try:
        project_root_resolved = project_root.resolve()
        resolved_base.relative_to(project_root_resolved)
    except ValueError:
        return None
    except Exception:
        return None

    candidates = [
        resolved_base,
        resolved_base.with_suffix('.py'),
        resolved_base.with_suffix('.ts'),
        resolved_base.with_suffix('.tsx'),
        resolved_base.with_suffix('.js'),
        resolved_base / "index.ts",
        resolved_base / "index.tsx",
        resolved_base / "index.js",
        resolved_base / "__init__.py"
    ]

    for candidate in candidates:
        try:
            candidate.resolve().relative_to(project_root_resolved)
        except (ValueError, OSError):
            return None
        if candidate.is_file():
            return candidate
            
    return None

def _derive_project_root(artifact_paths: List[Union[str, Path]]) -> Path:
    """Derive a bounded local project root for import following and manifests."""
    resolved_paths = [Path(p).resolve() for p in artifact_paths]
    existing_dirs = [p.parent if p.is_file() else p for p in resolved_paths]
    common = Path(os.path.commonpath([str(p) for p in existing_dirs]))

    root_markers = ("package.json", "pyproject.toml", "requirements.txt", "go.mod", ".git")
    cursor = common
    while True:
        if any((cursor / marker).exists() for marker in root_markers):
            return cursor
        if cursor.parent == cursor:
            break
        cursor = cursor.parent

    if common.name in {"src", "lib", "app", "tests", "test"} and common.parent != common:
        return common.parent
    return common

def _inspect_manifests(project_root: Path) -> Dict[str, List[str]]:
    """Read dependency manifests and return a mapping of manager to package name lists."""
    manifests: Dict[str, List[str]] = {}
    
    # package.json
    pkg_json = project_root / "package.json"
    if pkg_json.is_file():
        try:
            with open(pkg_json, "r", encoding="utf-8") as f:
                data = json.load(f)
                deps = list(data.get("dependencies", {}).keys()) + list(data.get("devDependencies", {}).keys())
                if deps:
                    manifests["npm"] = deps
        except Exception:
            pass

    # requirements.txt
    req_txt = project_root / "requirements.txt"
    if req_txt.is_file():
        try:
            with open(req_txt, "r", encoding="utf-8") as f:
                deps = [line.split("==")[0].strip() for line in f if line.strip() and not line.startswith("#")]
                if deps:
                    manifests["pip"] = deps
        except Exception:
            pass

    # pyproject.toml
    pyproject = project_root / "pyproject.toml"
    if pyproject.is_file():
        try:
            with open(pyproject, "r", encoding="utf-8") as f:
                content = f.read()
                # Basic extraction without heavy toml parser
                match = re.search(r"\[project\.dependencies\](.*?)(?:\n\[|$)", content, re.DOTALL)
                if match:
                    deps = re.findall(r"[\"']([^\"']+)[\"']", match.group(1))
                    if deps:
                        manifests["poetry/pip"] = deps
        except Exception:
            pass

    # go.mod
    go_mod = project_root / "go.mod"
    if go_mod.is_file():
        try:
            with open(go_mod, "r", encoding="utf-8") as f:
                deps = []
                in_require = False
                for line in f:
                    line = line.strip()
                    if line == "require (":
                        in_require = True
                    elif line == ")":
                        in_require = False
                    elif in_require and line and not line.startswith("//"):
                        deps.append(line.split()[0])
                    elif line.startswith("require ") and not in_require:
                        deps.append(line.split()[1])
                if deps:
                    manifests["go"] = deps
        except Exception:
            pass

    return manifests

def _build_classifier_input(contract_effects: List[Dict], observed_evidence: List[Dict], target_language: str) -> Dict[str, Any]:
    """Build the structured JSON input for the LLM classifier."""
    return {
        "contract_effects": contract_effects,
        "target": target_language,
        "observed_evidence": observed_evidence,
        "deterministic_findings": []
    }

def _extract_last_json(text: str) -> Optional[List]:
    """
    Extract the last valid top-level JSON array or object from a text string using raw_decode
    iterating from every `[` and `{` position. Used as a fallback.
    """
    decoder = json.JSONDecoder()
    last_valid_json = None

    for i in range(len(text)):
        if text[i] in ('{', '['):
            try:
                obj, idx = decoder.raw_decode(text[i:])
                # Capture arrays and objects per spec
                if isinstance(obj, (list, dict)):
                    last_valid_json = obj
            except json.JSONDecodeError:
                pass

    return last_valid_json

def run_agentic_reviewer(
    contract_effects: List[Dict],
    artifact_paths: List[Union[str, Path]],
    bounds: Optional[Dict] = None
) -> List[Dict]:
    """
    A read-only, bounded evidence collector for capability-policy checks.
    
    Extracts symbols, follows imports, inspects manifests, and calls a constrained LLM classifier
    to resolve ambiguous effects.
    """
    try:
        from rich.console import Console
    except ImportError:
        Console = None

    console = Console() if Console else None

    if not bounds:
        bounds = {}
    
    max_files = bounds.get("max_files", 20)
    max_follow_depth = bounds.get("max_follow_depth", 2)
    max_search_results = bounds.get("max_search_results", 50)
    max_runtime_seconds = bounds.get("max_runtime_seconds", 30)

    start_time = time.time()
    
    if not artifact_paths:
        return []

    project_root = _derive_project_root(artifact_paths)
    
    visited_files: Set[str] = set()
    queue: List[Tuple[Path, int]] = [(Path(p).resolve(), 0) for p in artifact_paths]
    
    observed_evidence = []
    agent_steps = []
    
    manifests = _inspect_manifests(project_root)
    if manifests:
        agent_steps.append(f"Inspected manifests: found dependencies for {', '.join(manifests.keys())}")

    # BFS Traversal
    while queue:
        if time.time() - start_time > max_runtime_seconds:
            agent_steps.append("Reached max_runtime_seconds bound.")
            break
            
        if len(visited_files) >= max_files:
            agent_steps.append("Reached max_files bound.")
            break

        current_file, depth = queue.pop(0)
        file_key = str(current_file)
        
        if file_key in visited_files:
            continue
            
        visited_files.add(file_key)
        agent_steps.append(f"Read file {current_file.name} (depth {depth})")
        
        try:
            with open(current_file, "r", encoding="utf-8") as f:
                content = f.read()
        except (UnicodeDecodeError, IOError):
            continue

        symbols = _extract_symbols(current_file, content)
        
        for sym in symbols:
            if len(observed_evidence) >= max_search_results:
                break
            
            observed_evidence.append({
                "file": current_file.name,
                "line": sym["line"],
                "excerpt": sym["excerpt"],
                "kind": sym["kind"],
                "symbol": sym["symbol"]
            })
            agent_steps.append(f"Found symbol '{sym['symbol']}' at line {sym['line']}")
            
            # Follow imports
            if sym["kind"] == "import" and depth < max_follow_depth:
                # Extract the import path from the excerpt
                match = re.search(r"['\"]([^'\"]+)['\"]", sym["excerpt"])
                if match:
                    import_path = match.group(1)
                    resolved = _resolve_local_import(current_file, import_path, project_root)
                    if resolved and str(resolved) not in visited_files:
                        queue.append((resolved, depth + 1))
                        agent_steps.append(f"Followed import to {resolved.name}")

    if not observed_evidence:
        return [{
            "judgment": "unknown",
            "confidence": 0.0,
            "source": "agentic_reviewer",
            "message": "Insufficient evidence to determine effect",
            "severity": "warning",
            "evidence": [],
            "agent_steps": agent_steps
        }]

    target_language = _detect_language(Path(artifact_paths[0]))
    classifier_input = _build_classifier_input(contract_effects, observed_evidence, target_language)

    prompt = """
    Analyze the provided contract effects against the observed evidence.
    Return a JSON array where each element contains:
    - action: string
    - resource: string
    - judgment: one of "violation", "likely_violation", "unknown", "no_violation"
    - confidence: float between 0.0 and 1.0
    - message: string explanation
    """

    try:
        schema = {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "action": {"type": "string"},
                    "resource": {"type": "string"},
                    "judgment": {"type": "string", "enum": ["violation", "likely_violation", "unknown", "no_violation"]},
                    "confidence": {"type": "number"},
                    "message": {"type": "string"}
                },
                "required": ["action", "resource", "judgment", "confidence", "message"]
            }
        }
        
        response = llm_invoke(
            prompt=prompt,
            input_json=classifier_input,
            strength=0.0,
            temperature=0.1,
            output_schema=schema,
            time=0.25
        )
        
        result_content = response.get("result", [])
        if isinstance(result_content, str):
            parsed = _extract_last_json(result_content)
            if parsed is not None:
                result_content = parsed
            else:
                raise ValueError("Failed to extract JSON from LLM response")
                
        normalized_findings = []
        all_low_confidence = True

        for item in result_content:
            if not isinstance(item, dict):
                continue
                
            conf = float(item.get("confidence", 0.0))
            if conf >= 0.5:
                all_low_confidence = False
                
            normalized_findings.append({
                "source": "agentic_reviewer",
                "severity": "warning",
                "confidence": conf,
                "effect": {
                    "action": item.get("action", "unknown"),
                    "resource": item.get("resource", "unknown")
                },
                "message": item.get("message", "No message provided"),
                "evidence": [
                    {
                        "file": ev["file"],
                        "line": ev["line"],
                        "excerpt": ev["excerpt"]
                    } for ev in observed_evidence[:5] # Provide a sample of evidence
                ],
                "agent_steps": agent_steps,
                "judgment": item.get("judgment", "unknown")
            })

        if all_low_confidence:
            return [{
                "judgment": "unknown",
                "confidence": 0.0,
                "source": "agentic_reviewer",
                "message": "Insufficient evidence to determine effect",
                "severity": "warning",
                "evidence": [],
                "agent_steps": agent_steps
            }]
            
        return normalized_findings

    except Exception as e:
        if console:
            console.print(f"[yellow]LLM classifier call failed or was invalid: {e}[/yellow]")
        return []
