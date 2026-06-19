from __future__ import annotations

import ast
import copy
import hashlib
import re
from pathlib import Path
from typing import Dict, List, Optional
from pydantic import BaseModel, Field
from rich.console import Console

console = Console()


class CompatibilityContract(BaseModel):
    public_symbols: List[str] = Field(default_factory=list)
    callable_signatures: Dict[str, str] = Field(default_factory=dict)
    patch_targets: List[str] = Field(default_factory=list)
    source_hash: str = ""
    truncated: bool = False
    truncated_counts: Dict[str, int] = Field(default_factory=dict)

    def to_prompt_block(self) -> str:
        lines = ["% Compatibility Surface"]

        # public_symbols
        pub_line = f"% public_symbols: {', '.join(self.public_symbols)}"
        if "public_symbols" in self.truncated_counts:
            pub_line += f" # (truncated: {self.truncated_counts['public_symbols']} symbols omitted)"
        lines.append(pub_line)

        # callable_signatures
        sig_line = "% callable_signatures:"
        if "callable_signatures" in self.truncated_counts:
            sig_line += f" # (truncated: {self.truncated_counts['callable_signatures']} symbols omitted)"
        lines.append(sig_line)
        for k in sorted(self.callable_signatures.keys()):
            lines.append(f"  {self.callable_signatures[k]}")

        # patch_targets
        patch_line = f"% patch_targets: {', '.join(self.patch_targets)}"
        if "patch_targets" in self.truncated_counts:
            patch_line += f" # (truncated: {self.truncated_counts['patch_targets']} symbols omitted)"
        lines.append(patch_line)

        return "\n".join(lines)


def _get_assigned_names(target: ast.AST) -> List[str]:
    if isinstance(target, ast.Name):
        return [target.id]
    elif isinstance(target, (ast.Tuple, ast.List)):
        names = []
        for elt in target.elts:
            names.extend(_get_assigned_names(elt))
        return names
    return []


def _clean_sig(node: ast.AST) -> str:
    node_copy = copy.copy(node)
    node_copy.decorator_list = []  # type: ignore
    node_copy.body = [ast.Pass()]  # type: ignore
    sig = ast.unparse(node_copy).strip()
    if sig.endswith("\n    pass"):
        sig = sig[:-9] + " ..."
    elif sig.endswith(":pass"):
        sig = sig[:-5] + " ..."
    return sig


def extract_compatibility_contract(
    py_file: Path,
    *,
    max_symbols: int = 200,
    test_files: Optional[List[Path]] = None,
) -> CompatibilityContract:
    if not py_file.is_file():
        console.print(f"[warning] Source file not found: {py_file}", style="yellow")
        return CompatibilityContract()

    try:
        source_bytes = py_file.read_bytes()
        source_hash = hashlib.sha256(source_bytes).hexdigest()
        source_code = source_bytes.decode("utf-8", errors="replace")
        tree = ast.parse(source_code, filename=str(py_file))
    except (SyntaxError, Exception) as e:
        console.print(f"[error] Failed to parse or read {py_file}: {e}", style="red")
        try:
            shash = hashlib.sha256(py_file.read_bytes()).hexdigest()
        except Exception:
            shash = ""
        return CompatibilityContract(source_hash=shash)

    # 1. Determine Public Symbols (__all__-authoritative)
    has_all = False
    all_symbols: List[str] = []
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id == "__all__":
                    if isinstance(node.value, (ast.List, ast.Tuple)):
                        all_symbols = [
                            elt.value
                            for elt in node.value.elts
                            if isinstance(elt, ast.Constant) and isinstance(elt.value, str)
                        ]
                        has_all = True

    if has_all:
        public_symbols = all_symbols
    else:
        top_level_names = set()
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                top_level_names.add(node.name)
            elif isinstance(node, ast.Assign):
                for target in node.targets:
                    top_level_names.update(_get_assigned_names(target))
            elif isinstance(node, ast.AnnAssign):
                if isinstance(node.target, ast.Name):
                    top_level_names.add(node.target.id)
            elif isinstance(node, (ast.Import, ast.ImportFrom)):
                for alias in node.names:
                    top_level_names.add(alias.asname or alias.name)

        public_symbols = [
            n for n in top_level_names
            if not n.startswith("_")
        ]

    # 2. Extract Callable Signatures
    callable_signatures: Dict[str, str] = {}

    def visit_class(class_node: ast.ClassDef, parent_qname: str):
        qname = f"{parent_qname}.{class_node.name}" if parent_qname else class_node.name
        callable_signatures[qname] = f"[class] {_clean_sig(class_node)}"

        for body_node in class_node.body:
            if isinstance(body_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                m_name = body_node.name
                if not m_name.startswith("_") or m_name == "__init__":
                    method_qname = f"{qname}.{m_name}"
                    callable_signatures[method_qname] = f"[method] {_clean_sig(body_node)}"
            elif isinstance(body_node, ast.ClassDef):
                visit_class(body_node, qname)

    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            if not node.name.startswith("_"):
                callable_signatures[node.name] = f"[function] {_clean_sig(node)}"
        elif isinstance(node, ast.AsyncFunctionDef):
            if not node.name.startswith("_"):
                callable_signatures[node.name] = f"[async_function] {_clean_sig(node)}"
        elif isinstance(node, ast.ClassDef):
            if not node.name.startswith("_"):
                visit_class(node, "")

    # 3. Determine Patch Targets
    patch_targets: List[str] = []
    if test_files is not None:
        patch_targets_set = set()
        pattern = re.compile(r"patch\(\s*['\"]([^'\"]+?)['\"]")
        for t_file in test_files:
            if t_file.is_file():
                try:
                    content = t_file.read_text(errors="ignore")
                    for match in pattern.finditer(content):
                        target_path = match.group(1)
                        parts = target_path.split(".")
                        if parts:
                            last_part = parts[-1]
                            if last_part.startswith("_") and not (
                                last_part.startswith("__") and last_part.endswith("__")
                            ):
                                patch_targets_set.add(target_path)
                except Exception:
                    pass
        patch_targets = list(patch_targets_set)
    else:
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                name = node.name
                if name.startswith("_") and not (
                    name.startswith("__") and name.endswith("__")
                ):
                    patch_targets.append(name)

    # 4. Sorting and Capping
    truncated = False
    truncated_counts: Dict[str, int] = {}

    # Public Symbols Cap
    public_symbols = sorted(list(set(public_symbols)))
    orig_pub_count = len(public_symbols)
    if orig_pub_count > max_symbols:
        truncated = True
        truncated_counts["public_symbols"] = orig_pub_count - max_symbols
        public_symbols = public_symbols[:max_symbols]

    # Callable Signatures Cap
    sorted_sig_keys = sorted(callable_signatures.keys())
    orig_sig_count = len(sorted_sig_keys)
    if orig_sig_count > max_symbols:
        truncated = True
        truncated_counts["callable_signatures"] = orig_sig_count - max_symbols
        sorted_sig_keys = sorted_sig_keys[:max_symbols]
    callable_signatures = {k: callable_signatures[k] for k in sorted_sig_keys}

    # Patch Targets Cap
    patch_targets = sorted(list(set(patch_targets)))
    orig_patch_count = len(patch_targets)
    if orig_patch_count > max_symbols:
        truncated = True
        truncated_counts["patch_targets"] = orig_patch_count - max_symbols
        patch_targets = patch_targets[:max_symbols]

    return CompatibilityContract(
        public_symbols=public_symbols,
        callable_signatures=callable_signatures,
        patch_targets=patch_targets,
        source_hash=source_hash,
        truncated=truncated,
        truncated_counts=truncated_counts,
    )