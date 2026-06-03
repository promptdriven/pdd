"""AST-based API/dependency contract slicing for compressed PDD context (#875)."""

from __future__ import annotations

import ast
import hashlib
import re
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Set, Tuple, Union


class ContractSlicerError(Exception):
    """Raised when contract slicing or verification fails."""


@dataclass
class ContractManifest:
    """Symbols and imports included in a contract slice."""

    seeds: List[str] = field(default_factory=list)
    included_symbols: List[str] = field(default_factory=list)
    included_imports: List[str] = field(default_factory=list)
    source_hash: str = ""


_NameDef = Tuple[ast.stmt, str, Optional[str]]


class _RefVisitor(ast.NodeVisitor):  # pylint: disable=invalid-name
    """Collect loaded names from an AST subtree."""

    def __init__(self) -> None:
        self.names: Set[str] = set()

    def visit_Name(self, node: ast.Name) -> None:  # pylint: disable=invalid-name,missing-function-docstring
        if isinstance(node.ctx, ast.Load):
            self.names.add(node.id)
        self.generic_visit(node)


class ApiContractSlicer:
    """Preserve module API surface and local dependencies for seed symbols."""

    def __init__(self, source: str, file_path: str | None = None) -> None:
        self.source = source
        self.file_path = file_path or "module.py"
        try:
            self.tree = ast.parse(source, filename=self.file_path)
        except SyntaxError as exc:
            raise ContractSlicerError(f"Syntax error in {self.file_path}: {exc}") from exc
        self.definitions: Dict[str, _NameDef] = {}
        self.import_nodes: List[Tuple[ast.stmt, str]] = []
        self._index_module()

    def _hash_source(self) -> str:
        return hashlib.md5(self.source.encode("utf-8")).hexdigest()

    def _segment(self, node: ast.AST) -> str:
        start = node.lineno
        if (
            isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
            and node.decorator_list
        ):
            start = min(d.lineno for d in node.decorator_list)
        lines = self.source.splitlines()
        end = getattr(node, "end_lineno", node.lineno)
        return "\n".join(lines[start - 1 : end])

    def _index_module(self) -> None:
        for node in self.tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                self.import_nodes.append((node, self._segment(node)))
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self.definitions[node.name] = (node, self._segment(node), None)
            elif isinstance(node, ast.ClassDef):
                self.definitions[node.name] = (node, self._segment(node), None)
                for item in node.body:
                    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        key = f"{node.name}.{item.name}"
                        self.definitions[key] = (item, self._segment(item), node.name)
                    elif isinstance(item, (ast.Assign, ast.AnnAssign)):
                        for name in self._assign_names(item):
                            self.definitions[f"{node.name}.{name}"] = (
                                item,
                                self._segment(item),
                                node.name,
                            )
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                for name in self._assign_names(node):
                    self.definitions[name] = (node, self._segment(node), None)

    @staticmethod
    def _assign_names(node: Union[ast.Assign, ast.AnnAssign]) -> List[str]:
        names: List[str] = []
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    names.append(target.id)
        elif isinstance(node.target, ast.Name):
            names.append(node.target.id)
        return names

    @staticmethod
    def _is_patch_callee(func: ast.AST) -> Tuple[bool, bool]:
        """Return (is_patch_call, is_patch_object)."""
        if isinstance(func, ast.Name):
            return (
                func.id in {"patch", "patch.object"},
                func.id == "patch.object",
            )
        if isinstance(func, ast.Attribute):
            if (
                func.attr == "object"
                and isinstance(func.value, ast.Name)
                and func.value.id == "patch"
            ):
                return True, True
            if (
                func.attr == "object"
                and isinstance(func.value, ast.Attribute)
                and func.value.attr == "patch"
                and isinstance(func.value.value, ast.Name)
                and func.value.value.id in {"mock", "mocker"}
            ):
                return True, True
            if isinstance(func.value, ast.Name) and func.value.id in {"mock", "mocker"}:
                return (
                    func.attr in {"patch", "patch.object"},
                    func.attr == "patch.object",
                )
        return False, False

    @staticmethod
    def _add_symbols_from_patch_path(
        patch_path: str,
        module_qualname: str,
        seeds: Set[str],
    ) -> None:
        prefix = f"{module_qualname}."
        if not patch_path.startswith(prefix):
            parts = patch_path.split(".")
            for index, part in enumerate(parts):
                if part == module_qualname.split(".")[-1] and index < len(parts) - 1:
                    seeds.update(parts[index + 1 :])
                    return
            return
        remainder = patch_path[len(prefix) :]
        if remainder:
            seeds.update(remainder.split("."))

    @staticmethod
    def _build_test_alias_map(
        tree: ast.Module,
        module_qualname: str,
        seeds: Set[str],
    ) -> Dict[str, Optional[str]]:
        """Map local test names to target-module symbols (None = whole-module alias)."""
        alias_map: Dict[str, Optional[str]] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module:
                if node.module == module_qualname or node.module.startswith(
                    module_qualname + "."
                ):
                    for alias in node.names:
                        local = alias.asname or alias.name
                        alias_map[local] = alias.name
                        seeds.add(alias.name)
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name == module_qualname or alias.name.startswith(
                        module_qualname + "."
                    ):
                        bound = alias.asname or alias.name.split(".")[-1]
                        alias_map[bound] = None
        return alias_map

    @staticmethod
    def _collect_module_alias_attribute_seeds(
        tree: ast.Module,
        alias_map: Dict[str, Optional[str]],
        seeds: Set[str],
    ) -> None:
        """Record ``alias.attr`` uses when *alias* is a module import alias."""
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Attribute)
                and isinstance(node.ctx, ast.Load)
                and isinstance(node.value, ast.Name)
                and node.value.id in alias_map
                and alias_map[node.value.id] is None
            ):
                seeds.add(node.attr)

    @staticmethod
    def _collect_patch_seeds_from_test(  # pylint: disable=too-many-branches
        tree: ast.Module,
        module_qualname: str,
        alias_map: Dict[str, Optional[str]],
        seeds: Set[str],
    ) -> None:
        patch_re = re.compile(
            r"^(?:"
            + re.escape(module_qualname)
            + r"\.)([A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*)$"
        )
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            is_patch, is_patch_object = ApiContractSlicer._is_patch_callee(node.func)
            if not is_patch or not node.args:
                continue

            if is_patch_object and len(node.args) >= 2:
                attr_arg = node.args[1]
                attr_name: Optional[str] = None
                if isinstance(attr_arg, ast.Constant) and isinstance(attr_arg.value, str):
                    attr_name = attr_arg.value
                if not attr_name:
                    continue
                target = node.args[0]
                if isinstance(target, ast.Constant) and isinstance(target.value, str):
                    ApiContractSlicer._add_symbols_from_patch_path(
                        f"{target.value}.{attr_name}",
                        module_qualname,
                        seeds,
                    )
                elif isinstance(target, ast.Name):
                    mapped = alias_map.get(target.id)
                    if mapped is None:
                        seeds.add(attr_name)
                    else:
                        seeds.add(f"{mapped}.{attr_name}")
                elif isinstance(target, ast.Attribute):
                    ApiContractSlicer._add_patch_attribute_target(
                        target, attr_name, alias_map, seeds
                    )
                continue

            target = node.args[0]
            if isinstance(target, ast.Constant) and isinstance(target.value, str):
                match = patch_re.match(target.value)
                if match:
                    seeds.update(match.group(1).split("."))
                else:
                    ApiContractSlicer._add_symbols_from_patch_path(
                        target.value, module_qualname, seeds
                    )
            elif isinstance(target, ast.Attribute):
                ApiContractSlicer._add_patch_attribute_target(
                    target, None, alias_map, seeds
                )

    @staticmethod
    def _add_patch_attribute_target(
        target: ast.Attribute,
        trailing_attr: Optional[str],
        alias_map: Dict[str, Optional[str]],
        seeds: Set[str],
    ) -> None:
        parts: List[str] = []
        if trailing_attr:
            parts.append(trailing_attr)
        cur: ast.AST = target
        while isinstance(cur, ast.Attribute):
            parts.insert(0, cur.attr)
            cur = cur.value
        if isinstance(cur, ast.Name):
            mapped = alias_map.get(cur.id)
            if mapped is None:
                seeds.update(parts)
            elif mapped:
                seeds.add(mapped)
                seeds.update(parts[1:])

    @staticmethod
    def seeds_from_test(test_source: str, module_qualname: str) -> List[str]:
        """Extract patch targets and imported symbols from tests."""
        try:
            tree = ast.parse(test_source)
        except SyntaxError as exc:
            raise ContractSlicerError(f"Syntax error in test source: {exc}") from exc

        seeds: Set[str] = set()
        alias_map = ApiContractSlicer._build_test_alias_map(
            tree, module_qualname, seeds
        )
        ApiContractSlicer._collect_patch_seeds_from_test(
            tree, module_qualname, alias_map, seeds
        )
        ApiContractSlicer._collect_module_alias_attribute_seeds(
            tree, alias_map, seeds
        )
        return sorted(seeds)

    def slice(  # pylint: disable=duplicate-code,too-many-locals,too-many-branches,too-many-statements
        self,
        seeds: List[str],
        *,
        extra_seeds: Iterable[str] | None = None,
    ) -> Tuple[str, ContractManifest]:
        """Slice *seeds* and transitive local dependencies from the module."""
        if not seeds and not extra_seeds:
            raise ContractSlicerError("At least one seed symbol is required for contract slicing.")

        manifest = ContractManifest(seeds=list(seeds), source_hash=self._hash_source())
        all_seeds = list(dict.fromkeys([*seeds, *(extra_seeds or [])]))
        required: Set[str] = set()
        queue = list(all_seeds)
        processed: Set[str] = set()

        while queue:
            name = queue.pop(0)
            if name in processed:
                continue
            processed.add(name)
            resolved = self._resolve_symbol(name)
            if not resolved:
                if name in all_seeds:
                    raise ContractSlicerError(f"Seed symbol '{name}' not found in {self.file_path}")
                continue
            required.add(resolved)
            node, _, parent = self.definitions[resolved]
            if parent and parent not in processed:
                queue.append(parent)
            visitor = _RefVisitor()
            visitor.visit(node)
            for dep in visitor.names:
                dep_resolved = self._resolve_symbol(dep, parent_class=parent)
                if dep_resolved and dep_resolved not in processed:
                    queue.append(dep_resolved.split(".")[-1])

        manifest.included_symbols = sorted(required)
        parts = [
            "# --- API Contract Slice ---",
            f"# Seeds: {', '.join(all_seeds)}",
            f"# Included: {', '.join(manifest.included_symbols)}",
            f"# Source hash: {manifest.source_hash}",
            "# --------------------------\n",
        ]
        used_imports = self._imports_for_symbols(required)
        manifest.included_imports = used_imports
        parts.extend(used_imports)

        emitted_nodes: Set[int] = set()
        for node in sorted(self.tree.body, key=lambda n: n.lineno):
            if isinstance(node, ast.ClassDef):
                if node.name not in required and not any(
                    sym.startswith(f"{node.name}.") for sym in required
                ):
                    continue
                if id(node) in emitted_nodes:
                    continue
                emitted_nodes.add(id(node))
                parts.append(self._render_class(node, required))
                continue
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                names = self._assign_names(node)
                if not any(n in required for n in names):
                    continue
            else:
                name = getattr(node, "name", None)
                if name not in required:
                    continue
            if id(node) in emitted_nodes:
                continue
            emitted_nodes.add(id(node))
            parts.append(self._segment(node))
            parts.append("")

        body = "\n".join(parts).rstrip() + "\n"
        self.verify_contract(body, required)
        return body, manifest

    def _resolve_symbol(self, name: str, parent_class: str | None = None) -> Optional[str]:
        if parent_class:
            qualified = f"{parent_class}.{name}"
            if qualified in self.definitions:
                return qualified
        if name in self.definitions:
            return name
        for key in self.definitions:
            if key.endswith(f".{name}"):
                return key
        return None

    def _imports_for_symbols(self, symbols: Set[str]) -> List[str]:
        needed: Set[str] = set()
        for symbol in symbols:
            visitor = _RefVisitor()
            visitor.visit(self.definitions[symbol][0])
            needed.update(visitor.names)
        segments: List[str] = []
        for imp_node, segment in self.import_nodes:
            imp_names: Set[str] = set()
            if isinstance(imp_node, ast.Import):
                for alias in imp_node.names:
                    imp_names.add(alias.asname or alias.name.split(".")[0])
            elif isinstance(imp_node, ast.ImportFrom):
                for alias in imp_node.names:
                    imp_names.add(alias.asname or alias.name)
            if imp_names & needed:
                segments.append(segment)
        return segments

    def _render_class(
        self, node: ast.ClassDef, required: Set[str]
    ) -> str:  # pylint: disable=too-many-branches
        """Emit class header plus only required members."""
        lines = self._segment(node).splitlines()
        header: List[str] = []
        for line in lines:
            stripped = line.strip()
            if stripped.startswith("def ") or stripped.startswith("async def "):
                break
            header.append(line)
        members: List[str] = []
        for item in node.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                key = f"{node.name}.{item.name}"
                if key in required or node.name in required:
                    members.append(self._segment(item))
            elif isinstance(item, (ast.Assign, ast.AnnAssign)):
                for name in self._assign_names(item):
                    if f"{node.name}.{name}" in required or name in required:
                        members.append(self._segment(item))
        if not members and node.name in required:
            for item in node.body:
                if (
                    isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and item.name == "__init__"
                ):
                    members.append(self._segment(item))
        if members:
            return "\n".join(header).rstrip() + "\n" + "\n\n".join(members) + "\n"
        return self._segment(node) + "\n"

    @staticmethod
    def verify_contract(  # pylint: disable=too-many-branches
        output_source: str,
        required_symbols: Iterable[str],
        *,
        file_path: str | None = None,
    ) -> None:
        """Raise when *required_symbols* are absent from sliced output."""
        label = file_path or "output"
        code = "\n".join(
            line for line in output_source.splitlines() if not line.lstrip().startswith("#")
        )
        try:
            tree = ast.parse(code, filename=label)
        except SyntaxError as exc:
            raise ContractSlicerError(
                f"Contract output for {label} is not valid Python: {exc}"
            ) from exc

        defined: Set[str] = set()
        for node in tree.body:
            if isinstance(node, ast.ClassDef):
                defined.add(node.name)
                for item in node.body:
                    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        defined.add(f"{node.name}.{item.name}")
                        defined.add(item.name)
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                defined.add(node.name)
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                if isinstance(node, ast.Assign):
                    for target in node.targets:
                        if isinstance(target, ast.Name):
                            defined.add(target.id)
                elif isinstance(node.target, ast.Name):
                    defined.add(node.target.id)

        missing: List[str] = []
        for sym in required_symbols:
            if sym in defined:
                continue
            if sym.split(".")[-1] in defined:
                continue
            missing.append(sym)
        if missing:
            raise ContractSlicerError(
                f"Contract verification failed for {label}; "
                f"missing symbols: {', '.join(sorted(missing))}"
            )
