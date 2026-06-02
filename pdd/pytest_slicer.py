"""AST-based pytest context slicing for selective PDD includes."""

# pylint: disable=line-too-long,broad-exception-caught,too-many-arguments,too-many-positional-arguments

from __future__ import annotations

import ast
import hashlib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

from rich.console import Console

console = Console()

class SlicerError(Exception):
    """Raised when slicing fails."""


@dataclass
class SlicedManifest:
    """Metadata for a sliced pytest context excerpt."""

    selected_tests: List[str] = field(default_factory=list)
    included_fixtures: List[str] = field(default_factory=list)
    included_helpers: List[str] = field(default_factory=list)
    source_hashes: Dict[str, str] = field(default_factory=dict)


class ASTVisitor(ast.NodeVisitor):  # pylint: disable=invalid-name,missing-function-docstring
    """Collect names, fixtures, and self/cls attribute refs from a test node."""

    def __init__(self) -> None:
        self.names: Set[str] = set()
        self.usefixtures: Set[str] = set()
        self.instance_attrs: Set[str] = set()

    def visit_Name(self, node: ast.Name) -> None:  # pylint: disable=invalid-name
        if isinstance(node.ctx, ast.Load):
            self.names.add(node.id)
        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:  # pylint: disable=invalid-name
        if isinstance(node.ctx, ast.Load) and isinstance(node.value, ast.Name):
            if node.value.id in {"self", "cls"}:
                self.instance_attrs.add(node.attr)
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:  # pylint: disable=invalid-name
        self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # pylint: disable=invalid-name
        self._visit_function_like(node)

    def visit_AsyncFunctionDef(
        self, node: ast.AsyncFunctionDef
    ) -> None:  # pylint: disable=invalid-name
        self._visit_function_like(node)

    def _visit_function_like(
        self, node: ast.FunctionDef | ast.AsyncFunctionDef
    ) -> None:
        for decorator in node.decorator_list:
            if isinstance(decorator, ast.Call):
                func = decorator.func
                is_usefixtures = False
                if isinstance(func, ast.Attribute) and func.attr == "usefixtures":
                    if isinstance(func.value, ast.Attribute) and func.value.attr == "mark":
                        is_usefixtures = True

                if is_usefixtures:
                    for arg in decorator.args:
                        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                            self.usefixtures.add(arg.value)
            self.visit(decorator)

        for arg in node.args.args:
            if arg.annotation:
                self.visit(arg.annotation)

        for stmt in node.body:
            self.visit(stmt)

        if node.returns:
            self.visit(node.returns)


class PytestSlicer:  # pylint: disable=too-few-public-methods
    """AST-based pytest context slicer for selective includes."""

    def __init__(self, main_source: str, file_path: str | None = None) -> None:
        self.main_source = main_source
        self.file_path = file_path
        self.main_path_str = file_path or "main.py"

        try:
            self.main_ast = ast.parse(main_source, filename=self.main_path_str)
        except SyntaxError as exc:
            raise SlicerError(f"Syntax error in main source: {exc}") from exc

        # Map to store AST nodes: name -> (node, source_segment, file_path, parent_class_node)
        self.definitions: Dict[str, Tuple[ast.stmt, str, str, Optional[ast.ClassDef]]] = {}
        self.imports: List[Tuple[ast.stmt, str, str]] = []

        self.source_hashes: Dict[str, str] = {}
        self.source_hashes[self.main_path_str] = self._hash_source(main_source)

        self._index_file(self.main_ast, main_source, self.main_path_str)
        if self.file_path:
            self._discover_and_index_conftests()

    def _hash_source(self, source: str) -> str:
        return hashlib.md5(source.encode("utf-8")).hexdigest()

    def _index_file(self, tree: ast.Module, source: str, path: str) -> None:
        for node in tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                self.imports.append((node, self._get_source_segment(source, node), path))
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self.definitions[node.name] = (node, self._get_source_segment(source, node), path, None)
            elif isinstance(node, ast.ClassDef):
                self.definitions[node.name] = (node, self._get_source_segment(source, node), path, None)
                for item in node.body:
                    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        full_name = f"{node.name}.{item.name}"
                        self.definitions[full_name] = (item, self._get_source_segment(source, item), path, node)
            elif isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        self.definitions[target.id] = (node, self._get_source_segment(source, node), path, None)
            elif isinstance(node, ast.AnnAssign):
                if isinstance(node.target, ast.Name):
                    self.definitions[node.target.id] = (node, self._get_source_segment(source, node), path, None)

    def _get_source_segment(self, source: str, node: ast.AST) -> str:
        try:
            start_lineno = node.lineno
            if isinstance(node, (ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef)) and node.decorator_list:
                start_lineno = min(d.lineno for d in node.decorator_list)

            lines = source.splitlines()
            segment_lines = lines[start_lineno-1 : node.end_lineno]
            return "\n".join(segment_lines)
        except Exception:
            try:
                return ast.get_source_segment(source, node) or ast.unparse(node)
            except Exception:
                return ast.unparse(node)

    def _discover_and_index_conftests(self) -> None:
        if not self.file_path:
            return

        current_dir = Path(self.file_path).parent.resolve()
        root_markers = {".git", "pyproject.toml", "requirements.txt", "GEMINI.md", "setup.py"}

        while True:
            conftest_path = current_dir / "conftest.py"
            if conftest_path.exists():
                try:
                    source = conftest_path.read_text(encoding="utf-8")
                    self.source_hashes[str(conftest_path)] = self._hash_source(source)
                    tree = ast.parse(source, filename=str(conftest_path))
                    self._index_file(tree, source, str(conftest_path))
                except SyntaxError:
                    console.print(f"[yellow]Warning: Syntax error in {conftest_path}, skipping.[/yellow]")
                except Exception as e:
                    console.print(f"[yellow]Warning: Could not read {conftest_path}: {e}[/yellow]")

            if any((current_dir / m).exists() for m in root_markers) or current_dir == current_dir.parent:
                break
            current_dir = current_dir.parent

    def slice(
        self, test_names: List[str]
    ) -> Tuple[str, SlicedManifest]:  # pylint: disable=too-many-locals,too-many-branches,too-many-statements
        """Return sliced test context and a manifest of included symbols."""
        if not test_names:
            raise SlicerError("No tests specified for slicing.")

        manifest = SlicedManifest()
        manifest.selected_tests = list(test_names)

        required_nodes: Set[str] = set()
        queue: List[str] = list(test_names)
        processed: Set[str] = set()

        while queue:
            name = queue.pop(0)
            if name in processed:
                continue
            processed.add(name)

            node_info = self.definitions.get(name)
            if not node_info:
                if name in test_names:
                    raise SlicerError(f"Test '{name}' not found in source or conftests.")
                continue

            required_nodes.add(name)
            node, _, _, parent_class = node_info

            if parent_class:
                if parent_class.name not in processed:
                    queue.append(parent_class.name)

            visitor = ASTVisitor()
            visitor.visit(node)

            is_test = name.startswith("test_") or (parent_class and name.split('.')[-1].startswith("test_"))
            is_fixture = any(
                isinstance(d, ast.Call) and isinstance(d.func, ast.Attribute) and d.func.attr == "fixture"
                or isinstance(d, ast.Attribute) and d.attr == "fixture"
                for d in (node.decorator_list if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) else [])
            )

            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and (is_test or is_fixture):
                for arg in node.args.args:
                    if arg.arg != "self":
                        self._add_dependency(arg.arg, parent_class, queue, manifest, test_names)
                for arg in node.args.posonlyargs:
                    self._add_dependency(arg.arg, parent_class, queue, manifest, test_names)
                for arg in node.args.kwonlyargs:
                    self._add_dependency(arg.arg, parent_class, queue, manifest, test_names)

            for dep in visitor.names:
                self._add_dependency(dep, parent_class, queue, manifest, test_names)

            for attr in visitor.instance_attrs:
                self._add_dependency(attr, parent_class, queue, manifest, test_names)

            for fix in visitor.usefixtures:
                self._add_dependency(fix, parent_class, queue, manifest, test_names)

        manifest.included_fixtures = sorted(list(set(manifest.included_fixtures)))
        all_included = required_nodes | set(manifest.included_fixtures)
        manifest.included_helpers = sorted(list(all_included - set(test_names) - set(manifest.included_fixtures)))
        manifest.source_hashes = dict(self.source_hashes)

        output_blocks: List[str] = []
        output_blocks.append("# --- Sliced Test Manifest ---")
        output_blocks.append(f"# Selected Tests: {', '.join(manifest.selected_tests)}")
        output_blocks.append(f"# Included Fixtures: {', '.join(manifest.included_fixtures)}")
        output_blocks.append(f"# Included Helpers: {', '.join(manifest.included_helpers)}")
        output_blocks.append("# Source Hashes:")
        for file, hash_val in sorted(manifest.source_hashes.items()):
            output_blocks.append(f"#   {file}: {hash_val}")
        output_blocks.append("# ----------------------------\n")

        files_to_nodes: Dict[str, Set[str]] = {}
        for name in required_nodes:
            _, _, path, _ = self.definitions[name]
            files_to_nodes.setdefault(path, set()).add(name)

        for path in sorted(files_to_nodes.keys()):
            output_blocks.append(f"# --- From {path} ---")
            for node, segment, imp_path in self.imports:
                if imp_path == path:
                    output_blocks.append(segment)

            file_required = files_to_nodes[path]
            classes: Dict[str, List[str]] = {}
            standalone: List[str] = []

            for name in sorted(file_required):
                node, _, _, parent = self.definitions[name]
                if parent:
                    classes.setdefault(parent.name, []).append(name)
                elif isinstance(node, ast.ClassDef):
                    if name not in classes:
                        classes[name] = []
                else:
                    standalone.append(name)

            for name in standalone:
                _, segment, _, _ = self.definitions[name]
                output_blocks.append(segment)

            for class_name, members in sorted(classes.items()):
                node, _, _, _ = self.definitions[class_name]
                class_lines = []
                full_segment = self._get_source_segment(self.main_source if path == self.main_path_str else Path(path).read_text(encoding="utf-8"), node)

                header_lines = []
                for line in full_segment.splitlines():
                    stripped = line.strip()
                    if stripped.startswith("def ") or stripped.startswith("async def "):
                        break
                    header_lines.append(line)
                class_lines.extend(header_lines)

                for member_name in sorted(members):
                    _, member_segment, _, _ = self.definitions[member_name]
                    class_lines.append(member_segment)

                output_blocks.append("\n".join(class_lines))
            output_blocks.append("")

        return "\n".join(output_blocks), manifest

    def _add_dependency(
        self,
        name: str,
        current_class: Optional[ast.ClassDef],
        queue: List[str],
        manifest: SlicedManifest,
        test_names: List[str],
    ) -> None:
        resolved_dep = None
        if current_class and f"{current_class.name}.{name}" in self.definitions:
            resolved_dep = f"{current_class.name}.{name}"
        elif name in self.definitions:
            resolved_dep = name

        if resolved_dep:
            queue.append(resolved_dep)
            # If it's a fixture, add to included_fixtures
            node, _, _, _ = self.definitions[resolved_dep]
            is_fixture = any(
                isinstance(d, ast.Call) and isinstance(d.func, ast.Attribute) and d.func.attr == "fixture"
                or isinstance(d, ast.Attribute) and d.attr == "fixture"
                for d in (node.decorator_list if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) else [])
            )
            # Pytest arguments are fixtures by convention if not found as regular definitions?
            # Actually, if we found it in definitions, we check if it's marked as fixture.
            if is_fixture and resolved_dep not in test_names:
                if resolved_dep not in manifest.included_fixtures:
                    manifest.included_fixtures.append(resolved_dep)
        else:
            # If not found, it might be an external dependency or a pytest built-in fixture (like tmp_path)
            # We don't add those to the manifest for now as we can't slice them.
            pass
