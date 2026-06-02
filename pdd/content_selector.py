from __future__ import annotations

import ast
import json
import re
import textwrap
import time
import signal
from dataclasses import dataclass, field
from typing import Optional, Any, Union

from rich.console import Console
from rich.theme import Theme

from .pytest_slicer import PytestSlicer, SlicerError

# Theme for consistent styling
theme = Theme({
    "info": "cyan",
    "warning": "yellow",
    "error": "bold red",
    "success": "green",
    "path": "dim blue",
    "command": "bold magenta"
})
console = Console(theme=theme)

class SelectorError(Exception):
    """Exception raised for errors in the ContentSelector."""
    pass


@dataclass
class ContentSelector:
    """
    Deterministic content extraction from files based on line ranges, Python AST structures, 
    Markdown sections, regex patterns, and JSON/YAML path traversal.
    """

    @staticmethod
    def select(content: str, selectors: list[str] | str, file_path: str | None = None, mode: str = "full") -> str:
        """
        Extracts content based on provided selectors.
        """
        if isinstance(selectors, str):
            raw_parts = [s.strip() for s in selectors.split(",") if s.strip()]
            selectors = []
            for part in raw_parts:
                # If part has a kind: prefix, it's a new selector
                # Kind prefix is word characters followed by a colon
                if re.match(r'^\w+:', part) or not selectors:
                    selectors.append(part)
                else:
                    # Otherwise it's a continuation of the previous selector's value
                    selectors[-1] += "," + part
        else:
            selectors = [s.strip() for s in selectors if s.strip()]

        file_ext = (file_path.split(".")[-1].lower() if file_path and "." in file_path else "py")
        if not file_path:
            file_ext = "py"

        if not selectors:
            if mode == "interface":
                if file_ext == "py":
                    return ContentSelector._generate_interface(content, file_path)
                return content
            return content

        # Check if all selectors are empty strings
        if all(not s for s in selectors):
            return content

        valid_kinds = {"lines", "def", "class", "section", "pattern", "path", "pytest"}
        
        spans: list[tuple[int, int]] = []
        path_results: list[str] = []
        lines = content.splitlines(keepends=True)

        for selector in selectors:
            if not selector: continue
            if ":" not in selector:
                _report_error(f"Malformed selector: '{selector}'. Must be kind:value.", file_path)
                raise SelectorError(f"Malformed selector: '{selector}'. Valid kinds are: {', '.join(sorted(valid_kinds))}")
            
            kind, value = selector.split(":", 1)
            kind = kind.strip()
            value = value.strip()

            if kind not in valid_kinds:
                _report_error(f"Malformed selector: Invalid kind '{kind}'. Valid kinds are: {', '.join(sorted(valid_kinds))}", file_path)
                raise SelectorError(f"Malformed selector: Invalid kind '{kind}'. Valid kinds are: {', '.join(sorted(valid_kinds))}")

            try:
                if kind == "lines":
                    spans.extend(ContentSelector._process_lines(lines, value))
                elif kind == "def":
                    if file_ext != "py":
                        raise SelectorError("AST selectors require a .py file")
                    spans.extend(ContentSelector._process_def(content, value))
                elif kind == "class":
                    if file_ext != "py":
                        raise SelectorError("AST selectors require a .py file")
                    spans.extend(ContentSelector._process_class(content, value))
                elif kind == "section":
                    if file_ext not in {"md", "markdown"}:
                        raise SelectorError("Section selector requires a .md file")
                    spans.extend(ContentSelector._process_section(lines, value))
                elif kind == "pattern":
                    spans.extend(ContentSelector._process_pattern(lines, value))
                elif kind == "path":
                    if file_ext not in {"json", "yaml", "yml"}:
                        raise SelectorError("Path selector requires a JSON or YAML file")
                    path_results.append(ContentSelector._process_path(content, value, file_ext))
                elif kind == "pytest":
                    if file_ext != "py":
                        raise SelectorError("pytest selector requires a Python file.")
                    try:
                        slicer = PytestSlicer(content, file_path=file_path)
                        test_names = [t.strip() for t in value.split(",") if t.strip()]
                        sliced_content, _ = slicer.slice(test_names)
                        path_results.append(sliced_content)
                    except SlicerError as e:
                        raise SelectorError(str(e))
            except SelectorError:
                raise
            except Exception as e:
                _report_error(f"Error processing selector '{selector}': {e}", file_path)
                raise SelectorError(f"Error processing selector '{selector}': {e}")

        # Merge spans
        result = ""
        if spans:
            spans.sort()
            merged = [spans[0]]
            for current in spans[1:]:
                last = merged[-1]
                if current[0] <= last[1]: # Overlap or touch
                    merged[-1] = (last[0], max(last[1], current[1]))
                else:
                    merged.append(current)
            
            if mode == "interface" and file_ext == "py":
                result = ContentSelector._generate_interface(content, file_path, filter_spans=merged)
            else:
                extracted_lines = []
                for start, end in merged:
                    extracted_lines.extend(lines[start:end])
                result = "".join(extracted_lines).rstrip('\n')

        if path_results:
            if result:
                result += "\n"
            result += "\n".join(path_results)

        return result

    @staticmethod
    def _process_lines(lines: list[str], value: str) -> list[tuple[int, int]]:
        spans = []
        parts = [p.strip() for p in value.split(",")]
        total_lines = len(lines)
        for part in parts:
            if not part: continue
            if "-" in part:
                start_str, end_str = part.split("-", 1)
                try:
                    start = int(start_str) if start_str else 1
                    end = int(end_str) if end_str else total_lines
                except ValueError:
                    raise SelectorError(f"Malformed selector: Invalid line range syntax: {part}")
            else:
                try:
                    start = end = int(part)
                except ValueError:
                    raise SelectorError(f"Malformed selector: Invalid line number: {part}")
            
            if start < 1 or end > total_lines or start > end:
                raise SelectorError(f"Line number out of range: {part} (total lines: {total_lines})")
            spans.append((start - 1, end))
        return spans

    @staticmethod
    def _process_def(content: str, name: str) -> list[tuple[int, int]]:
        try:
            tree = ast.parse(content)
        except SyntaxError as e:
            raise SelectorError(f"Python parse error: {e}")
        
        spans = []
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name:
                start = node.lineno - 1
                if node.decorator_list:
                    start = min(d.lineno for d in node.decorator_list) - 1
                end = node.end_lineno if node.end_lineno else node.lineno
                spans.append((start, end))
        
        if not spans:
            raise SelectorError(f"Function '{name}' not found.")
        return spans

    @staticmethod
    def _process_class(content: str, value: str) -> list[tuple[int, int]]:
        try:
            tree = ast.parse(content)
        except SyntaxError as e:
            raise SelectorError(f"Python parse error: {e}")
        
        class_name, dot, method_name = value.partition(".")
        spans = []
        
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef) and node.name == class_name:
                if dot:
                    method_found = False
                    for child in node.body:
                        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)) and child.name == method_name:
                            start = child.lineno - 1
                            if child.decorator_list:
                                start = min(d.lineno for d in child.decorator_list) - 1
                            end = child.end_lineno if child.end_lineno else child.lineno
                            spans.append((start, end))
                            method_found = True
                    if not method_found:
                        raise SelectorError(f"Method '{method_name}' not found in class '{class_name}'.")
                else:
                    start = node.lineno - 1
                    if node.decorator_list:
                        start = min(d.lineno for d in node.decorator_list) - 1
                    end = node.end_lineno if node.end_lineno else node.lineno
                    spans.append((start, end))
        
        if not spans:
            raise SelectorError(f"Class '{class_name}' not found.")
        return spans

    @staticmethod
    def _process_section(lines: list[str], heading: str) -> list[tuple[int, int]]:
        spans = []
        heading = heading.strip()
        
        for i, line in enumerate(lines):
            match = re.match(r'^(#{1,6})\s+(.*)', line)
            if match:
                current_level = len(match.group(1))
                current_heading = match.group(2).strip()
                
                if current_heading == heading:
                    start_idx = i
                    end_idx = len(lines)
                    for j in range(i + 1, len(lines)):
                        next_match = re.match(r'^(#{1,6})\s+', lines[j])
                        if next_match:
                            next_level = len(next_match.group(1))
                            if next_level <= current_level:
                                end_idx = j
                                break
                    spans.append((start_idx, end_idx))
            
        if not spans:
            raise SelectorError(f"Markdown section '{heading}' not found.")
        return spans

    @staticmethod
    def _process_pattern(lines: list[str], pattern: str) -> list[tuple[int, int]]:
        if pattern.startswith("/") and pattern.endswith("/"):
            pattern = pattern[1:-1]
        if not pattern:
            raise SelectorError("Empty regex pattern.")
            
        try:
            regex = re.compile(pattern)
        except re.error as e:
            raise SelectorError(f"Invalid regex '{pattern}': {e}")
            
        spans = []

        def handle_timeout(signum, frame):
            raise TimeoutError("Regex pattern matching timed out after 5 seconds.")

        # signal.alarm only works in main thread. We try it, otherwise fallback.
        has_signal = False
        try:
            old_handler = signal.signal(signal.SIGALRM, handle_timeout)
            has_signal = True
        except (ValueError, AttributeError):
            pass

        try:
            for i, line in enumerate(lines):
                if has_signal:
                    signal.alarm(5)
                
                try:
                    if regex.search(line):
                        spans.append((i, i + 1))
                except TimeoutError:
                    raise SelectorError("Regex pattern matching timed out after 5 seconds.")
                finally:
                    if has_signal:
                        signal.alarm(0)
        finally:
            if has_signal:
                signal.signal(signal.SIGALRM, old_handler)
                
        if not spans:
            raise SelectorError(f"No lines matched pattern '{pattern}'.")
        return spans

    @staticmethod
    def _process_path(content: str, path: str, file_ext: str) -> str:
        if file_ext in {"yaml", "yml"}:
            try:
                import yaml
            except ImportError:
                raise SelectorError("PyYAML is not installed. Required for YAML path selectors.")
            try:
                data = yaml.safe_load(content)
            except Exception as e:
                raise SelectorError(f"Failed to parse YAML: {e}")
        else:
            try:
                data = json.loads(content)
            except Exception as e:
                raise SelectorError(f"Failed to parse JSON: {e}")

        if not path:
            raise SelectorError("Empty path provided.")

        parts = []
        for match in re.finditer(r'([^.\[\]]+)|\[(\d+)\]', path):
            if match.group(1):
                parts.append(match.group(1))
            else:
                parts.append(int(match.group(2)))

        current = data
        for part in parts:
            try:
                if isinstance(part, int):
                    if not isinstance(current, list):
                        raise SelectorError(f"Expected array for index '{part}'.")
                    current = current[part]
                else:
                    if not isinstance(current, dict):
                        raise SelectorError(f"Expected object for key '{part}'.")
                    current = current[part]
            except (IndexError, KeyError, TypeError) as e:
                raise SelectorError(f"Path component '{part}' not found: {e}")

        if file_ext in {"yaml", "yml"}:
            import yaml
            return yaml.dump(current, default_flow_style=False).strip()
        else:
            return json.dumps(current, indent=2)

    @staticmethod
    def _generate_interface(content: str, file_path: Optional[str], filter_spans: list[tuple[int, int]] | None = None) -> str:
        try:
            tree = ast.parse(content)
        except SyntaxError as e:
            raise SelectorError(f"Python parse error: {e}")

        lines = content.splitlines(keepends=True)
        interface_lines: list[str] = []

        def is_overlapping(node_start: int, node_end: int) -> bool:
            if filter_spans is None:
                return True
            for span_start, span_end in filter_spans:
                if max(node_start - 1, span_start) < min(node_end, span_end):
                    return True
            return False

        def get_node_span(node: ast.AST) -> tuple[int, int]:
            start = node.lineno
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.decorator_list:
                start = min(d.lineno for d in node.decorator_list)
            end = getattr(node, "end_lineno", start)
            return start, end

        def process_function(node: Union[ast.FunctionDef, ast.AsyncFunctionDef], indent: str = "") -> str:
            start, end = get_node_span(node)
            first_stmt = node.body[0]
            body_start_line = first_stmt.lineno
            
            header_lines = lines[start - 1 : body_start_line - 1]
            if not header_lines:
                full_line = lines[node.lineno - 1]
                match = re.search(r':', full_line)
                if match:
                    header = full_line[:match.start() + 1] + "\n"
                else:
                    header = full_line
            else:
                header = "".join(header_lines)
            
            docstring = ast.get_docstring(node)
            if docstring:
                doc_node = node.body[0]
                if isinstance(doc_node, ast.Expr) and isinstance(doc_node.value, (ast.Str, ast.Constant)):
                    doc_end = doc_node.end_lineno
                    header += "".join(lines[body_start_line - 1 : doc_end])
            
            if not header.endswith("\n"):
                header += "\n"
                
            body_line = lines[first_stmt.lineno - 1]
            body_indent = body_line[:len(body_line) - len(body_line.lstrip())]
            if not body_indent or len(body_indent) <= len(indent):
                body_indent = indent + "    "
            
            header += f"{body_indent}...\n"
            return header

        def process_class(node: ast.ClassDef) -> str:
            start, end = get_node_span(node)
            first_stmt = node.body[0]
            last_header_line = first_stmt.lineno - 1
            
            class_interface = "".join(lines[start - 1 : last_header_line])
            if not class_interface.endswith("\n"):
                class_interface += "\n"
                
            docstring = ast.get_docstring(node)
            if docstring:
                doc_node = node.body[0]
                if isinstance(doc_node, ast.Expr) and isinstance(doc_node.value, (ast.Str, ast.Constant)):
                    class_interface += "".join(lines[doc_node.lineno - 1 : doc_node.end_lineno])
                    if not class_interface.endswith("\n"):
                        class_interface += "\n"
            
            for child in node.body:
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if child.name == "__init__" or not child.name.startswith("_"):
                        class_interface += process_function(child, indent="    ")
                elif isinstance(child, (ast.Assign, ast.AnnAssign)):
                    is_public = True
                    if isinstance(child, ast.Assign):
                        for target in child.targets:
                            if isinstance(target, ast.Name) and target.id.startswith("_"):
                                is_public = False
                    elif isinstance(child, ast.AnnAssign):
                        if isinstance(child.target, ast.Name) and child.target.id.startswith("_"):
                            is_public = False
                    
                    if is_public:
                        c_start, c_end = get_node_span(child)
                        class_interface += "".join(lines[c_start - 1 : c_end])
            
            return class_interface

        module_docstring = ast.get_docstring(tree)
        if module_docstring:
            doc_node = tree.body[0]
            if isinstance(doc_node, ast.Expr) and isinstance(doc_node.value, (ast.Str, ast.Constant)):
                start, end = get_node_span(doc_node)
                if is_overlapping(start, end):
                    interface_lines.append("".join(lines[start-1:end]))

        for node in tree.body:
            start, end = get_node_span(node)
            if not is_overlapping(start, end):
                continue

            if isinstance(node, (ast.Import, ast.ImportFrom)):
                interface_lines.append("".join(lines[start-1:end]))
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if not node.name.startswith("_"):
                    interface_lines.append("\n" + process_function(node))
            elif isinstance(node, ast.ClassDef):
                if not node.name.startswith("_"):
                    interface_lines.append("\n" + process_class(node))
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                is_public = True
                if isinstance(node, ast.Assign):
                    for target in node.targets:
                        if isinstance(target, ast.Name) and target.id.startswith("_"):
                            is_public = False
                elif isinstance(node, ast.AnnAssign):
                    if isinstance(node.target, ast.Name) and node.target.id.startswith("_"):
                        is_public = False
                
                if is_public:
                    interface_lines.append("".join(lines[start-1:end]))

        result = "".join(interface_lines).strip() + "\n"
        
        if filter_spans and not result.strip():
            extracted_lines = []
            for start, end in filter_spans:
                extracted_lines.extend(lines[start:end])
            result = "".join(extracted_lines).rstrip('\n')

        return result


def _report_error(msg: str, file_path: str | None = None) -> None:
    if file_path:
        console.print(f"[path]{file_path}[/path]: ", end="")
    console.print(f"[error]Error:[/error] {msg}")
