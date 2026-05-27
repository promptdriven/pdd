#!/usr/bin/env python3
import json
import ast
import os
import sys
from pathlib import Path

def resolve_module_path(current_file_path: Path, module_name: str, level: int) -> Path | None:
    """Resolve a relative or absolute local import to its python file path."""
    if level > 0:
        # Relative import, e.g. from .agentic_common import ...
        base_dir = current_file_path.parent
        for _ in range(level - 1):
            base_dir = base_dir.parent
        if not module_name:
            target_path = base_dir / "__init__.py"
            if target_path.exists():
                return target_path
            return None
        parts = module_name.split('.')
        target_path = base_dir.joinpath(*parts)
        py_file = target_path.with_suffix('.py')
        if py_file.exists():
            return py_file
        init_file = target_path / "__init__.py"
        if init_file.exists():
            return init_file
        return None
    else:
        # Absolute import, e.g. from pdd.cli_branding import ...
        if not module_name:
            return None
        parts = module_name.split('.')
        if parts[0] not in ('pdd', 'extensions', 'utils'):
            return None
        
        target_path = Path(parts[0]).joinpath(*parts[1:])
        py_file = target_path.with_suffix('.py')
        if py_file.exists():
            return py_file
        init_file = target_path / "__init__.py"
        if init_file.exists():
            return init_file
        return None

def parse_file_exports(file_path: Path) -> dict:
    """Parse functions, classes, globals, and imports from a Python file AST."""
    if not file_path.exists():
        return {}
    try:
        content = file_path.read_text(encoding='utf-8')
        tree = ast.parse(content, filename=str(file_path))
    except Exception as e:
        return {"error": str(e)}

    exports = {
        "functions": set(),
        "classes": {},
        "globals": set()
    }

    # Helper to recursively extract variables assigned in Try, If, etc.
    def extract_globals(node_list):
        for node in node_list:
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        exports["globals"].add(target.id)
            elif isinstance(node, ast.AnnAssign):
                if isinstance(node.target, ast.Name):
                    exports["globals"].add(node.target.id)
            elif isinstance(node, (ast.Try, ast.TryStar)):
                extract_globals(node.body)
                extract_globals(node.handlers)
                extract_globals(node.finalbody)
                extract_globals(node.orelse)
            elif isinstance(node, ast.If):
                extract_globals(node.body)
                extract_globals(node.orelse)
            elif isinstance(node, ast.ExceptHandler):
                extract_globals(node.body)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            exports["functions"].add(node.name)
        elif isinstance(node, ast.ClassDef):
            class_methods = set()
            for subnode in node.body:
                if isinstance(subnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    class_methods.add(subnode.name)
            exports["classes"][node.name] = {
                "methods": class_methods
            }
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            # Imports are also exports if other files import from us
            for name in node.names:
                export_name = name.asname if name.asname else name.name
                exports["globals"].add(export_name)
    
    extract_globals(tree.body)
    return exports

def get_file_imports(file_path: Path) -> list:
    """Extract all import statements from a Python file AST."""
    if not file_path.exists():
        return []
    try:
        content = file_path.read_text(encoding='utf-8')
        tree = ast.parse(content, filename=str(file_path))
    except Exception:
        return []

    imports = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for name in node.names:
                imports.append({
                    "module": name.name,
                    "names": None,
                    "level": 0,
                    "lineno": node.lineno
                })
        elif isinstance(node, ast.ImportFrom):
            imported_names = [name.name for name in node.names]
            imports.append({
                "module": node.module,
                "names": imported_names,
                "level": node.level,
                "lineno": node.lineno
            })
    return imports

def main():
    arch_path = Path("architecture.json")
    if not arch_path.exists():
        print("ERROR: architecture.json not found.")
        sys.exit(1)

    with open(arch_path, 'r', encoding='utf-8') as f:
        try:
            arch_data = json.load(f)
        except Exception as e:
            print(f"ERROR parsing architecture.json: {e}")
            sys.exit(1)

    # 1. Map filename -> module metadata
    modules_by_filepath = {}
    modules_by_filename = {}
    for entry in arch_data:
        filepath = entry.get("filepath")
        filename = entry.get("filename")
        if filepath:
            modules_by_filepath[filepath] = entry
        if filename:
            modules_by_filename[filename] = entry

    all_parsed_exports = {}
    issues = []
    dependency_graph = {}

    print("=== Scanning Local Modules & Parsing AST ===")
    for filepath, entry in modules_by_filepath.items():
        p = Path(filepath)
        if not p.exists():
            if filepath.endswith('.py'):
                issues.append({
                    "module": entry.get("filename", filepath),
                    "issue_type": "missing_file",
                    "description": f"File defined in architecture.json does not exist: {filepath}"
                })
            continue

        if filepath.endswith('.py'):
            exports = parse_file_exports(p)
            if "error" in exports:
                issues.append({
                    "module": entry.get("filename", filepath),
                    "issue_type": "syntax_error",
                    "description": f"Syntax error or parse failure in {filepath}: {exports['error']}"
                })
            else:
                all_parsed_exports[filepath] = exports

    print("=== Verifying Module Exports against architecture.json ===")
    for filepath, entry in modules_by_filepath.items():
        if not filepath.endswith('.py') or filepath not in all_parsed_exports:
            continue

        exports = all_parsed_exports[filepath]
        interface = entry.get("interface", {})
        if not interface:
            continue

        if interface.get("type") == "module":
            module_config = interface.get("module", {})
            declared_functions = module_config.get("functions", [])
            for df in declared_functions:
                name = df.get("name")
                if not name:
                    continue
                if '.' in name:
                    class_name, method_name = name.split('.', 1)
                    if class_name not in exports["classes"]:
                        issues.append({
                            "module": entry.get("filename", filepath),
                            "issue_type": "missing_export",
                            "description": f"Class '{class_name}' declared in interface not found in {filepath}"
                        })
                    else:
                        methods = exports["classes"][class_name]["methods"]
                        if method_name not in methods:
                            issues.append({
                                "module": entry.get("filename", filepath),
                                "issue_type": "missing_export",
                                "description": f"Method '{class_name}.{method_name}' declared in interface not found in {filepath}"
                            })
                else:
                    if name not in exports["functions"] and name not in exports["globals"] and name not in exports["classes"]:
                        if name == "__init__":
                            continue
                        issues.append({
                            "module": entry.get("filename", filepath),
                            "issue_type": "missing_export",
                            "description": f"Function '{name}' declared in interface not found in {filepath}"
                        })

    print("=== Verifying Import Correctness and Symbol Bindings ===")
    for filepath, entry in modules_by_filepath.items():
        if not filepath.endswith('.py'):
            continue
        p = Path(filepath)
        file_imports = get_file_imports(p)
        filename = entry.get("filename", filepath)
        
        dependency_graph[filename] = set()

        for imp in file_imports:
            module_name = imp["module"]
            level = imp["level"]
            names = imp["names"]
            lineno = imp["lineno"]

            target_py_path = resolve_module_path(p, module_name, level)
            if target_py_path:
                target_filepath_str = target_py_path.as_posix()
                target_entry = modules_by_filepath.get(target_filepath_str)
                if target_entry:
                    target_filename = target_entry.get("filename")
                    if target_filename:
                        dependency_graph[filename].add(target_filename)

                # Check if imported names actually exist in target module
                if names and target_filepath_str in all_parsed_exports:
                    target_exports = all_parsed_exports[target_filepath_str]
                    for name in names:
                        if name == '*':
                            continue
                        
                        name_exists = (
                            name in target_exports.get("functions", set()) or
                            name in target_exports.get("classes", {}) or
                            name in target_exports.get("globals", set())
                        )
                        if not name_exists:
                            issues.append({
                                "module": filename,
                                "issue_type": "missing_import_symbol",
                                "description": f"Imported symbol '{name}' from '{module_name}' at line {lineno} does not exist in {target_filepath_str}"
                            })
            elif level == 0 and module_name:
                parts = module_name.split('.')
                if parts[0] in ('pdd', 'extensions', 'utils'):
                    issues.append({
                        "module": filename,
                        "issue_type": "broken_import_path",
                        "description": f"Broken import '{module_name}' at line {lineno} in {filepath} (file does not exist)"
                    })

    print("=== Verifying Cross-Module Dependencies in architecture.json ===")
    for filepath, entry in modules_by_filepath.items():
        filename = entry.get("filename")
        deps = entry.get("dependencies", [])
        for dep in deps:
            if dep not in modules_by_filename:
                issues.append({
                    "module": filename,
                    "issue_type": "broken_architecture_dependency",
                    "description": f"Module '{filename}' depends on '{dep}', which is not defined in architecture.json"
                })

    print("=== Checking for Circular Import Cycles in Local Modules ===")
    visited = {}
    path = []
    cycles = []

    def dfs(node):
        if node in path:
            cycle_start = path.index(node)
            cycles.append(path[cycle_start:] + [node])
            return
        if visited.get(node) == 'done':
            return
        visited[node] = 'visiting'
        path.append(node)
        for neighbor in dependency_graph.get(node, []):
            dfs(neighbor)
        path.pop()
        visited[node] = 'done'

    for node in list(dependency_graph.keys()):
        dfs(node)

    for cycle in cycles:
        issues.append({
            "module": " -> ".join(cycle),
            "issue_type": "circular_import",
            "description": f"Circular import cycle detected: {' -> '.join(cycle)}"
        })

    print(f"=== Validation Complete. Found {len(issues)} issues. ===")
    results = {
        "valid": len(issues) == 0,
        "issues": issues
    }
    
    with open("interface_validation_report.json", "w") as out:
        json.dump(results, out, indent=2)

if __name__ == "__main__":
    main()
