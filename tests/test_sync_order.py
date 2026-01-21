import os
import stat
import pytest
import logging
from pathlib import Path
from unittest.mock import MagicMock, patch
from z3 import Solver, Int, Distinct, Implies, sat, And

# Import the module under test
# Assuming the file structure allows this import, or adjusting path as necessary
import pdd.sync_order as sync_order

# ==============================================================================
# Fixtures
# ==============================================================================

@pytest.fixture
def temp_prompts_dir(tmp_path):
    """Creates a temporary directory for prompt files."""
    d = tmp_path / "prompts"
    d.mkdir()
    return d

@pytest.fixture
def mock_logger():
    """Mocks the logger to verify warning/error calls."""
    with patch("pdd.sync_order.logger") as mock:
        yield mock

# ==============================================================================
# Unit Tests: extract_includes_from_file
# ==============================================================================

def test_extract_includes_happy_path(tmp_path):
    """Test extracting includes from a valid file."""
    f = tmp_path / "test.prompt"
    f.write_text("Some text\n<include>path/to/a</include>\n<include>path/to/b</include>", encoding="utf-8")
    
    includes = sync_order.extract_includes_from_file(f)
    assert includes == {"path/to/a", "path/to/b"}

def test_extract_includes_whitespace(tmp_path):
    """Test that whitespace is stripped from includes."""
    f = tmp_path / "test.prompt"
    f.write_text("<include>  path/to/a  \n</include>", encoding="utf-8")
    
    includes = sync_order.extract_includes_from_file(f)
    assert includes == {"path/to/a"}

def test_extract_includes_file_not_found(mock_logger):
    """Test behavior when file does not exist."""
    f = Path("non_existent_file.prompt")
    includes = sync_order.extract_includes_from_file(f)
    
    assert includes == set()
    mock_logger.warning.assert_called()

def test_extract_includes_empty_file(tmp_path):
    """Test parsing an empty file."""
    f = tmp_path / "empty.prompt"
    f.write_text("", encoding="utf-8")
    assert sync_order.extract_includes_from_file(f) == set()

# ==============================================================================
# Unit Tests: extract_module_from_include
# ==============================================================================

@pytest.mark.parametrize("include_path, expected", [
    ("prompts/cli_python.prompt", "cli"),
    ("prompts/api_typescript.prompt", "api"),
    ("context/llm_invoke_example.py", "llm_invoke"),
    ("context/utils_example.ts", "utils"),
    ("simple_python.prompt", "simple"),
    ("prompts/complex_name_example_python.prompt", "complex_name"), # Order of stripping check
])
def test_extract_module_valid(include_path, expected):
    """Test extraction of module names from valid paths."""
    assert sync_order.extract_module_from_include(include_path) == expected

@pytest.mark.parametrize("include_path", [
    "context/preamble.prompt",  # No language suffix, should be excluded
    "context/shared.py",        # Not a prompt file
    "README.md",                # Not a prompt file
    "prompts/logic_LLM.prompt", # LLM prompts are runtime, not code generation
])
def test_extract_module_invalid(include_path):
    """Test that invalid paths return None."""
    assert sync_order.extract_module_from_include(include_path) is None

def test_extract_module_suffix_stripping_order():
    """Ensure _example is stripped correctly even if combined with language."""
    # Code logic: strips language first, then _example.
    # e.g. "foo_example_python" -> strip _python -> "foo_example" -> strip _example -> "foo"
    assert sync_order.extract_module_from_include("foo_example_python.prompt") == "foo"


def test_extract_module_excludes_llm_includes_all_languages():
    """
    Test that extract_module_from_include:
    - Returns None for LLM prompts (runtime, not code generation)
    - Works for ANY language suffix (python, typescript, java, go, rust, etc.)
    """
    # LLM prompts should return None
    assert sync_order.extract_module_from_include("prompts/foo_LLM.prompt") is None
    assert sync_order.extract_module_from_include("agentic_step9_LLM.prompt") is None

    # All code generation languages should work
    assert sync_order.extract_module_from_include("prompts/foo_python.prompt") == "foo"
    assert sync_order.extract_module_from_include("prompts/bar_typescript.prompt") == "bar"
    assert sync_order.extract_module_from_include("prompts/baz_java.prompt") == "baz"
    assert sync_order.extract_module_from_include("prompts/qux_go.prompt") == "qux"
    assert sync_order.extract_module_from_include("prompts/quux_rust.prompt") == "quux"


# ==============================================================================
# Unit Tests: build_dependency_graph
# ==============================================================================

def test_build_dependency_graph_basic(temp_prompts_dir):
    """Test building a simple dependency graph."""
    # Create module A
    (temp_prompts_dir / "a_python.prompt").write_text("", encoding="utf-8")
    
    # Create module B that includes A
    (temp_prompts_dir / "b_python.prompt").write_text("<include>prompts/a_python.prompt</include>", encoding="utf-8")
    
    graph = sync_order.build_dependency_graph(temp_prompts_dir)
    
    # B depends on A. Graph keys are modules.
    # Logic: current_module = B. dep_module = A.
    # dependency_graph[B].add(A)
    
    assert "a" in graph
    assert "b" in graph
    assert "a" in graph["b"] # B depends on A
    assert graph["a"] == []  # A has no dependencies

def test_build_dependency_graph_self_reference(temp_prompts_dir):
    """Test that self-references are ignored."""
    (temp_prompts_dir / "self_python.prompt").write_text("<include>prompts/self_python.prompt</include>", encoding="utf-8")
    
    graph = sync_order.build_dependency_graph(temp_prompts_dir)
    assert "self" in graph
    assert graph["self"] == []

def test_build_dependency_graph_missing_dir(mock_logger):
    """Test handling of missing directory."""
    graph = sync_order.build_dependency_graph(Path("/non/existent/path"))
    assert graph == {}
    mock_logger.error.assert_called()


def test_build_dependency_graph_nested_directories(temp_prompts_dir):
    """
    Test that build_dependency_graph finds prompts in nested subdirectories.

    Regression test for bug where prompts in subdirectories like
    prompts/backend/models/ were not discovered because glob() was
    used instead of rglob().
    """
    # Create nested directory structure (mimics prompts/backend/models/)
    backend_dir = temp_prompts_dir / "backend" / "models"
    backend_dir.mkdir(parents=True)

    # Create prompt files at different nesting levels
    (backend_dir / "foo_python.prompt").write_text("% foo module", encoding="utf-8")
    (temp_prompts_dir / "backend" / "bar_python.prompt").write_text(
        "<include>prompts/backend/models/foo_python.prompt</include>",
        encoding="utf-8"
    )

    graph = sync_order.build_dependency_graph(temp_prompts_dir)

    # Verify modules are discovered (rglob finds nested files)
    assert "foo" in graph, f"foo not found in graph: {graph}"
    assert "bar" in graph, f"bar not found in graph: {graph}"

    # Verify dependency parsing works for nested paths
    assert "foo" in graph["bar"], f"bar should depend on foo: {graph}"
    assert graph["foo"] == [], f"foo should have no dependencies: {graph}"


def test_build_dependency_graph_excludes_llm_includes_all_languages(temp_prompts_dir):
    """
    Test that build_dependency_graph:
    - Excludes LLM prompts from the graph
    - Includes prompts for ANY language (not just python/typescript)
    """
    # Create various prompt types
    (temp_prompts_dir / "foo_python.prompt").write_text("% foo", encoding="utf-8")
    (temp_prompts_dir / "bar_typescript.prompt").write_text("% bar", encoding="utf-8")
    (temp_prompts_dir / "baz_java.prompt").write_text("% baz", encoding="utf-8")
    (temp_prompts_dir / "qux_go.prompt").write_text("% qux", encoding="utf-8")
    (temp_prompts_dir / "runtime_LLM.prompt").write_text("% runtime", encoding="utf-8")

    graph = sync_order.build_dependency_graph(temp_prompts_dir)

    # All code generation prompts should be in the graph
    assert "foo" in graph, f"foo (python) not found: {graph}"
    assert "bar" in graph, f"bar (typescript) not found: {graph}"
    assert "baz" in graph, f"baz (java) not found: {graph}"
    assert "qux" in graph, f"qux (go) not found: {graph}"

    # LLM prompts should NOT be in the graph
    assert "runtime" not in graph, f"runtime (LLM) should not be in graph: {graph}"


# ==============================================================================
# Unit Tests: topological_sort
# ==============================================================================

def test_topological_sort_linear():
    """Test sorting a linear dependency chain: C -> B -> A."""
    # C depends on B, B depends on A.
    # Expected order: A, B, C
    graph = {
        "c": ["b"],
        "b": ["a"],
        "a": []
    }
    sorted_list, cycles = sync_order.topological_sort(graph)
    assert cycles == []
    assert sorted_list == ["a", "b", "c"]

def test_topological_sort_diamond():
    """Test sorting a diamond dependency."""
    # D -> B, D -> C, B -> A, C -> A
    # A is base. B and C depend on A. D depends on B and C.
    graph = {
        "d": ["b", "c"],
        "b": ["a"],
        "c": ["a"],
        "a": []
    }
    sorted_list, cycles = sync_order.topological_sort(graph)
    assert cycles == []
    
    # A must be first
    assert sorted_list[0] == "a"
    # D must be last
    assert sorted_list[-1] == "d"
    # B and C are in the middle (order between them doesn't matter)
    assert set(sorted_list[1:3]) == {"b", "c"}

def test_topological_sort_cycle():
    """Test cycle detection."""
    # A -> B -> A
    graph = {
        "a": ["b"],
        "b": ["a"]
    }
    sorted_list, cycles = sync_order.topological_sort(graph)
    
    # Should detect cycle
    assert len(cycles) > 0
    # Sorted list might be empty or partial
    assert len(sorted_list) < 2

def test_topological_sort_disconnected():
    """Test sorting disconnected components."""
    # A -> B, C -> D
    graph = {
        "a": ["b"],
        "b": [],
        "c": ["d"],
        "d": []
    }
    sorted_list, cycles = sync_order.topological_sort(graph)
    assert cycles == []
    assert len(sorted_list) == 4
    
    # Check relative ordering
    assert sorted_list.index("b") < sorted_list.index("a")
    assert sorted_list.index("d") < sorted_list.index("c")

# ==============================================================================
# Unit Tests: get_affected_modules
# ==============================================================================

def test_get_affected_modules_leaf():
    """Test modifying a leaf node (no dependents)."""
    # C -> B -> A
    # Graph input is Module -> Dependencies
    graph = {"c": ["b"], "b": ["a"], "a": []}
    sorted_modules = ["a", "b", "c"]
    
    # Modify C (leaf in dependency tree, but 'root' in terms of who depends on it? No.)
    # Wait, terminology:
    # "C depends on B". If I change C, only C needs sync.
    # If I change B, B needs sync, and C needs sync (because C includes B).
    
    # Case 1: Modify C. No one depends on C.
    affected = sync_order.get_affected_modules(sorted_modules, {"c"}, graph)
    assert affected == ["c"]

def test_get_affected_modules_root():
    """Test modifying a root dependency."""
    # C -> B -> A
    graph = {"c": ["b"], "b": ["a"], "a": []}
    sorted_modules = ["a", "b", "c"]
    
    # Modify A. B depends on A. C depends on B.
    # All should be affected.
    affected = sync_order.get_affected_modules(sorted_modules, {"a"}, graph)
    assert affected == ["a", "b", "c"]

def test_get_affected_modules_branch():
    """Test modifying a node in a branch."""
    # D -> B, D -> C, B -> A, C -> A
    graph = {"d": ["b", "c"], "b": ["a"], "c": ["a"], "a": []}
    sorted_modules = ["a", "b", "c", "d"] # One valid sort
    
    # Modify B. D depends on B. C does not. A does not.
    # Affected: B, D.
    affected = sync_order.get_affected_modules(sorted_modules, {"b"}, graph)
    assert affected == ["b", "d"]

def test_get_affected_modules_none_modified():
    """Test with empty modified set."""
    graph = {"a": []}
    assert sync_order.get_affected_modules(["a"], set(), graph) == []

# ==============================================================================
# Unit Tests: generate_sync_order_script
# ==============================================================================

def test_generate_sync_order_script_content(tmp_path):
    """Test script generation content."""
    output = tmp_path / "sync.sh"
    modules = ["base", "lib", "app"]
    
    content = sync_order.generate_sync_order_script(modules, output)
    
    assert "#!/bin/bash" in content
    assert "pdd sync base" in content
    assert "pdd sync lib" in content
    assert "pdd sync app" in content
    
    # Check order
    base_idx = content.find("pdd sync base")
    lib_idx = content.find("pdd sync lib")
    app_idx = content.find("pdd sync app")
    assert base_idx < lib_idx < app_idx

def test_generate_sync_order_script_executable(tmp_path):
    """Test that the generated script is executable."""
    output = tmp_path / "sync.sh"
    sync_order.generate_sync_order_script(["foo"], output)
    
    st = os.stat(output)
    assert bool(st.st_mode & stat.S_IEXEC)

def test_generate_sync_order_script_empty(tmp_path):
    """Test that no script is generated for empty modules."""
    output = tmp_path / "sync.sh"
    content = sync_order.generate_sync_order_script([], output)
    assert content == ""
    assert not output.exists()

# ==============================================================================
# Z3 Formal Verification Tests
# ==============================================================================

def test_z3_topological_sort_correctness():
    """
    Uses Z3 to verify that the topological sort output respects all dependency constraints.
    We construct a scenario where we have a known graph, run the python function,
    and then use Z3 to verify the result is a valid topological ordering.
    """
    # Define a complex graph
    # A -> []
    # B -> [A]
    # C -> [A]
    # D -> [B, C]
    # E -> [D]
    graph = {
        "e": ["d"],
        "d": ["b", "c"],
        "c": ["a"],
        "b": ["a"],
        "a": []
    }
    
    # Run the actual implementation
    sorted_modules, cycles = sync_order.topological_sort(graph)
    
    assert not cycles, "Cycle detected in acyclic graph"
    
    # Z3 Verification
    s = Solver()
    
    # Create integer variables representing the position (index) of each module in the sorted list
    # positions["a"] = index of "a" in sorted_modules
    positions = {m: Int(f"pos_{m}") for m in graph.keys()}
    
    # Constraint 1: All positions must be distinct and within valid range
    s.add(Distinct(*positions.values()))
    for m in graph:
        s.add(positions[m] >= 0)
        s.add(positions[m] < len(graph))
    
    # Constraint 2: Dependency Ordering
    # If M depends on D (M -> [D]), then D must come BEFORE M (pos_D < pos_M)
    for module, dependencies in graph.items():
        for dep in dependencies:
            s.add(positions[dep] < positions[module])
            
    # Constraint 3: The specific ordering returned by the Python function
    # We assert that the positions found by Z3 match the indices in our result list
    # If Z3 is SAT, it means our result is ONE OF the valid topological sorts.
    # However, to prove OUR result is valid, we simply check if OUR result satisfies the constraints.
    
    # Let's verify our specific result satisfies the constraints.
    # We bind the Z3 variables to the actual indices from the result.
    for idx, mod in enumerate(sorted_modules):
        s.add(positions[mod] == idx)
        
    # If UNSAT, it means our result violated a dependency constraint
    result = s.check()
    if result != sat:
        pytest.fail(f"Z3 Verification Failed: The generated sort order {sorted_modules} violates dependency constraints.")

def test_z3_cycle_detection_property():
    """
    Uses Z3 to verify that if a cycle exists, the topological sort cannot complete fully.
    """
    # Graph with a cycle: A -> B -> C -> A
    graph = {
        "a": ["b"],
        "b": ["c"],
        "c": ["a"],
        "d": [] # D is independent
    }
    
    sorted_modules, cycles = sync_order.topological_sort(graph)
    
    # Property: If cycles exist, we cannot assign unique positions 0..N-1 such that for all edges u->v, pos(v) < pos(u).
    # (Note: In our graph dict, key depends on value. So key is dependent, value is dependency.
    #  So dependency must be earlier. pos(val) < pos(key))
    
    s = Solver()
    positions = {m: Int(f"pos_{m}") for m in graph.keys()}
    
    # Valid range
    for m in graph:
        s.add(positions[m] >= 0)
        s.add(positions[m] < len(graph))
    s.add(Distinct(*positions.values()))
    
    # Dependency constraints
    for module, dependencies in graph.items():
        for dep in dependencies:
            s.add(positions[dep] < positions[module])
            
    # This should be UNSAT because of the cycle
    assert s.check() != sat, "Z3 found a valid topological sort for a cyclic graph, which is impossible."
    
    # Verify Python code detected it
    assert len(cycles) > 0
    assert "d" in sorted_modules # D should be sorted as it's not in cycle