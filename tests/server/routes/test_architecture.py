"""
Test Plan for pdd/server/routes/architecture.py

1. **Unit Tests**:
    - **Valid Architecture**: Verify a standard dependency tree (A->B, A->C) passes validation with no errors or warnings.
    - **Circular Dependencies**:
        - Direct cycle (A->B->A).
        - Self cycle (A->A).
        - Deep cycle (A->B->C->A).
        - Verify that `valid=False` and error type is `circular_dependency`.
        - Verify the reported cycle path structure.
    - **Missing Dependencies**:
        - Module depends on a filename that doesn't exist in the module list.
        - Verify `valid=False` and error type is `missing_dependency`.
    - **Invalid Fields**:
        - Test empty `filename`, `filepath`, `description`.
        - Verify `valid=False` and error type is `invalid_field`.
    - **Warnings**:
        - **Duplicate Dependencies**: Module lists same dependency twice. Verify `valid=True` (if no errors) and warning present.
        - **Orphan Modules**: Module with no dependencies and no incoming edges. Verify `valid=True` and warning present.
    - **Complex Mixed Case**:
        - Combination of valid modules, orphans, and cycles to ensure all are reported correctly in the result.

2. **Formal Verification (Z3)**:
    - **DAG Generation**: Use Z3 to synthesize a non-trivial Directed Acyclic Graph (DAG) structure by enforcing rank constraints (edge(u,v) implies rank(u) < rank(v)).
        - Convert the Z3 model into `ArchitectureModule` objects.
        - Assert that the validator returns `valid=True` and finds 0 cycles.
    - **Cycle Generation**: Use Z3 to synthesize a graph structure that contains a cycle of a specific length.
        - Convert to modules.
        - Assert that the validator returns `valid=False` and identifies the circular dependency.
"""

import pytest
import asyncio
from typing import List, Dict, Any
from pdd.server.routes.architecture import (
    validate_architecture,
    ValidateArchitectureRequest,
    ArchitectureModule,
    ValidationResult,
    ValidationError,
    ValidationWarning
)

# Helper to create modules quickly
def create_module(
    filename: str, 
    dependencies: List[str] = None, 
    description: str = "desc", 
    filepath: str = None
) -> ArchitectureModule:
    if dependencies is None:
        dependencies = []
    if filepath is None:
        filepath = f"src/{filename}"
    
    return ArchitectureModule(
        reason="test",
        description=description,
        dependencies=dependencies,
        priority=1,
        filename=filename,
        filepath=filepath,
        tags=[],
        interface={}
    )

@pytest.mark.asyncio
async def test_validate_architecture_valid_simple():
    """Test a simple valid dependency chain A -> B -> C."""
    modules = [
        create_module("A.py", ["B.py"]),
        create_module("B.py", ["C.py"]),
        create_module("C.py", [])
    ]
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    assert result.valid is True
    assert len(result.errors) == 0
    assert len(result.warnings) == 0

@pytest.mark.asyncio
async def test_validate_architecture_circular_direct():
    """Test detection of a direct circular dependency A -> B -> A."""
    modules = [
        create_module("A.py", ["B.py"]),
        create_module("B.py", ["A.py"])
    ]
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    assert result.valid is False
    assert len(result.errors) > 0
    
    # Check for circular dependency error
    circle_errors = [e for e in result.errors if e.type == "circular_dependency"]
    assert len(circle_errors) >= 1
    
    # The cycle might be reported starting from A or B, but should contain both
    cycle_modules = set(circle_errors[0].modules)
    assert "A.py" in cycle_modules
    assert "B.py" in cycle_modules

@pytest.mark.asyncio
async def test_validate_architecture_circular_self():
    """Test detection of a self-referencing module A -> A."""
    modules = [
        create_module("A.py", ["A.py"])
    ]
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    assert result.valid is False
    circle_errors = [e for e in result.errors if e.type == "circular_dependency"]
    assert len(circle_errors) == 1
    assert circle_errors[0].modules == ["A.py", "A.py"]

@pytest.mark.asyncio
async def test_validate_architecture_missing_dependency():
    """Test detection of dependencies on non-existent modules."""
    modules = [
        create_module("A.py", ["NonExistent.py"])
    ]
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    assert result.valid is False
    missing_errors = [e for e in result.errors if e.type == "missing_dependency"]
    assert len(missing_errors) == 1
    assert "NonExistent.py" in missing_errors[0].message
    assert "A.py" in missing_errors[0].modules

@pytest.mark.asyncio
async def test_validate_architecture_invalid_fields():
    """Test validation of required fields (filename, filepath, description)."""
    modules = [
        create_module("", [], description="valid", filepath="valid"),  # Empty filename
        create_module("B.py", [], description="", filepath="valid"),   # Empty description
        create_module("C.py", [], description="valid", filepath=""),   # Empty filepath
    ]
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    assert result.valid is False
    field_errors = [e for e in result.errors if e.type == "invalid_field"]
    assert len(field_errors) == 3

@pytest.mark.asyncio
async def test_validate_architecture_duplicate_dependency_warning():
    """Test warning generation for duplicate dependencies."""
    modules = [
        create_module("A.py", ["B.py", "B.py"]),
        create_module("B.py", [])
    ]
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    # Should be valid as duplicates are just warnings
    assert result.valid is True
    assert len(result.errors) == 0
    
    warnings = [w for w in result.warnings if w.type == "duplicate_dependency"]
    assert len(warnings) == 1
    assert "B.py" in warnings[0].message
    assert warnings[0].modules == ["A.py"]

@pytest.mark.asyncio
async def test_validate_architecture_orphan_module_warning():
    """Test warning generation for orphan modules (no deps, no incoming edges)."""
    modules = [
        create_module("Connected1.py", ["Connected2.py"]),
        create_module("Connected2.py", []),
        create_module("Orphan.py", [])  # No outgoing, no incoming
    ]
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    assert result.valid is True
    warnings = [w for w in result.warnings if w.type == "orphan_module"]
    assert len(warnings) == 1
    assert warnings[0].modules == ["Orphan.py"]

@pytest.mark.asyncio
async def test_validate_architecture_complex_mixed():
    """Test a mix of valid structures, cycles, and orphans."""
    modules = [
        # Cycle
        create_module("C1.py", ["C2.py"]),
        create_module("C2.py", ["C1.py"]),
        
        # Orphan
        create_module("Orphan.py", []),
        
        # Valid chain
        create_module("V1.py", ["V2.py"]),
        create_module("V2.py", [])
    ]
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    assert result.valid is False
    
    # Check errors
    assert any(e.type == "circular_dependency" for e in result.errors)
    
    # Check warnings
    assert any(w.type == "orphan_module" for w in result.warnings)

# -----------------------------------------------------------------------------
# Z3 Formal Verification Tests
# -----------------------------------------------------------------------------

try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

@pytest.mark.skipif(not Z3_AVAILABLE, reason="z3-solver not installed")
@pytest.mark.asyncio
async def test_z3_generated_dag_is_valid():
    """
    Formal Verification:
    Use Z3 to generate a random Directed Acyclic Graph (DAG).
    Verify that the architecture validator correctly identifies it as valid (no cycles).
    """
    solver = z3.Solver()
    
    # Parameters
    N = 5  # Number of nodes
    nodes = [f"Node_{i}" for i in range(N)]
    
    # Variables: edge[i][j] is boolean
    edges = [[z3.Bool(f"e_{i}_{j}") for j in range(N)] for i in range(N)]
    
    # Variables: rank[i] is integer (for topological sort)
    ranks = [z3.Int(f"r_{i}") for i in range(N)]
    
    # Constraint 1: No self loops
    for i in range(N):
        solver.add(z3.Not(edges[i][i]))
        
    # Constraint 2: DAG property (Edge i->j implies rank[i] < rank[j])
    for i in range(N):
        for j in range(N):
            solver.add(z3.Implies(edges[i][j], ranks[i] < ranks[j]))
            
    # Constraint 3: Ensure non-trivial graph (at least N-1 edges)
    edge_count = z3.Sum([z3.If(edges[i][j], 1, 0) for i in range(N) for j in range(N)])
    solver.add(edge_count >= N - 1)
    
    # Find a model
    assert solver.check() == z3.sat
    model = solver.model()
    
    # Convert model to ArchitectureModules
    modules = []
    for i in range(N):
        deps = []
        for j in range(N):
            if z3.is_true(model.evaluate(edges[i][j])):
                deps.append(nodes[j])
        
        modules.append(create_module(nodes[i], deps))
        
    # Validate
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    # Should be valid regarding cycles
    # Note: Might have orphan warnings, but valid should be True if no errors
    # We specifically check for circular_dependency errors
    cycle_errors = [e for e in result.errors if e.type == "circular_dependency"]
    assert len(cycle_errors) == 0, f"Z3 generated a DAG but validator found cycles: {cycle_errors}"

@pytest.mark.skipif(not Z3_AVAILABLE, reason="z3-solver not installed")
@pytest.mark.asyncio
async def test_z3_generated_cycle_is_invalid():
    """
    Formal Verification:
    Use Z3 to generate a graph that MUST contain a cycle of length 3.
    Verify that the architecture validator correctly identifies it as invalid.
    """
    solver = z3.Solver()
    
    N = 3
    nodes = [f"CNode_{i}" for i in range(N)]
    edges = [[z3.Bool(f"ce_{i}_{j}") for j in range(N)] for i in range(N)]
    
    # Force a cycle: 0->1, 1->2, 2->0
    solver.add(edges[0][1])
    solver.add(edges[1][2])
    solver.add(edges[2][0])
    
    # Allow other edges arbitrarily or restrict them? Let's just force these.
    
    assert solver.check() == z3.sat
    model = solver.model()
    
    modules = []
    for i in range(N):
        deps = []
        for j in range(N):
            if z3.is_true(model.evaluate(edges[i][j])):
                deps.append(nodes[j])
        modules.append(create_module(nodes[i], deps))
        
    request = ValidateArchitectureRequest(modules=modules)
    result = await validate_architecture(request)
    
    assert result.valid is False
    cycle_errors = [e for e in result.errors if e.type == "circular_dependency"]
    assert len(cycle_errors) > 0
    
    # Verify the specific cycle is found
    found_cycle = False
    expected_elements = {"CNode_0", "CNode_1", "CNode_2"}
    for error in cycle_errors:
        if expected_elements.issubset(set(error.modules)):
            found_cycle = True
            break
    
    assert found_cycle, "Validator failed to find the Z3-generated cycle 0->1->2->0"