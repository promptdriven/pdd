# PDD Sync Command: Comprehensive Problem Analysis and Solution Design

## Executive Summary

The PDD sync command promises to be a "PRIMARY COMMAND" that automatically executes the complete PDD workflow loop. However, analysis reveals fundamental design flaws that prevent it from reliably fulfilling this promise. This document provides a comprehensive analysis of these problems and actionable solutions for engineering implementation.

## Critical Problems Identified

### 1. State Management Issues

**Problem**: The sync command attempts to infer system state from file existence and timestamps, leading to:
- Inability to recover from interrupted operations
- No knowledge of which operations have been attempted
- Confusion between user-edited files and generated files
- Race conditions in multi-process environments

**Impact**: Users experience unpredictable behavior, repeated operations, and potential data loss.

### 2. Circular Dependency Logic

**Problem**: The codebase contains contradictory dependencies:
- Comments state "generate must be done before test"
- Code allows test generation without prior code generation
- Example generation requires code, but code generation doesn't ensure examples exist

**Impact**: Operations fail with cryptic errors or produce invalid outputs.

### 3. Non-Deterministic Decision Making

**Problem**: Critical workflow decisions rely on LLM analysis without fallbacks:
```python
if significant_changes and has_dependencies:
    # Ask LLM what to do - no deterministic fallback
    recommendation = await self._analyze_change_propagation_with_llm()
```

**Impact**: Same inputs produce different outputs, making debugging impossible.

### 4. No Conflict Resolution

**Problem**: When code has manual changes and prompt has updates:
- No three-way merge capability
- Binary choice: keep manual changes OR regenerate
- No AST-aware merging for code files

**Impact**: Users lose work or miss important updates.

### 5. Missing Error Recovery

**Problem**: Operations can fail midway with no recovery mechanism:
- No transaction/rollback system
- No checkpoint saving
- Failed operations leave system in undefined state

**Impact**: Users must manually clean up partial changes.

### 6. Ignored Test Results

**Problem**: Test execution results aren't used for decision-making:
- Tests might pass/fail but sync continues blindly
- No intelligence about types of failures
- Coverage reports generated but not analyzed

**Impact**: Sync claims success even when tests reveal problems.

### 7. Inadequate Multi-Unit Handling

**Problem**: Projects with multiple interconnected units lack:
- Dependency graph tracking
- Change propagation intelligence
- Parallel execution safety

**Impact**: Changes break dependent units silently.

### 8. Resource Control Issues

**Problem**: No mechanisms to prevent:
- Runaway costs from infinite fix loops
- Multiple sync processes on same files
- Excessive LLM calls for simple decisions

**Impact**: Unexpected costs and resource conflicts.

## Comprehensive Solution Architecture

### Solution 1: Implement Proper State Machine

**Design**: Replace file-based state inference with explicit state tracking.

**Implementation**:

```python
# pdd/sync/state_manager.py
from enum import Enum
from typing import Dict, Optional, List
from datetime import datetime
import json
import sqlite3
from pathlib import Path

class SyncState(Enum):
    INITIAL = "initial"
    DEPS_INJECTED = "deps_injected"
    CODE_GENERATED = "code_generated"
    EXAMPLE_CREATED = "example_created"
    CRASH_FIXED = "crash_fixed"
    VERIFIED = "verified"
    TESTS_GENERATED = "tests_generated"
    TESTS_PASSING = "tests_passing"
    COMPLETED = "completed"
    FAILED = "failed"
    INTERRUPTED = "interrupted"

class StateManager:
    def __init__(self, db_path: Path = Path(".pdd/sync_state.db")):
        self.db_path = db_path
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self._init_db()
    
    def _init_db(self):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS sync_state (
                    unit_id TEXT PRIMARY KEY,
                    current_state TEXT NOT NULL,
                    last_operation TEXT,
                    last_operation_status TEXT,
                    last_operation_time TIMESTAMP,
                    operation_count INTEGER DEFAULT 0,
                    file_hashes TEXT,  -- JSON
                    metadata TEXT,     -- JSON
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS operation_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    unit_id TEXT NOT NULL,
                    operation TEXT NOT NULL,
                    status TEXT NOT NULL,
                    cost REAL DEFAULT 0,
                    duration_seconds REAL,
                    error_message TEXT,
                    metadata TEXT,  -- JSON
                    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    FOREIGN KEY (unit_id) REFERENCES sync_state(unit_id)
                )
            """)
    
    def get_state(self, unit_id: str) -> Optional[Dict]:
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute(
                "SELECT * FROM sync_state WHERE unit_id = ?", 
                (unit_id,)
            )
            row = cursor.fetchone()
            if row:
                return self._row_to_dict(cursor, row)
        return None
    
    def update_state(self, unit_id: str, state: SyncState, 
                    operation: str = None, status: str = None,
                    file_hashes: Dict[str, str] = None):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO sync_state 
                (unit_id, current_state, last_operation, last_operation_status,
                 last_operation_time, operation_count, file_hashes, updated_at)
                VALUES (?, ?, ?, ?, ?, 
                        COALESCE((SELECT operation_count + 1 FROM sync_state WHERE unit_id = ?), 0),
                        ?, CURRENT_TIMESTAMP)
            """, (unit_id, state.value, operation, status, datetime.now(),
                  unit_id, json.dumps(file_hashes) if file_hashes else None))
    
    def log_operation(self, unit_id: str, operation: str, 
                     status: str, cost: float = 0, 
                     duration: float = None, error: str = None):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT INTO operation_log 
                (unit_id, operation, status, cost, duration_seconds, error_message)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (unit_id, operation, status, cost, duration, error))
```

**Migration Strategy**:
```python
# pdd/sync/migration.py
def migrate_existing_project():
    """One-time migration to initialize state for existing projects"""
    state_manager = StateManager()
    
    for prompt_file in Path("prompts").glob("*_*.prompt"):
        basename, language = parse_prompt_filename(prompt_file)
        unit_id = f"{basename}_{language}"
        
        # Infer current state from files
        state = infer_current_state(basename, language)
        state_manager.update_state(unit_id, state)
```

### Solution 2: Fix Circular Dependencies

**Design**: Establish clear, enforced operation prerequisites.

**Implementation**:

```python
# pdd/sync/operation_graph.py
from typing import Dict, Set, List
from dataclasses import dataclass

@dataclass
class Operation:
    name: str
    prerequisites: Set[str]
    produces: Set[str]
    optional: bool = False

class OperationGraph:
    def __init__(self):
        self.operations = {
            "auto_deps": Operation(
                name="auto_deps",
                prerequisites=set(),
                produces={"dependencies_analyzed"}
            ),
            "generate": Operation(
                name="generate",
                prerequisites={"dependencies_analyzed"},
                produces={"code_file"}
            ),
            "example": Operation(
                name="example",
                prerequisites={"code_file"},
                produces={"example_file"}
            ),
            "crash": Operation(
                name="crash",
                prerequisites={"code_file", "example_file"},
                produces={"runnable_code"}
            ),
            "verify": Operation(
                name="verify",
                prerequisites={"runnable_code"},
                produces={"functionally_verified"},
                optional=True
            ),
            "test": Operation(
                name="test",
                prerequisites={"runnable_code"},
                produces={"test_file"}
            ),
            "fix": Operation(
                name="fix",
                prerequisites={"test_file", "runnable_code"},
                produces={"passing_tests"}
            ),
            "update": Operation(
                name="update",
                prerequisites={"code_file"},
                produces={"updated_prompt"}
            )
        }
    
    def get_execution_order(self, target_operations: List[str]) -> List[str]:
        """Topological sort to determine execution order"""
        visited = set()
        order = []
        
        def visit(op_name: str):
            if op_name in visited:
                return
            
            operation = self.operations[op_name]
            
            # Visit prerequisites first
            for prereq_product in operation.prerequisites:
                # Find operation that produces this
                for name, op in self.operations.items():
                    if prereq_product in op.produces:
                        visit(name)
            
            visited.add(op_name)
            order.append(op_name)
        
        for target in target_operations:
            visit(target)
        
        return order
    
    def validate_prerequisites(self, operation: str, 
                             available_products: Set[str]) -> bool:
        """Check if all prerequisites are met"""
        op = self.operations[operation]
        return op.prerequisites.issubset(available_products)
```

### Solution 3: Deterministic Decision Engine

**Design**: Use rules-based decisions with LLM as fallback for complex cases.

**Implementation**:

```python
# pdd/sync/decision_engine.py
from enum import Enum
from typing import Optional, Dict, List
import hashlib

class ChangeType(Enum):
    NO_CHANGE = "no_change"
    PROMPT_ONLY = "prompt_only"
    CODE_ONLY = "code_only"
    BOTH_COMPATIBLE = "both_compatible"
    BOTH_CONFLICTING = "both_conflicting"
    NEW_FILE = "new_file"

class DecisionEngine:
    def __init__(self, state_manager: StateManager):
        self.state_manager = state_manager
    
    def analyze_changes(self, unit_id: str, 
                       prompt_path: Path, 
                       code_path: Path) -> ChangeType:
        """Deterministic change analysis"""
        state = self.state_manager.get_state(unit_id)
        
        if not code_path.exists():
            return ChangeType.NEW_FILE
        
        current_hashes = {
            "prompt": self._hash_file(prompt_path),
            "code": self._hash_file(code_path)
        }
        
        if not state or not state.get("file_hashes"):
            return ChangeType.NEW_FILE
        
        stored_hashes = json.loads(state["file_hashes"])
        
        prompt_changed = current_hashes["prompt"] != stored_hashes.get("prompt")
        code_changed = current_hashes["code"] != stored_hashes.get("code")
        
        if not prompt_changed and not code_changed:
            return ChangeType.NO_CHANGE
        elif prompt_changed and not code_changed:
            return ChangeType.PROMPT_ONLY
        elif code_changed and not prompt_changed:
            return ChangeType.CODE_ONLY
        else:
            # Both changed - check if they're compatible
            if self._are_changes_compatible(prompt_path, code_path, state):
                return ChangeType.BOTH_COMPATIBLE
            else:
                return ChangeType.BOTH_CONFLICTING
    
    def decide_next_operation(self, unit_id: str, 
                            change_type: ChangeType,
                            target_state: SyncState) -> str:
        """Deterministic operation selection"""
        decision_map = {
            ChangeType.NEW_FILE: "generate",
            ChangeType.PROMPT_ONLY: "generate",
            ChangeType.CODE_ONLY: "update",
            ChangeType.BOTH_COMPATIBLE: "merge",
            ChangeType.BOTH_CONFLICTING: "request_user_input",
            ChangeType.NO_CHANGE: self._next_operation_for_state(unit_id)
        }
        
        return decision_map[change_type]
    
    def _are_changes_compatible(self, prompt_path: Path, 
                               code_path: Path, 
                               state: Dict) -> bool:
        """Rule-based compatibility check"""
        # Simple rules first
        prompt_diff = self._get_diff_summary(prompt_path, state["last_prompt"])
        code_diff = self._get_diff_summary(code_path, state["last_code"])
        
        # If changes are in different sections, likely compatible
        if not self._sections_overlap(prompt_diff, code_diff):
            return True
        
        # If both are small changes, likely compatible
        if prompt_diff["lines_changed"] < 10 and code_diff["lines_changed"] < 10:
            return True
        
        # For complex cases, fall back to LLM
        return self._llm_compatibility_check(prompt_diff, code_diff)
```

### Solution 4: Implement Conflict Resolution

**Design**: Three-way merge with AST awareness for code files.

**Implementation**:

```python
# pdd/sync/merge_strategies.py
import ast
import difflib
from typing import Tuple, List, Optional

class MergeStrategy:
    def merge_files(self, 
                   base: str,      # Original version
                   ours: str,      # Manual changes
                   theirs: str,    # Generated changes
                   file_type: str) -> Tuple[str, List[str]]:
        """
        Returns: (merged_content, list_of_conflicts)
        """
        if file_type == "python":
            return self._merge_python(base, ours, theirs)
        else:
            return self._merge_text(base, ours, theirs)
    
    def _merge_python(self, base: str, ours: str, theirs: str) -> Tuple[str, List[str]]:
        """AST-aware Python merging"""
        try:
            base_ast = ast.parse(base)
            ours_ast = ast.parse(ours)
            theirs_ast = ast.parse(theirs)
            
            # Extract function/class definitions
            base_defs = self._extract_definitions(base_ast)
            ours_defs = self._extract_definitions(ours_ast)
            theirs_defs = self._extract_definitions(theirs_ast)
            
            # Merge at definition level
            merged_defs = {}
            conflicts = []
            
            all_names = set(base_defs.keys()) | set(ours_defs.keys()) | set(theirs_defs.keys())
            
            for name in all_names:
                base_def = base_defs.get(name)
                ours_def = ours_defs.get(name)
                theirs_def = theirs_defs.get(name)
                
                if ours_def and theirs_def and ours_def != theirs_def:
                    # Conflict - both modified
                    if self._can_auto_merge(base_def, ours_def, theirs_def):
                        merged_defs[name] = self._auto_merge(base_def, ours_def, theirs_def)
                    else:
                        conflicts.append(f"Conflict in {name}")
                        merged_defs[name] = ours_def  # Keep manual changes by default
                elif ours_def:
                    merged_defs[name] = ours_def
                elif theirs_def:
                    merged_defs[name] = theirs_def
            
            # Reconstruct file
            merged_content = self._reconstruct_python(merged_defs, base)
            return merged_content, conflicts
            
        except SyntaxError:
            # Fall back to text merge
            return self._merge_text(base, ours, theirs)
    
    def _merge_text(self, base: str, ours: str, theirs: str) -> Tuple[str, List[str]]:
        """Three-way text merge"""
        base_lines = base.splitlines(keepends=True)
        ours_lines = ours.splitlines(keepends=True)
        theirs_lines = theirs.splitlines(keepends=True)
        
        # Use difflib's three-way merge
        merger = difflib.Differ()
        
        # Get diffs
        base_to_ours = list(merger.compare(base_lines, ours_lines))
        base_to_theirs = list(merger.compare(base_lines, theirs_lines))
        
        merged_lines = []
        conflicts = []
        i = j = k = 0
        
        while i < len(base_lines) or j < len(ours_lines) or k < len(theirs_lines):
            # Complex merge logic here
            # Simplified for brevity
            pass
        
        return ''.join(merged_lines), conflicts
```

### Solution 5: Transaction System

**Design**: Atomic operations with rollback capability.

**Implementation**:

```python
# pdd/sync/transactions.py
import shutil
from contextlib import contextmanager
from pathlib import Path
import tempfile
from typing import List, Dict

class SyncTransaction:
    def __init__(self, unit_id: str):
        self.unit_id = unit_id
        self.backup_dir = None
        self.files_backed_up: Dict[Path, Path] = {}
        self.state_snapshot = None
        
    @contextmanager
    def atomic_operation(self, operation_name: str, 
                        files_to_protect: List[Path]):
        """Context manager for atomic operations"""
        try:
            # Create backup
            self._create_backup(files_to_protect)
            
            # Snapshot state
            state_manager = StateManager()
            self.state_snapshot = state_manager.get_state(self.unit_id)
            
            yield self
            
            # Success - clean up backup
            self._cleanup_backup()
            
        except Exception as e:
            # Failure - restore from backup
            self._restore_backup()
            
            # Restore state
            if self.state_snapshot:
                state_manager.update_state(
                    self.unit_id,
                    SyncState(self.state_snapshot["current_state"]),
                    error=str(e)
                )
            raise
    
    def _create_backup(self, files: List[Path]):
        """Create backup of all files"""
        self.backup_dir = Path(tempfile.mkdtemp(prefix=f"pdd_backup_{self.unit_id}_"))
        
        for file_path in files:
            if file_path.exists():
                backup_path = self.backup_dir / file_path.name
                shutil.copy2(file_path, backup_path)
                self.files_backed_up[file_path] = backup_path
    
    def _restore_backup(self):
        """Restore all files from backup"""
        for original, backup in self.files_backed_up.items():
            if backup.exists():
                shutil.copy2(backup, original)
    
    def _cleanup_backup(self):
        """Remove backup directory"""
        if self.backup_dir and self.backup_dir.exists():
            shutil.rmtree(self.backup_dir)

# Usage example:
async def sync_with_transactions(unit_id: str):
    transaction = SyncTransaction(unit_id)
    
    files_to_protect = [
        Path(f"src/{unit_id}.py"),
        Path(f"tests/test_{unit_id}.py"),
        Path(f"prompts/{unit_id}.prompt")
    ]
    
    with transaction.atomic_operation("generate", files_to_protect):
        # All operations here are atomic
        await generate_code(unit_id)
        await generate_tests(unit_id)
        
        # If any operation fails, all changes are rolled back
```

### Solution 6: Test Result Integration

**Design**: Parse and use actual test execution results.

**Implementation**:

```python
# pdd/sync/test_analyzer.py
import subprocess
import json
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from typing import List, Dict, Optional

@dataclass
class TestResult:
    passed: int
    failed: int
    skipped: int
    errors: List[Dict[str, str]]
    coverage: Optional[float]
    failure_patterns: List[str]

class TestAnalyzer:
    def run_and_analyze_tests(self, test_file: Path, 
                            code_file: Path) -> TestResult:
        """Run tests and analyze results"""
        # Run pytest with XML output
        result = subprocess.run([
            "pytest", str(test_file),
            f"--cov={code_file.stem}",
            "--cov-report=xml",
            "--junit-xml=test_results.xml",
            "-v"
        ], capture_output=True, text=True)
        
        # Parse results
        test_result = self._parse_junit_xml("test_results.xml")
        test_result.coverage = self._parse_coverage_xml("coverage.xml")
        test_result.failure_patterns = self._analyze_failure_patterns(result.stderr)
        
        return test_result
    
    def _parse_junit_xml(self, xml_path: str) -> TestResult:
        """Parse JUnit XML test results"""
        tree = ET.parse(xml_path)
        root = tree.getroot()
        
        passed = int(root.attrib.get("tests", 0)) - int(root.attrib.get("failures", 0)) - int(root.attrib.get("errors", 0))
        failed = int(root.attrib.get("failures", 0))
        errors = []
        
        for testcase in root.findall(".//testcase"):
            failure = testcase.find("failure")
            if failure is not None:
                errors.append({
                    "test": testcase.attrib["name"],
                    "error": failure.attrib.get("message", ""),
                    "type": failure.attrib.get("type", "AssertionError")
                })
        
        return TestResult(
            passed=passed,
            failed=failed,
            skipped=int(root.attrib.get("skipped", 0)),
            errors=errors,
            coverage=None,
            failure_patterns=[]
        )
    
    def _analyze_failure_patterns(self, stderr: str) -> List[str]:
        """Identify common failure patterns"""
        patterns = []
        
        if "ImportError" in stderr:
            patterns.append("import_error")
        if "AttributeError" in stderr:
            patterns.append("missing_attribute")
        if "TypeError" in stderr:
            patterns.append("type_error")
        if "AssertionError" in stderr:
            patterns.append("assertion_failure")
            
        return patterns
    
    def recommend_fix_strategy(self, test_result: TestResult) -> str:
        """Recommend fix strategy based on test results"""
        if "import_error" in test_result.failure_patterns:
            return "fix_imports"
        elif "missing_attribute" in test_result.failure_patterns:
            return "fix_interface"
        elif test_result.failed > test_result.passed:
            return "major_refactor"
        else:
            return "targeted_fixes"
```

### Solution 7: Multi-Unit Dependency Management

**Design**: Track and manage dependencies between units.

**Implementation**:

```python
# pdd/sync/dependency_manager.py
import networkx as nx
from typing import Set, List, Dict
import re

class DependencyManager:
    def __init__(self):
        self.graph = nx.DiGraph()
        self._load_dependencies()
    
    def _load_dependencies(self):
        """Load dependency graph from .pdd/dependencies.json"""
        dep_file = Path(".pdd/dependencies.json")
        if dep_file.exists():
            with open(dep_file) as f:
                deps = json.load(f)
                for unit, info in deps.items():
                    self.graph.add_node(unit)
                    for dep in info.get("depends_on", []):
                        self.graph.add_edge(unit, dep)
    
    def analyze_dependencies(self, unit_id: str, 
                           code_path: Path) -> Set[str]:
        """Analyze code to find dependencies"""
        dependencies = set()
        
        if code_path.suffix == ".py":
            dependencies.update(self._analyze_python_imports(code_path))
        
        # Check example includes in prompt
        prompt_path = Path(f"prompts/{unit_id}.prompt")
        if prompt_path.exists():
            dependencies.update(self._analyze_prompt_includes(prompt_path))
        
        return dependencies
    
    def _analyze_python_imports(self, code_path: Path) -> Set[str]:
        """Extract local module imports"""
        dependencies = set()
        
        with open(code_path) as f:
            tree = ast.parse(f.read())
        
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if self._is_local_module(alias.name):
                        dependencies.add(alias.name)
            elif isinstance(node, ast.ImportFrom):
                if self._is_local_module(node.module):
                    dependencies.add(node.module)
        
        return dependencies
    
    def get_affected_units(self, changed_unit: str) -> List[str]:
        """Get units that depend on the changed unit"""
        return list(nx.ancestors(self.graph, changed_unit))
    
    def get_sync_order(self, units: List[str]) -> List[str]:
        """Get order to sync units respecting dependencies"""
        subgraph = self.graph.subgraph(units)
        try:
            return list(nx.topological_sort(subgraph))
        except nx.NetworkXError:
            # Circular dependency
            raise CyclicDependencyError(f"Circular dependency detected in {units}")
    
    def update_dependencies(self, unit_id: str, dependencies: Set[str]):
        """Update dependency graph"""
        # Remove old edges
        self.graph.remove_edges_from([(unit_id, dep) for dep in self.graph.successors(unit_id)])
        
        # Add new edges
        for dep in dependencies:
            self.graph.add_edge(unit_id, dep)
        
        # Save to file
        self._save_dependencies()
```

### Solution 8: Resource Control

**Design**: Implement comprehensive resource management.

**Implementation**:

```python
# pdd/sync/resource_manager.py
import fcntl
import psutil
from dataclasses import dataclass
from typing import Optional
import time

@dataclass
class ResourceLimits:
    max_cost: float = 10.0
    max_operations: int = 50
    max_time_seconds: int = 3600
    max_concurrent_syncs: int = 1
    max_llm_calls_per_minute: int = 10

class ResourceManager:
    def __init__(self, limits: ResourceLimits = None):
        self.limits = limits or ResourceLimits()
        self.operation_count = 0
        self.total_cost = 0.0
        self.start_time = time.time()
        self.llm_call_times = []
    
    def acquire_sync_lock(self, unit_id: str) -> Optional[int]:
        """Acquire exclusive lock for unit"""
        lock_path = Path(f".pdd/locks/{unit_id}.lock")
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        
        try:
            lock_file = open(lock_path, 'w')
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            lock_file.write(str(os.getpid()))
            lock_file.flush()
            return lock_file.fileno()
        except IOError:
            # Check if the process holding the lock is still alive
            if lock_path.exists():
                with open(lock_path) as f:
                    pid = int(f.read())
                    if not psutil.pid_exists(pid):
                        # Stale lock - remove it
                        lock_path.unlink()
                        return self.acquire_sync_lock(unit_id)
            return None
    
    def check_resource_limits(self) -> Tuple[bool, str]:
        """Check if any resource limits exceeded"""
        if self.total_cost >= self.limits.max_cost:
            return False, f"Cost limit exceeded: ${self.total_cost:.2f} >= ${self.limits.max_cost:.2f}"
        
        if self.operation_count >= self.limits.max_operations:
            return False, f"Operation limit exceeded: {self.operation_count} >= {self.limits.max_operations}"
        
        elapsed = time.time() - self.start_time
        if elapsed >= self.limits.max_time_seconds:
            return False, f"Time limit exceeded: {elapsed:.0f}s >= {self.limits.max_time_seconds}s"
        
        return True, "OK"
    
    def check_rate_limit(self) -> bool:
        """Check if we can make another LLM call"""
        now = time.time()
        
        # Remove calls older than 1 minute
        self.llm_call_times = [t for t in self.llm_call_times if now - t < 60]
        
        if len(self.llm_call_times) >= self.limits.max_llm_calls_per_minute:
            # Wait until we can make another call
            wait_time = 60 - (now - self.llm_call_times[0])
            time.sleep(wait_time)
            return self.check_rate_limit()
        
        self.llm_call_times.append(now)
        return True
    
    def track_operation(self, operation: str, cost: float):
        """Track resource usage"""
        self.operation_count += 1
        self.total_cost += cost
        
        # Log to database
        with sqlite3.connect(".pdd/sync_state.db") as conn:
            conn.execute("""
                INSERT INTO resource_usage 
                (timestamp, operation, cost, cumulative_cost, operation_count)
                VALUES (?, ?, ?, ?, ?)
            """, (datetime.now(), operation, cost, self.total_cost, self.operation_count))
```

### Solution 9: Progressive Sync Implementation

**Design**: Allow partial syncs with checkpointing.

**Implementation**:

```python
# pdd/sync/progressive_sync.py
from typing import List, Optional, Dict
from dataclasses import dataclass

@dataclass
class SyncProfile:
    name: str
    steps: List[str]
    skip_on_failure: List[str]
    require_confirmation: List[str]
    max_attempts_per_step: Dict[str, int]

class ProgressiveSync:
    def __init__(self):
        self.profiles = {
            "quick": SyncProfile(
                name="quick",
                steps=["generate", "example"],
                skip_on_failure=[],
                require_confirmation=[],
                max_attempts_per_step={"generate": 1, "example": 1}
            ),
            "standard": SyncProfile(
                name="standard",
                steps=["auto_deps", "generate", "example", "crash", "test"],
                skip_on_failure=["verify"],
                require_confirmation=[],
                max_attempts_per_step={"crash": 3, "test": 1}
            ),
            "thorough": SyncProfile(
                name="thorough",
                steps=["auto_deps", "generate", "example", "crash", "verify", "test", "fix"],
                skip_on_failure=[],
                require_confirmation=["generate"],
                max_attempts_per_step={"crash": 5, "fix": 5}
            ),
            "safe": SyncProfile(
                name="safe",
                steps=["auto_deps", "generate", "example"],
                skip_on_failure=["example"],
                require_confirmation=["generate", "auto_deps"],
                max_attempts_per_step={"generate": 1}
            )
        }
    
    async def sync_with_profile(self, unit_id: str, 
                               profile_name: str = "standard",
                               resume_from: Optional[str] = None):
        """Execute sync with specified profile"""
        profile = self.profiles[profile_name]
        state_manager = StateManager()
        
        # Determine starting point
        if resume_from:
            start_index = profile.steps.index(resume_from)
        else:
            state = state_manager.get_state(unit_id)
            start_index = self._determine_resume_point(state, profile)
        
        # Execute steps
        for step in profile.steps[start_index:]:
            if step in profile.require_confirmation:
                if not await self._get_user_confirmation(step, unit_id):
                    continue
            
            success = await self._execute_step(
                unit_id, step, 
                max_attempts=profile.max_attempts_per_step.get(step, 1)
            )
            
            if not success and step not in profile.skip_on_failure:
                raise SyncError(f"Failed at step {step} for {unit_id}")
            
            # Save checkpoint
            state_manager.save_checkpoint(unit_id, step)
    
    def _determine_resume_point(self, state: Optional[Dict], 
                               profile: SyncProfile) -> int:
        """Determine where to resume based on state"""
        if not state:
            return 0
        
        last_successful = state.get("last_successful_step")
        if last_successful in profile.steps:
            return profile.steps.index(last_successful) + 1
        
        return 0
```

### Solution 10: Intelligent Change Detection

**Design**: Use git integration and AST analysis for better change detection.

**Implementation**:

```python
# pdd/sync/change_detector.py
import git
import ast
from typing import Dict, List, Tuple

class ChangeDetector:
    def __init__(self, repo_path: Path = Path(".")):
        try:
            self.repo = git.Repo(repo_path)
        except git.InvalidGitRepositoryError:
            self.repo = None
    
    def detect_changes(self, unit_id: str) -> Dict[str, Any]:
        """Comprehensive change detection"""
        prompt_path = Path(f"prompts/{unit_id}.prompt")
        code_path = self._find_code_file(unit_id)
        
        changes = {
            "prompt": self._analyze_prompt_changes(prompt_path),
            "code": self._analyze_code_changes(code_path),
            "dependencies": self._analyze_dependency_changes(unit_id),
            "tests": self._analyze_test_changes(unit_id)
        }
        
        changes["impact"] = self._assess_change_impact(changes)
        changes["recommendation"] = self._recommend_sync_strategy(changes)
        
        return changes
    
    def _analyze_code_changes(self, code_path: Path) -> Dict:
        """Detailed code change analysis"""
        if not code_path.exists():
            return {"status": "not_found"}
        
        if not self.repo:
            return {"status": "no_git"}
        
        # Get diff from last commit
        diffs = self.repo.index.diff("HEAD", paths=[str(code_path)])
        
        if not diffs:
            return {"status": "unchanged"}
        
        # Analyze changes
        analysis = {
            "status": "changed",
            "additions": 0,
            "deletions": 0,
            "modified_functions": [],
            "modified_classes": [],
            "structural_changes": False
        }
        
        for diff in diffs:
            # Parse before/after AST
            before_ast = ast.parse(diff.a_blob.data_stream.read().decode())
            after_ast = ast.parse(diff.b_blob.data_stream.read().decode())
            
            # Compare AST structure
            before_defs = self._extract_definitions(before_ast)
            after_defs = self._extract_definitions(after_ast)
            
            # Find modified definitions
            for name in before_defs:
                if name in after_defs and before_defs[name] != after_defs[name]:
                    if isinstance(before_defs[name], ast.FunctionDef):
                        analysis["modified_functions"].append(name)
                    elif isinstance(before_defs[name], ast.ClassDef):
                        analysis["modified_classes"].append(name)
            
            # Check for structural changes
            if set(before_defs.keys()) != set(after_defs.keys()):
                analysis["structural_changes"] = True
        
        return analysis
    
    def _assess_change_impact(self, changes: Dict) -> str:
        """Assess overall impact of changes"""
        impact_score = 0
        
        # Structural changes have high impact
        if changes["code"].get("structural_changes"):
            impact_score += 50
        
        # Many modified functions
        if len(changes["code"].get("modified_functions", [])) > 3:
            impact_score += 30
        
        # Dependency changes
        if changes["dependencies"].get("added") or changes["dependencies"].get("removed"):
            impact_score += 40
        
        # Test changes
        if changes["tests"].get("status") == "changed":
            impact_score += 20
        
        if impact_score >= 70:
            return "high"
        elif impact_score >= 30:
            return "medium"
        else:
            return "low"
```

## Implementation Plan

### Phase 1: Foundation (Week 1-2)
1. Implement StateManager with database schema
2. Create OperationGraph for dependency management
3. Build ResourceManager with locking
4. Add migration script for existing projects

### Phase 2: Core Logic (Week 3-4)
1. Implement DecisionEngine with deterministic rules
2. Create ChangeDetector with git integration
3. Build TestAnalyzer for result parsing
4. Add SyncTransaction for atomicity

### Phase 3: Advanced Features (Week 5-6)
1. Implement MergeStrategy with AST awareness
2. Create DependencyManager for multi-unit projects
3. Build ProgressiveSync with profiles
4. Add comprehensive error handling

### Phase 4: Testing & Polish (Week 7-8)
1. Unit tests for all components
2. Integration tests for common workflows
3. Performance optimization
4. Documentation updates

## Backward Compatibility

### Migration Strategy
1. Detect legacy sync operations by absence of state database
2. Infer current state from existing files
3. Initialize state database with inferred state
4. Preserve existing file naming conventions

### Gradual Rollout
1. Add `--use-new-sync` flag initially
2. Run both old and new sync in parallel for comparison
3. Gradually migrate users with clear communication
4. Remove old implementation after stability proven

## Success Metrics

1. **Reliability**: 95% of sync operations complete without manual intervention
2. **Predictability**: Same inputs produce same outputs 100% of time
3. **Performance**: Average sync time reduced by 30%
4. **Cost**: LLM costs reduced by 50% through caching and deterministic decisions
5. **User Satisfaction**: Error reports reduced by 80%

## Conclusion

The current sync implementation fails to deliver on its promises due to fundamental architectural flaws. This comprehensive solution addresses each problem with specific, implementable solutions that will transform sync from an unreliable automation attempt into a robust, predictable workflow engine that users can trust.

The key insight is that sync should be deterministic and state-driven, using AI only where it adds clear value, rather than relying on it for basic workflow decisions. With proper state management, dependency tracking, and resource control, sync can finally become the "PRIMARY COMMAND" it promises to be.
