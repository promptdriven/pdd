# Sync --skip-tests Edge Case Fix Plan

## Problem Summary

The `sync --skip-tests` command hangs when files are deleted but metadata remains from previous sync runs. This creates an inconsistent state where the sync determine operation logic incorrectly returns `analyze_conflict` instead of detecting missing files and regenerating them.

### Specific Failure Scenarios

1. **Regression Test Scenario**:
   - Run full sync → generates all files + metadata
   - Clean files but keep metadata (simulating test cleanup)
   - Run `sync --skip-tests` → hangs in `analyze_conflict` LLM processing

2. **Root Cause Validated**: 
   - `sync_determine_operation` returns `operation='analyze_conflict'` when files are missing
   - `analyze_conflict` leads to LLM processing that hangs/times out
   - Missing file validation prevents proper recovery

## Root Cause Analysis - VALIDATED ✅

**Definitive Root Cause**: `sync_determine_operation.py` incorrectly returns `'analyze_conflict'` when files are deleted but metadata exists, instead of detecting missing files and returning appropriate regeneration operations.

### Validated Issues

1. **Incorrect Conflict Detection**: When files are missing, hash comparison (`None != "hash_value"`) marks all files as "changed", triggering `analyze_conflict` instead of missing file recovery
2. **Missing File Validation**: No `validate_expected_files()` function to detect missing files before hash comparison
3. **Skip-Tests Workflow Gaps**: `--skip-tests` flag not passed to `sync_determine_operation` 
4. **No Recovery Logic**: Missing `_handle_missing_expected_files()` function for systematic file recovery

### Test Validation Results

**ALL 5 CRITICAL ISSUES CONFIRMED**:
- ✅ `sync_determine_operation` returns `'analyze_conflict'` for missing files (should return `'generate'`)
- ✅ `validate_expected_files()` function missing (checklist lines 41-61)
- ✅ `_handle_missing_expected_files()` function missing (checklist lines 98-161)  
- ✅ Skip flags (`skip_tests`, `skip_verify`) not supported in `sync_determine_operation`
- ✅ Skip flags not passed in `sync_orchestration.py:274` call

### Code Locations Affected

- `pdd/sync_determine_operation.py:701-708` - Incorrect `analyze_conflict` decision logic
- `pdd/sync_orchestration.py:274` - Skip flags not passed to sync_determine_operation
- Missing validation and recovery functions throughout sync_determine_operation.py

## Implementation Plan

### Phase 1: Enhance Sync Determine Operation Logic

#### 1.1 Add File Existence Validation
**File**: `pdd/sync_determine_operation.py`

```python
def validate_expected_files(fingerprint: Optional[Fingerprint], paths: Dict[str, Path]) -> Dict[str, bool]:
    """
    Validate that files expected to exist based on fingerprint actually exist.
    
    Returns:
        Dict mapping file types to existence status
    """
    validation = {}
    
    if not fingerprint:
        return validation
    
    # Check each file type that has a hash in the fingerprint
    if fingerprint.code_hash:
        validation['code'] = paths['code'].exists()
    if fingerprint.example_hash:
        validation['example'] = paths['example'].exists()
    if fingerprint.test_hash:
        validation['test'] = paths['test'].exists()
        
    return validation
```

#### 1.2 Modify Hash Comparison Logic (CRITICAL FIX)
**File**: `pdd/sync_determine_operation.py`

```python
def _perform_sync_analysis(basename: str, language: str, target_coverage: float, budget: float, prompts_dir: str = "prompts", skip_tests: bool = False, skip_verify: bool = False) -> SyncDecision:
    """Enhanced sync analysis with file existence validation."""
    
    # ... existing code ...
    
    # 2. Analyze File State with validation
    paths = get_pdd_file_paths(basename, language, prompts_dir)
    current_hashes = calculate_current_hashes(paths)
    
    # NEW: Validate expected files actually exist BEFORE hash comparison
    if fingerprint:
        file_validation = validate_expected_files(fingerprint, paths)
        missing_expected_files = [
            file_type for file_type, exists in file_validation.items() 
            if not exists
        ]
        
        if missing_expected_files:
            # CRITICAL: Files are missing that should exist - need to regenerate
            # This prevents the incorrect analyze_conflict decision
            return _handle_missing_expected_files(
                missing_expected_files, paths, fingerprint, basename, language, prompts_dir, skip_tests, skip_verify
            )
    
    # 3. Compare hashes only for files that actually exist
    changes = []
    if fingerprint:
        if current_hashes.get('prompt_hash') != fingerprint.prompt_hash:
            changes.append('prompt')
        # Only compare hashes for files that exist (prevents None != "hash" false positives)
        if paths['code'].exists() and current_hashes.get('code_hash') != fingerprint.code_hash:
            changes.append('code')
        if paths['example'].exists() and current_hashes.get('example_hash') != fingerprint.example_hash:
            changes.append('example')
        if paths['test'].exists() and current_hashes.get('test_hash') != fingerprint.test_hash:
            changes.append('test')
    
    # ... rest of existing logic with skip flag awareness ...
```

#### 1.3 Add Missing File Recovery Logic
**File**: `pdd/sync_determine_operation.py`

```python
def _handle_missing_expected_files(
    missing_files: List[str], 
    paths: Dict[str, Path], 
    fingerprint: Fingerprint,
    basename: str, 
    language: str, 
    prompts_dir: str,
    skip_tests: bool = False,
    skip_verify: bool = False
) -> SyncDecision:
    """
    Handle the case where expected files are missing.
    Determine the appropriate recovery operation.
    """
    
    # Priority: regenerate from the earliest missing component
    if 'code' in missing_files:
        # Code file missing - start from the beginning
        if paths['prompt'].exists():
            prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
            if check_for_dependencies(prompt_content):
                return SyncDecision(
                    operation='auto-deps',
                    reason='Code file missing, prompt has dependencies - regenerate from auto-deps',
                    details={'missing_files': missing_files, 'prompt_path': str(paths['prompt'])},
                    estimated_cost=0.5,
                    confidence=0.85
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='Code file missing - regenerate from prompt',
                    details={'missing_files': missing_files, 'prompt_path': str(paths['prompt'])},
                    estimated_cost=1.0,
                    confidence=0.90
                )
    
    elif 'example' in missing_files and paths['code'].exists():
        # Code exists but example missing
        return SyncDecision(
            operation='example',
            reason='Example file missing - regenerate example',
            details={'missing_files': missing_files, 'code_path': str(paths['code'])},
            estimated_cost=0.5,
            confidence=0.85
        )
    
    elif 'test' in missing_files and paths['code'].exists() and paths['example'].exists():
        # Code and example exist but test missing
        if skip_tests:
            # Skip test generation if --skip-tests flag is used
            return SyncDecision(
                operation='nothing',
                reason='Test file missing but --skip-tests specified - workflow complete',
                details={'missing_files': missing_files, 'skip_tests': True},
                estimated_cost=0.0,
                confidence=1.0
            )
        else:
            return SyncDecision(
                operation='test',
                reason='Test file missing - regenerate tests',
                details={'missing_files': missing_files, 'code_path': str(paths['code'])},
                estimated_cost=1.0,
                confidence=0.85
            )
    
    # Fallback - regenerate everything
    return SyncDecision(
        operation='generate',
        reason='Multiple files missing - regenerate from prompt',
        details={'missing_files': missing_files},
        estimated_cost=2.0,
        confidence=0.80
    )
```

### Phase 2: Integrate Skip-Tests Awareness

#### 2.1 Pass Skip Flags to Sync Determine Operation
**File**: `pdd/sync_orchestration.py`

```python
# Modify the sync_determine_operation call to include skip flags
decision = sync_determine_operation(
    basename, 
    language, 
    target_coverage, 
    budget - current_cost_ref[0], 
    False, 
    prompts_dir,
    skip_tests=skip_tests,  # NEW
    skip_verify=skip_verify  # NEW
)
```

#### 2.2 Update Sync Determine Operation Signature
**File**: `pdd/sync_determine_operation.py`

```python
def sync_determine_operation(
    basename: str, 
    language: str, 
    target_coverage: float, 
    budget: float = 10.0, 
    log_mode: bool = False, 
    prompts_dir: str = "prompts",
    skip_tests: bool = False,  # NEW
    skip_verify: bool = False  # NEW
) -> SyncDecision:
    """
    Core decision-making function for sync operations with skip flag awareness.
    """
```

#### 2.3 Modify Decision Logic for Skip Flags
**File**: `pdd/sync_determine_operation.py`

```python
def _perform_sync_analysis(
    basename: str, 
    language: str, 
    target_coverage: float, 
    budget: float, 
    prompts_dir: str,
    skip_tests: bool = False,
    skip_verify: bool = False
) -> SyncDecision:
    """Enhanced sync analysis with skip flag awareness."""
    
    # ... existing validation logic ...
    
    # Modify completion checks based on skip flags
    def is_workflow_complete(paths: Dict[str, Path]) -> bool:
        """Check if workflow is complete considering skip flags."""
        required_files = ['code', 'example']
        
        if not skip_tests:
            required_files.append('test')
            
        return all(paths[f].exists() for f in required_files)
    
    # Use in decision logic
    if not changes:
        # No Changes (Hashes Match Fingerprint) - Check completion with skip awareness
        if is_workflow_complete(paths):
            return SyncDecision(
                operation='nothing',
                reason=f'All required files synchronized (skip_tests={skip_tests})',
                details={'skip_tests': skip_tests, 'skip_verify': skip_verify},
                estimated_cost=0.0,
                confidence=1.0
            )
        
        # Progress workflow considering skip flags
        if paths['code'].exists() and not paths['example'].exists():
            return SyncDecision(
                operation='example',
                reason='Code exists but example missing - progress workflow',
                details={'code_path': str(paths['code'])},
                estimated_cost=0.5,
                confidence=0.85
            )
        
        if (paths['code'].exists() and paths['example'].exists() and 
            not skip_tests and not paths['test'].exists()):
            return SyncDecision(
                operation='test',
                reason='Code and example exist but test missing - progress workflow',
                details={'code_path': str(paths['code']), 'example_path': str(paths['example'])},
                estimated_cost=1.0,
                confidence=0.85
            )
    
    # ... rest of logic ...
```

### Phase 3: Add Defensive File Operations

#### 3.1 Safe File Reading Wrapper
**File**: `pdd/sync_utils.py` (new file)

```python
from pathlib import Path
from typing import Optional, Tuple

def safe_read_file(file_path: Path, context: str = "") -> Tuple[bool, Optional[str]]:
    """
    Safely read a file with proper error handling.
    
    Returns:
        Tuple of (success: bool, content: Optional[str])
    """
    try:
        if not file_path.exists():
            return False, None
        
        content = file_path.read_text(encoding='utf-8', errors='ignore')
        return True, content
        
    except Exception as e:
        console.print(f"[red]Error reading {context} file {file_path}: {e}[/red]")
        return False, None

def ensure_file_exists_for_operation(file_path: Path, operation: str) -> bool:
    """
    Ensure a file exists before attempting an operation on it.
    
    Returns:
        True if file exists, False otherwise
    """
    if not file_path.exists():
        console.print(f"[red]Cannot perform {operation}: file {file_path} does not exist[/red]")
        return False
    return True
```

#### 3.2 Update Command Functions
**Files**: `pdd/context_generator_main.py`, `pdd/cmd_test_main.py`, etc.

```python
# Add defensive file existence checks before file operations
from .sync_utils import safe_read_file, ensure_file_exists_for_operation

def context_generator_main(ctx: click.Context, prompt_file: str, code_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """Enhanced context generator with defensive file operations."""
    
    # ... existing code ...
    
    # Replace direct file reads with safe reads
    success, prompt_content = safe_read_file(Path(prompt_file), "prompt")
    if not success:
        raise FileNotFoundError(f"Prompt file not found or unreadable: {prompt_file}")
    
    success, code_content = safe_read_file(Path(code_file), "code")
    if not success:
        raise FileNotFoundError(f"Code file not found or unreadable: {code_file}")
    
    # ... rest of logic ...
```

### Phase 4: Testing and Validation

#### 4.1 Unit Tests
**File**: `tests/test_sync_edge_cases.py` (new file)

```python
import pytest
from pathlib import Path
from pdd.sync_determine_operation import sync_determine_operation, validate_expected_files

class TestSyncEdgeCases:
    """Test sync edge cases with missing files and skip flags."""
    
    def test_missing_code_file_with_fingerprint(self, tmp_path):
        """Test sync behavior when code file is missing but fingerprint exists."""
        # Setup: create fingerprint but no actual files
        # Test: sync should detect missing file and regenerate
        pass
    
    def test_skip_tests_with_missing_example(self, tmp_path):
        """Test --skip-tests behavior when example file is missing."""
        # Setup: code exists, example missing, fingerprint indicates example should exist
        # Test: sync should regenerate example and stop (not try to generate tests)
        pass
    
    def test_validate_expected_files(self, tmp_path):
        """Test file validation function."""
        # Test various combinations of expected vs actual file existence
        pass
```

#### 4.2 Integration Tests
**File**: `tests/test_sync_regression_edge_cases.py` (new file)

```python
def test_regression_cleanup_scenario():
    """Test the exact scenario that causes regression test failures."""
    # 1. Run full sync
    # 2. Delete files but keep metadata
    # 3. Run sync --skip-tests
    # 4. Verify it regenerates correctly
    pass
```

#### 4.3 Enhanced Regression Test
**File**: `tests/sync_regression.sh`

Add specific test case for this edge case:

```bash
# Test edge case: files deleted but metadata remains
log "2c. Testing 'sync --skip-tests' with deleted files but existing metadata"
run_pdd_command sync "$SIMPLE_BASENAME"  # Create full state
rm -f "pdd/${SIMPLE_BASENAME}.py" "examples/${SIMPLE_BASENAME}_example.py" "tests/test_${SIMPLE_BASENAME}.py"  # Delete files
run_pdd_command sync --skip-tests "$SIMPLE_BASENAME"  # Should recover gracefully
check_exists "pdd/${SIMPLE_BASENAME}.py" "Regenerated code file"
check_exists "examples/${SIMPLE_BASENAME}_example.py" "Regenerated example file"
check_not_exists "tests/test_${SIMPLE_BASENAME}.py" "Test file (should not exist with --skip-tests)"
```

## Implementation Checklist

### Priority 1 (Critical - Fixes Regression)
- [ ] **URGENT**: Modify hash comparison logic to check file existence before comparing hashes (prevents None != "hash" false positives)
- [ ] **URGENT**: Add missing file detection to `_perform_sync_analysis()` before hash comparison
- [ ] Add skip flag parameters (`skip_tests`, `skip_verify`) to `sync_determine_operation()` function signature  
- [ ] Pass skip flags from `sync_orchestration.py:274` call site

### Priority 2 (Complete Solution)
- [ ] Implement `validate_expected_files()` function (lines 41-61)
- [ ] Implement `_handle_missing_expected_files()` recovery logic (lines 98-161)
- [ ] Implement `is_workflow_complete()` with skip awareness (lines 219-227)
- [ ] Update decision logic throughout to consider skip flags

### Priority 3 (Defensive Operations & Validation)
- [ ] Create safe file operation utilities (`safe_read_file`, `ensure_file_exists_for_operation`)
- [ ] Add defensive file reading throughout command functions  
- [ ] Write comprehensive unit tests
- [ ] Add integration tests for edge cases
- [ ] Enhance regression test with edge case scenarios
- [ ] Add logging/debugging for troubleshooting

## Risk Assessment

### Low Risk
- File validation functions (read-only operations)
- Enhanced logging and debugging
- Unit tests

### Medium Risk
- Modifying sync determine operation logic (well-tested area)
- Adding skip flag parameters (backward compatible)

### High Risk
- Changing core workflow completion logic
- Modifying hash comparison behavior

## Rollback Plan

1. **Git branch**: Implement in feature branch `fix/sync-skip-tests-edge-case`
2. **Incremental deployment**: Deploy changes in phases for easier rollback
3. **Regression testing**: Run full regression suite before each phase
4. **Monitoring**: Add debug logging to track new code paths

## Success Criteria

1. ✅ `sync --skip-tests` works reliably after file cleanup
2. ✅ Regression tests pass consistently
3. ✅ No regression in normal sync operations
4. ✅ Clear error messages for unrecoverable states
5. ✅ Proper handling of all skip flag combinations

## Timeline

- **Phase 1**: 2-3 days (core logic fixes)
- **Phase 2**: 1-2 days (skip flag integration)  
- **Phase 3**: 1-2 days (defensive operations)
- **Phase 4**: 2-3 days (testing and validation)

**Total**: 6-10 days

## Root Cause Validation - COMPLETED ✅

### Test Case Results (2025-07-02)

**Test File**: `test_root_cause_final.py`
**Status**: ALL 5 CRITICAL ISSUES CONFIRMED

#### Validation Results:
```
✅ CONFIRMED: Missing files cause analyze_conflict
✅ CONFIRMED: Expected correct behavior 
✅ CONFIRMED: Skip flags not supported
✅ CONFIRMED: Missing validation functions
✅ CONFIRMED: Skip flags not passed in orchestration

Issues confirmed: 5/5
```

#### Exact Failure Reproduction:
- **Setup**: Prompt exists, code/example/test deleted, metadata exists
- **Current Behavior**: `operation='analyze_conflict'` with `changed_files=['prompt', 'code', 'example', 'test']`
- **Expected Behavior**: `operation='generate'` to recreate missing code file
- **Impact**: `analyze_conflict` leads to LLM processing that hangs/times out

#### Function Signature Validation:
- **Current**: `sync_determine_operation(basename, language, target_coverage, budget, log_mode, prompts_dir)`
- **Missing**: `skip_tests`, `skip_verify` parameters
- **Call Site**: `sync_orchestration.py:274` doesn't pass skip flags

#### Missing Functions Confirmed:
- `validate_expected_files()` - ImportError (lines 41-61)
- `_handle_missing_expected_files()` - ImportError (lines 98-161)

### Implementation Priority - UPDATED

**CRITICAL (Fixes Regression)**: 
1. Add file existence validation before hash comparison in `_perform_sync_analysis()`
2. Handle missing files scenario to return `'generate'` instead of `'analyze_conflict'`
3. Add skip flag parameters to `sync_determine_operation()`
4. Pass skip flags from `sync_orchestration.py:274`

**HIGH (Complete Solution)**:
5. Implement `validate_expected_files()` function
6. Implement `_handle_missing_expected_files()` recovery logic

## Notes

- **Root cause definitively validated** through comprehensive testing
- This fix addresses a fundamental gap in sync state management where missing files trigger incorrect conflict analysis
- The solution is designed to be backward compatible
- Test case `test_root_cause_final.py` can be used for regression validation
- Additional logging will help diagnose similar issues in the future
- Consider this as foundation for more robust sync state handling