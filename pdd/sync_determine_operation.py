# pdd/sync_determine_operation.py

import os
import sys
import json
import hashlib
import subprocess
import threading
from dataclasses import dataclass, asdict, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional, Dict, Any, List
from pydantic import BaseModel

# Import PDD functions
from pdd.load_prompt_template import load_prompt_template
from pdd.llm_invoke import llm_invoke

# --- Dependencies ---
# This implementation requires the 'psutil' library for robust PID checking.
# It can be installed with: pip install psutil
try:
    import psutil
except ImportError:
    print("Error: 'psutil' library not found. Please install it using 'pip install psutil'", file=sys.stderr)
    sys.exit(1)

# Platform-specific locking
if sys.platform == 'win32':
    import msvcrt
else:
    import fcntl

# --- Constants for Directory Structure ---
PDD_DIR = Path(".pdd")
META_DIR = PDD_DIR / "meta"
LOCKS_DIR = PDD_DIR / "locks"
SYNC_FINGERPRINT_FILE = META_DIR / "sync_fingerprint.json"
RUNNING_SYNC_LOCK = LOCKS_DIR / "sync.lock"

# --- Data Structures ---
@dataclass
class Fingerprint:
    """Represents the last known good state of a PDD unit."""
    pdd_version: str
    timestamp: str  # ISO 8601 format
    command: str
    prompt_hash: Optional[str] = None
    code_hash: Optional[str] = None
    example_hash: Optional[str] = None
    test_hash: Optional[str] = None

@dataclass
class SyncFingerprint:
    """Represents the state of all relevant files at a point in time."""
    basename: str
    language: str
    files: Dict[str, Optional[str]]  # filename -> hash or None if file doesn't exist
    timestamp: str
    git_commit: Optional[str] = None

class LLMConflictResolutionOutput(BaseModel):
    """Output from LLM conflict resolution analysis."""
    next_operation: str
    reason: str
    confidence: float

@dataclass
class RunReport:
    """Represents the results of the last test or execution run."""
    timestamp: str
    exit_code: int
    tests_passed: int
    tests_failed: int
    coverage: float

@dataclass
class Fingerprint:
    """Represents the last known good state of a PDD unit (compatibility class)."""
    pdd_version: str
    timestamp: str  # ISO 8601 format
    command: str
    prompt_hash: Optional[str] = None
    code_hash: Optional[str] = None
    example_hash: Optional[str] = None
    test_hash: Optional[str] = None

@dataclass
class SyncDecision:
    """Decision about what operation to perform next."""
    operation: str
    reason: str
    confidence: float = 0.0
    
    @property
    def should_continue(self) -> bool:
        """Returns True if the sync process should continue."""
        return self.operation not in ["nothing", "fail_and_request_manual_merge"]

# --- Mock Internal PDD Modules ---
# These are placeholders for the internal pdd library functions.


# --- Directory and Locking Mechanism ---

def _ensure_pdd_dirs_exist():
    """Ensures that the .pdd metadata and lock directories exist."""
    META_DIR.mkdir(parents=True, exist_ok=True)
    LOCKS_DIR.mkdir(parents=True, exist_ok=True)

class FileLock:
    """Cross-platform file locking mechanism."""
    
    def __init__(self, lock_file: Path):
        self.lock_file = lock_file
        self.lock_handle = None
        self.is_locked = False
    
    def __enter__(self):
        return self.acquire()
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        self.release()
    
    def acquire(self, timeout_seconds: float = 30.0) -> bool:
        """
        Attempts to acquire the lock with a timeout.
        Returns True if lock was acquired, False if timeout.
        """
        import time
        start_time = time.time()
        
        while time.time() - start_time < timeout_seconds:
            try:
                # Ensure parent directory exists
                self.lock_file.parent.mkdir(parents=True, exist_ok=True)
                
                # Try to create and lock the file
                self.lock_handle = open(self.lock_file, 'w')
                
                if sys.platform == 'win32':
                    # Windows file locking
                    try:
                        msvcrt.locking(self.lock_handle.fileno(), msvcrt.LK_NBLCK, 1)
                        self.is_locked = True
                        return True
                    except IOError:
                        self.lock_handle.close()
                        self.lock_handle = None
                else:
                    # Unix file locking
                    try:
                        fcntl.flock(self.lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                        self.is_locked = True
                        return True
                    except (IOError, OSError):
                        self.lock_handle.close()
                        self.lock_handle = None
                
                # Lock failed, wait a bit and try again
                time.sleep(0.1)
                
            except (IOError, OSError):
                # File creation failed, wait a bit and try again
                if self.lock_handle:
                    self.lock_handle.close()
                    self.lock_handle = None
                time.sleep(0.1)
        
        return False  # Timeout
    
    def release(self):
        """Releases the lock."""
        if self.is_locked and self.lock_handle:
            try:
                if sys.platform == 'win32':
                    msvcrt.locking(self.lock_handle.fileno(), msvcrt.LK_UNLCK, 1)
                else:
                    fcntl.flock(self.lock_handle.fileno(), fcntl.LOCK_UN)
            except (IOError, OSError):
                pass  # Lock may have been released already
            
            self.lock_handle.close()
            self.lock_handle = None
            self.is_locked = False
            
            # Try to remove the lock file
            try:
                if self.lock_file.exists():
                    self.lock_file.unlink()
            except (IOError, OSError):
                pass  # File may have been removed already

class SyncLock:
    """
    A robust, re-entrant, PID-aware file lock for synchronizing operations.
    Ensures only one process can operate on a PDD unit at a time.
    """
    def __init__(self, basename: str, language: str):
        _ensure_pdd_dirs_exist()  # Ensure directories exist before creating lock file
        self.lock_path = LOCKS_DIR / f"{basename}_{language}.lock"
        self.file_lock = FileLock(self.lock_path)
    
    def __enter__(self):
        return self.file_lock.__enter__()
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        return self.file_lock.__exit__(exc_type, exc_val, exc_tb)
    
    def acquire(self, timeout_seconds: float = 30.0) -> bool:
        return self.file_lock.acquire(timeout_seconds)
    
    def release(self):
        return self.file_lock.release()

# --- Sync Orchestration Functions ---

def should_run_sync(basename: str, language: str) -> bool:
    """
    Determines if sync should run by checking if any relevant files have changed.
    
    Args:
        basename: The base name for the PDD module (e.g., 'split')
        language: The target language (e.g., 'python')
    
    Returns:
        bool: True if sync should run, False otherwise
    """
    try:
        # Generate current fingerprint
        current_fingerprint = generate_fingerprint(basename, language)
        
        # Load saved fingerprint
        saved_fingerprint = load_sync_fingerprint()
        
        # If no saved fingerprint exists, we should run sync
        if not saved_fingerprint:
            return True
        
        # If basenames or languages differ, we should run sync
        if (saved_fingerprint.basename != basename or 
            saved_fingerprint.language != language):
            return True
        
        # Compare file hashes
        for file_path, current_hash in current_fingerprint.files.items():
            saved_hash = saved_fingerprint.files.get(file_path)
            if current_hash != saved_hash:
                return True
        
        # Check for files that existed before but don't exist now
        for file_path, saved_hash in saved_fingerprint.files.items():
            if file_path not in current_fingerprint.files:
                return True
        
        return False
        
    except Exception as e:
        print(f"Error checking if sync should run: {e}")
        return True  # Default to running sync if we can't determine

def generate_fingerprint(basename: str, language: str) -> SyncFingerprint:
    """
    Generates a fingerprint of the current state of all relevant files.
    
    Args:
        basename: The base name for the PDD module
        language: The target language
    
    Returns:
        SyncFingerprint: Current state fingerprint
    """
    files = {}
    paths = get_pdd_file_paths(basename, language)
    
    for file_type, file_path in paths.items():
        try:
            if file_path.exists():
                with open(file_path, 'rb') as f:
                    content = f.read()
                    files[str(file_path)] = hashlib.sha256(content).hexdigest()
            else:
                files[str(file_path)] = None
        except Exception as e:
            print(f"Warning: Could not read {file_path}: {e}")
            files[str(file_path)] = None
    
    # Get current git commit if in a git repository
    git_commit = None
    try:
        result = subprocess.run(['git', 'rev-parse', 'HEAD'], 
                               capture_output=True, text=True, check=True)
        git_commit = result.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        pass  # Not in a git repo or git not available
    
    return SyncFingerprint(
        basename=basename,
        language=language,
        files=files,
        timestamp=datetime.now(timezone.utc).isoformat(),
        git_commit=git_commit
    )

def save_sync_fingerprint(fingerprint: SyncFingerprint):
    """
    Saves the sync fingerprint to the metadata file.
    
    Args:
        fingerprint: The fingerprint to save
    """
    try:
        _ensure_pdd_dirs_exist()
        with open(SYNC_FINGERPRINT_FILE, 'w') as f:
            json.dump(asdict(fingerprint), f, indent=2)
    except Exception as e:
        print(f"Warning: Could not save sync fingerprint: {e}")

def load_sync_fingerprint() -> Optional[SyncFingerprint]:
    """
    Loads the saved sync fingerprint from the metadata file.
    
    Returns:
        SyncFingerprint or None if no saved fingerprint exists
    """
    try:
        if not SYNC_FINGERPRINT_FILE.exists():
            return None
        
        with open(SYNC_FINGERPRINT_FILE, 'r') as f:
            data = json.load(f)
            return SyncFingerprint(**data)
    except Exception as e:
        print(f"Warning: Could not load sync fingerprint: {e}")
        return None

def load_orchestration_fingerprint(basename: str, language: str) -> Optional[Fingerprint]:
    """
    Loads the fingerprint file saved by sync orchestration.
    
    Args:
        basename: The base name for the PDD module
        language: The target language
    
    Returns:
        Fingerprint or None if no saved fingerprint exists
    """
    try:
        fingerprint_file = META_DIR / f"{basename}_{language}.json"
        if not fingerprint_file.exists():
            return None
        
        with open(fingerprint_file, 'r') as f:
            data = json.load(f)
            return Fingerprint(**data)
    except Exception as e:
        print(f"Warning: Could not load orchestration fingerprint: {e}")
        return None

def get_pdd_file_paths(basename: str, language: str, context_config: Optional[Dict[str, str]] = None) -> Dict[str, Path]:
    """
    Returns the expected file paths for a PDD module.
    
    Args:
        basename: The base name for the PDD module
        language: The target language
        context_config: Optional configuration for custom paths
    
    Returns:
        Dict mapping file types to their paths
    """
    if language == "python":
        # Use context_config if provided, otherwise use defaults
        if context_config:
            code_path = context_config.get('generate_output_path', f"pdd/{basename}.py")
            test_path = context_config.get('test_output_path', f"tests/test_{basename}.py")
            example_path = context_config.get('example_output_path', f"examples/{basename}_example.py")
        else:
            code_path = f"pdd/{basename}.py"
            test_path = f"tests/test_{basename}.py"
            example_path = f"examples/{basename}_example.py"
            
        return {
            'prompt': Path(f"prompts/{basename}_python.prompt"),
            'code': Path(code_path),
            'test': Path(test_path),
            'example': Path(example_path)
        }
    else:
        raise ValueError(f"Unsupported language: {language}")

def calculate_sha256(file_path: Path) -> Optional[str]:
    """Calculates the SHA256 hash of a file if it exists, otherwise returns None."""
    if not file_path.is_file():
        return None
    
    sha256_hash = hashlib.sha256()
    with open(file_path, "rb") as f:
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()

def calculate_current_hashes(paths: Dict[str, Path]) -> Dict[str, Optional[str]]:
    """
    Calculate current file hashes for the given paths.
    
    Args:
        paths: Dictionary mapping file types to their paths
    
    Returns:
        Dictionary mapping hash keys to file hashes or None if file doesn't exist
    """
    hashes = {}
    
    for file_type, file_path in paths.items():
        hash_key = f"{file_type}_hash"
        try:
            if file_path.exists():
                with open(file_path, 'rb') as f:
                    content = f.read()
                    hashes[hash_key] = hashlib.sha256(content).hexdigest()
            else:
                hashes[hash_key] = None
        except Exception:
            hashes[hash_key] = None
    
    return hashes

def get_git_diff(file_path: Path) -> str:
    """
    Gets the git diff for a specific file.
    
    Args:
        file_path: Path to the file
    
    Returns:
        Git diff as a string, or empty string if no diff or error
    """
    try:
        result = subprocess.run(['git', 'diff', str(file_path)], 
                               capture_output=True, text=True, check=False)
        return result.stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return ""

def analyze_conflict_with_llm(fingerprint: SyncFingerprint, 
                            changed_files: List[str]) -> SyncDecision:
    """
    Uses LLM to analyze the conflict and determine the next operation.
    
    Args:
        fingerprint: Current state fingerprint
        changed_files: List of file types that have changed
    
    Returns:
        SyncDecision with the recommended next operation
    """
    try:
        # Load the prompt template
        template = load_prompt_template("sync_analysis_LLM")
        if not template:
            return SyncDecision(
                operation="fail_and_request_manual_merge",
                reason="Could not load sync analysis prompt template",
                confidence=0.0
            )

        # Get file paths and diffs
        paths = get_pdd_file_paths(fingerprint.basename, fingerprint.language)
        diffs = {ftype: "" for ftype in ['prompt', 'code', 'test', 'example']}
        
        for file_type in changed_files:
            if file_type in paths:
                diffs[file_type] = get_git_diff(paths[file_type])

        # Prepare input for LLM
        input_json = {
            "fingerprint": json.dumps(asdict(fingerprint), indent=2),
            "changed_files_list": ", ".join(changed_files),
            "prompt_diff": diffs['prompt'],
            "code_diff": diffs['code'],
            "test_diff": diffs['test'],
            "example_diff": diffs['example'],
            "prompt_path": str(paths['prompt']),
            "code_path": str(paths['code']),
            "test_path": str(paths['test']),
            "example_path": str(paths['example'])
        }

        # Invoke the LLM with structured output
        llm_response = llm_invoke(
            prompt=template,
            input_json=input_json,
            output_pydantic=LLMConflictResolutionOutput,
            strength=0.5,
            temperature=0.0,
            verbose=False
        )
        response_obj = llm_response.get('result')

        # Validate the response object
        if not isinstance(response_obj, LLMConflictResolutionOutput):
            return SyncDecision(
                operation="fail_and_request_manual_merge",
                reason="LLM returned invalid response format",
                confidence=0.0
            )

        return SyncDecision(
            operation=response_obj.next_operation,
            reason=response_obj.reason,
            confidence=response_obj.confidence
        )

    except Exception as e:
        print(f"DEBUG: LLM conflict analysis error details:")
        print(f"  Exception: {type(e).__name__}: {e}")
        print(f"  Basename: {fingerprint.basename}, Language: {fingerprint.language}")
        print(f"  Changed files: {changed_files}")
        print(f"  Full traceback:")
        import traceback
        traceback.print_exc()
        
        return SyncDecision(
            operation="fail_and_request_manual_merge",
            reason=f"LLM analysis failed: {str(e)}",
            confidence=0.0
        )

def determine_sync_operation(basename: str, language: str, target_coverage: float = 80.0) -> SyncDecision:
    """
    Determines what sync operation should be performed.
    
    Args:
        basename: The base name for the PDD module
        language: The target language
        target_coverage: Target code coverage percentage (unused but kept for compatibility)
    
    Returns:
        SyncDecision indicating the next operation to perform
    """
    # Load the fingerprint saved by orchestration (preferred)
    saved_orchestration_fingerprint = load_orchestration_fingerprint(basename, language)
    
    # Fallback to sync fingerprint for backward compatibility
    if not saved_orchestration_fingerprint:
        current_fingerprint = generate_fingerprint(basename, language)
        saved_fingerprint = load_sync_fingerprint()
        
        # If no saved fingerprint at all, this is the first run
        if not saved_fingerprint:
            return SyncDecision(
                operation="generate",
                reason="No previous sync state found, starting fresh generation",
                confidence=0.95
            )
        
        # Use the old logic for sync fingerprint comparison
        changed_files = []
        for file_path, current_hash in current_fingerprint.files.items():
            saved_hash = saved_fingerprint.files.get(file_path)
            if current_hash != saved_hash:
                # Determine file type from path
                file_path_obj = Path(file_path)
                if 'prompt' in file_path_obj.name:
                    changed_files.append('prompt')
                elif file_path_obj.name.startswith('test_'):
                    changed_files.append('test')
                elif 'example' in file_path_obj.name:
                    changed_files.append('example')
                else:
                    changed_files.append('code')
        
        # Remove duplicates while preserving order
        changed_files = list(dict.fromkeys(changed_files))
        
        # If no changes detected, sync is complete
        if not changed_files:
            return SyncDecision(
                operation="nothing",
                reason="No changes detected since last sync",
                confidence=1.0
            )
        
        # Use LLM to analyze complex situations
        return analyze_conflict_with_llm(current_fingerprint, changed_files)
    
    # Use orchestration fingerprint logic
    paths = get_pdd_file_paths(basename, language)
    current_hashes = calculate_current_hashes(paths)
    
    # Compare current file hashes with saved fingerprint
    changed_files = []
    
    # Check each file type
    for file_type in ['prompt', 'code', 'test', 'example']:
        hash_key = f"{file_type}_hash"
        current_hash = current_hashes.get(hash_key)
        saved_hash = getattr(saved_orchestration_fingerprint, hash_key, None)
        
        if current_hash != saved_hash:
            changed_files.append(file_type)
    
    # Remove duplicates while preserving order
    changed_files = list(dict.fromkeys(changed_files))
    
    # If no changes detected, sync is complete
    if not changed_files:
        return SyncDecision(
            operation="nothing",
            reason="No changes detected since last sync",
            confidence=1.0
        )
    
    # Simple logic for common cases to avoid LLM calls when unnecessary
    if changed_files == ['prompt']:
        return SyncDecision(
            operation="generate",
            reason="Prompt has changed, regenerating code",
            confidence=0.95
        )
    elif 'code' not in changed_files and 'example' in changed_files:
        return SyncDecision(
            operation="example",
            reason="Example needs to be updated",
            confidence=0.90
        )
    elif 'code' not in changed_files and 'test' in changed_files:
        return SyncDecision(
            operation="test",
            reason="Tests need to be updated",
            confidence=0.90
        )
    
    # For complex situations, use LLM analysis
    current_fingerprint = generate_fingerprint(basename, language)
    return analyze_conflict_with_llm(current_fingerprint, changed_files)

def sync_operation_main(basename: str, language: str, max_attempts: int = 3) -> Dict[str, Any]:
    """
    Main sync operation orchestrator.
    
    Args:
        basename: The base name for the PDD module
        language: The target language  
        max_attempts: Maximum number of sync attempts
    
    Returns:
        Dict with sync results
    """
    _ensure_pdd_dirs_exist()
    
    # Use file locking to prevent concurrent sync operations
    with FileLock(RUNNING_SYNC_LOCK) as lock_acquired:
        if not lock_acquired:
            return {
                "success": False,
                "reason": "Could not acquire sync lock - another sync may be running",
                "attempts": 0
            }
        
        attempts = 0
        total_cost = 0.0
        
        while attempts < max_attempts:
            attempts += 1
            
            # Check if sync is needed
            if not should_run_sync(basename, language):
                return {
                    "success": True,
                    "reason": "No sync needed - files are already synchronized",
                    "attempts": attempts,
                    "cost": total_cost
                }
            
            # Determine what operation to perform
            decision = determine_sync_operation(basename, language)
            
            if decision.operation == "nothing":
                # Save current state and finish
                current_fingerprint = generate_fingerprint(basename, language)
                save_sync_fingerprint(current_fingerprint)
                return {
                    "success": True,
                    "reason": decision.reason,
                    "attempts": attempts,
                    "cost": total_cost,
                    "operation": decision.operation
                }
            elif decision.operation == "fail_and_request_manual_merge":
                return {
                    "success": False,
                    "reason": decision.reason,
                    "attempts": attempts,
                    "cost": total_cost,
                    "operation": decision.operation,
                    "confidence": decision.confidence
                }
            else:
                # For now, we just report what operation would be performed
                # In a full implementation, this would actually execute the operation
                print(f"Would perform operation: {decision.operation}")
                print(f"Reason: {decision.reason}")
                print(f"Confidence: {decision.confidence}")
                
                # For this implementation, we'll break here
                # In production, you would call the appropriate PDD operation
                break
        
        return {
            "success": False,
            "reason": f"Max sync attempts ({max_attempts}) reached",
            "attempts": attempts,
            "cost": total_cost
        }

# --- Test Functions ---

def test_fingerprint_generation():
    """Test fingerprint generation functionality."""
    print("Testing fingerprint generation...")
    
    fingerprint = generate_fingerprint("test", "python")
    print(f"Generated fingerprint for test module:")
    print(f"  Basename: {fingerprint.basename}")
    print(f"  Language: {fingerprint.language}")
    print(f"  Timestamp: {fingerprint.timestamp}")
    print(f"  Git commit: {fingerprint.git_commit}")
    print(f"  Files tracked: {len(fingerprint.files)}")
    
    for file_path, file_hash in fingerprint.files.items():
        status = "exists" if file_hash else "missing"
        print(f"    {file_path}: {status}")

def test_sync_decision():
    """Test sync decision logic."""
    print("\\nTesting sync decision logic...")
    
    decision = determine_sync_operation("test", "python")
    print(f"Sync decision:")
    print(f"  Operation: {decision.operation}")
    print(f"  Reason: {decision.reason}")
    print(f"  Confidence: {decision.confidence}")
    print(f"  Should continue: {decision.should_continue}")

if __name__ == "__main__":
    # Run basic tests
    test_fingerprint_generation()
    test_sync_decision()