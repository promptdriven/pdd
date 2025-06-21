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

PROMPTS_ROOT_DIR = Path("prompts")
CODE_ROOT_DIR = Path("src")
EXAMPLES_ROOT_DIR = Path("examples")
TESTS_ROOT_DIR = Path("tests")


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
class RunReport:
    """Represents the results of the last test or execution run."""
    timestamp: str
    exit_code: int
    tests_passed: int
    tests_failed: int
    coverage: float

@dataclass
class LLMConflictResolutionOutput:
    """Represents the structured output from the LLM for conflict resolution."""
    next_operation: str
    reason: str
    confidence: float

@dataclass
class SyncDecision:
    """Represents the recommended operation to run next."""
    operation: str
    reason: str
    details: Dict[str, Any] = field(default_factory=dict)

# --- Mock Internal PDD Modules ---
# These are placeholders for the internal pdd library functions.

def load_prompt_template(prompt_name: str) -> Optional[str]:
    """
    (MOCK) Loads a prompt template from the pdd library.
    In a real scenario, this would load from a package resource.
    """
    templates = {
        "sync_analysis_LLM.prompt": """
You are an expert software development assistant. Your task is to resolve a synchronization conflict in a PDD unit.
Both the user and the PDD tool have made changes, and you must decide the best course of action.

Analyze the following information:

**Last Known Good State (Fingerprint):**
```json
{fingerprint}
```

**Files Changed Since Last Sync:**
- {changed_files_list}

**Diffs:**

--- PROMPT DIFF ---
{prompt_diff}
--- END PROMPT DIFF ---

--- CODE DIFF ---
{code_diff}
--- END CODE DIFF ---

--- TEST DIFF ---
{test_diff}
--- END TEST DIFF ---

--- EXAMPLE DIFF ---
{example_diff}
--- END EXAMPLE DIFF ---

Based on the diffs, determine the user's intent and the nature of the conflict.
Respond with a JSON object recommending the next operation. The possible operations are:
- "generate": The prompt changes are significant; regenerate the code.
- "update": The code changes are valuable; update the prompt to reflect them.
- "fix": The test changes seem to be fixing a bug; try to fix the code.
- "merge_manually": The conflict is too complex. Ask the user to merge changes.

Your JSON response must have the following format:
{{
  "next_operation": "your_recommendation",
  "reason": "A clear, concise explanation of why you chose this operation.",
  "confidence": 0.9
}}
"""
    }
    return templates.get(prompt_name)

def llm_invoke(prompt: str, **kwargs) -> Dict[str, Any]:
    """
    (MOCK) Invokes the LLM with a given prompt.
    This mock version provides a deterministic response for demonstration.
    """
    print("--- (MOCK) LLM Invocation ---")
    print(f"Prompt sent to LLM:\n{prompt[:500]}...")
    # In a real scenario, this would call an actual LLM API.
    # Here, we return a canned response with low confidence to test the failure path.
    response_obj = LLMConflictResolutionOutput(
        next_operation="update",
        reason="Mock LLM analysis determined that the manual code changes are significant but confidence is low.",
        confidence=0.70
    )
    return {
        "result": response_obj,
        "cost": 0.001,
        "model_name": "mock-gpt-4"
    }


# --- Directory and Locking Mechanism ---

def _ensure_pdd_dirs_exist():
    """Ensures that the .pdd metadata and lock directories exist."""
    META_DIR.mkdir(parents=True, exist_ok=True)
    LOCKS_DIR.mkdir(parents=True, exist_ok=True)

_lock_registry = threading.local()

class SyncLock:
    """
    A robust, re-entrant, PID-aware file lock for synchronizing operations.
    Ensures only one process can operate on a PDD unit at a time.
    """
    def __init__(self, basename: str, language: str):
        _ensure_pdd_dirs_exist()  # Ensure directories exist before creating lock file
        self.lock_dir = LOCKS_DIR
        self.lock_path = self.lock_dir / f"{basename}_{language}.lock"
        self._lock_fd = None
        self._is_reentrant_acquisition = False
        self.lock_key = str(self.lock_path)
        # The file descriptor is only stored on the instance that actually acquires the lock
        self._is_lock_owner = False

    @property
    def lock_file_path(self):
        return self.lock_path

    def _get_lock_count(self) -> int:
        if not hasattr(_lock_registry, 'counts'):
            _lock_registry.counts = {}
        return _lock_registry.counts.get(self.lock_key, 0)

    def _increment_lock_count(self):
        if not hasattr(_lock_registry, 'counts'):
            _lock_registry.counts = {}
        count = _lock_registry.counts.get(self.lock_key, 0)
        _lock_registry.counts[self.lock_key] = count + 1

    def _decrement_lock_count(self) -> int:
        if not hasattr(_lock_registry, 'counts'):
            _lock_registry.counts = {}
        count = _lock_registry.counts.get(self.lock_key, 0)
        if count > 0:
            _lock_registry.counts[self.lock_key] = count - 1
        return _lock_registry.counts.get(self.lock_key, 0)

    def acquire(self):
        """
        Acquires an exclusive lock, handling stale locks from crashed processes.
        Raises TimeoutError if the lock is held by another active process.
        """
        lock_count = self._get_lock_count()
        if lock_count > 0:  # Re-entrancy
            self._is_reentrant_acquisition = True
            self._increment_lock_count()
            return

        # First time acquiring in this thread. Perform the actual lock.
        if self.lock_path.exists():
            try:
                pid_str = self.lock_path.read_text().strip()
                if pid_str:
                    pid = int(pid_str)
                    if psutil.pid_exists(pid):
                        raise TimeoutError(f"is locked by another process (PID: {pid})")
                    else:
                        self.lock_path.unlink()
            except (ValueError, FileNotFoundError):
                # Corrupted or unreadable lock file, treat as stale
                self.lock_path.unlink(missing_ok=True)

        # Use O_TRUNC to ensure we overwrite any previous (e.g., corrupted) content
        self._lock_fd = os.open(self.lock_path, os.O_CREAT | os.O_WRONLY | os.O_TRUNC)
        self._is_lock_owner = True

        try:
            if sys.platform == 'win32':
                msvcrt.locking(self._lock_fd, msvcrt.LK_NBLCK, 1)
            else:
                fcntl.flock(self._lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except (IOError, BlockingIOError):
            os.close(self._lock_fd)
            self._lock_fd = None
            self._is_lock_owner = False
            raise TimeoutError("Failed to acquire lock; another process may have just started.")

        os.write(self._lock_fd, str(os.getpid()).encode())
        os.fsync(self._lock_fd)
        self._increment_lock_count()

    def release(self):
        """Releases the lock and cleans up the lock file."""
        new_count = self._decrement_lock_count()
        
        if new_count == 0 and self._is_lock_owner:
            # This was the last lock holder in this thread, so release the file lock.
            if self._lock_fd:
                if sys.platform != 'win32':
                     fcntl.flock(self._lock_fd, fcntl.LOCK_UN)
                os.close(self._lock_fd)
                self._lock_fd = None
            
            try:
                if self.lock_path.exists():
                    # Safety check: only delete if we are still the owner
                    pid_str = self.lock_path.read_text().strip()
                    if not pid_str or int(pid_str) == os.getpid():
                        self.lock_path.unlink()
            except (OSError, ValueError, FileNotFoundError):
                pass # Ignore errors on cleanup

    def __enter__(self):
        self.acquire()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.release()


# --- State Analysis Functions ---

LANGUAGE_EXTENSIONS = {
    "python": "py",
    "javascript": "js",
    "typescript": "ts",
    "rust": "rs",
    "go": "go",
}

def get_language_extension(language: str) -> str:
    """Gets the file extension for a given language."""
    if language not in LANGUAGE_EXTENSIONS:
        raise ValueError(f"Unsupported language: {language}")
    return LANGUAGE_EXTENSIONS[language]

def get_pdd_file_paths(basename: str, language: str) -> Dict[str, Path]:
    """Returns configuration-aware dictionary mapping file types to their expected paths."""
    from .generate_output_paths import generate_output_paths
    from .get_extension import get_extension
    
    ext = get_language_extension(language)
    file_extension = get_extension(language)
    
    # Use PDD's configuration system to determine paths
    # Generate paths for each operation type to get the actual configured directories
    generate_paths = generate_output_paths(
        command='generate',
        output_locations={},  # No user overrides, use defaults/env vars
        basename=basename,
        language=language,
        file_extension=file_extension
    )
    
    example_paths = generate_output_paths(
        command='example',
        output_locations={},
        basename=basename,
        language=language,
        file_extension=file_extension
    )
    
    test_paths = generate_output_paths(
        command='test',
        output_locations={},
        basename=basename,
        language=language,
        file_extension=file_extension
    )
    
    return {
        'prompt': PROMPTS_ROOT_DIR / f"{basename}_{language}.prompt",  # Prompt path remains in prompts dir
        'code': Path(generate_paths.get('output', f"{basename}.{ext}")),
        'example': Path(example_paths.get('output', f"examples/{basename}_example.{ext}")),
        'test': Path(test_paths.get('output', f"tests/test_{basename}.{ext}")),
    }

def calculate_sha256(file_path: Path) -> Optional[str]:
    """Calculates the SHA256 hash of a file if it exists, otherwise returns None."""
    if not file_path.is_file():
        return None
    
    sha256_hash = hashlib.sha256()
    with open(file_path, "rb") as f:
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()

def _read_json_file(file_path: Path, data_class) -> Optional[Any]:
    """Generic JSON file reader and validator."""
    if not file_path.is_file():
        return None
    try:
        with open(file_path, 'r') as f:
            data = json.load(f)
            return data_class(**data)
    except (json.JSONDecodeError, TypeError):
        # Catches corrupted file, or if data doesn't match dataclass fields
        return None

def read_fingerprint(basename: str, language: str) -> Optional[Fingerprint]:
    """Reads and validates the JSON fingerprint file."""
    fingerprint_path = META_DIR / f"{basename}_{language}.json"
    return _read_json_file(fingerprint_path, Fingerprint)

def read_run_report(basename: str, language: str) -> Optional[RunReport]:
    """Reads and validates the JSON run report file."""
    report_path = META_DIR / f"{basename}_{language}_run.json"
    return _read_json_file(report_path, RunReport)

def calculate_current_hashes(paths: Dict[str, Path]) -> Dict[str, Optional[str]]:
    """Computes the hashes for all current files on disk."""
    return {
        f"{file_type}_hash": calculate_sha256(path)
        for file_type, path in paths.items()
    }

# --- LLM-based Conflict Analysis ---

def get_git_diff(file_path: Path) -> str:
    """
    Gets the git diff of a file against its last committed version (HEAD).
    Returns the full content for untracked files.
    """
    if not file_path.exists():
        return ""
    
    # Try to use a relative path if possible, as git's output is cleaner.
    # This is safe because test fixtures chdir into the repo root.
    try:
        path_for_git = file_path.relative_to(Path.cwd())
    except ValueError:
        # Not relative to CWD, use the original absolute path.
        path_for_git = file_path

    # Use 'git status' to check if the file is tracked
    try:
        status_result = subprocess.run(
            ['git', 'status', '--porcelain', str(path_for_git)],
            capture_output=True, text=True, check=True, encoding='utf-8'
        )
        is_untracked = status_result.stdout.strip().startswith('??')
    except (subprocess.CalledProcessError, FileNotFoundError):
        # Not a git repo, git not found, or file not in repo. Fallback to content.
        return file_path.read_text(encoding='utf-8')

    command = ['git', 'diff']
    if is_untracked:
        # Diff against nothing to show the whole file as an addition
        # Use /dev/null for POSIX and NUL for Windows
        null_device = "NUL" if sys.platform == "win32" else "/dev/null"
        command.extend(['--no-index', null_device, str(path_for_git)])
    else:
        # Diff against the last commit
        command.extend(['HEAD', '--', str(path_for_git)])
        
    try:
        # The `git diff` command returns exit code 1 if there are differences,
        # which `check=True` would interpret as an error. We must not use it.
        diff_result = subprocess.run(
            command, capture_output=True, text=True, encoding='utf-8'
        )
        return diff_result.stdout
    except FileNotFoundError:
        # Fallback if git command is not found
        return file_path.read_text(encoding='utf-8')

def analyze_conflict_with_llm(
    basename: str,
    language: str,
    fingerprint: Fingerprint,
    changed_files: List[str]
) -> SyncDecision:
    """
    Uses an LLM to analyze a complex sync conflict and recommend an operation.
    """
    try:
        prompt_template = load_prompt_template("sync_analysis_LLM.prompt")
        if not prompt_template:
            return SyncDecision(
                operation="fail_and_request_manual_merge",
                reason="Failed to load LLM analysis prompt template 'sync_analysis_LLM.prompt'."
            )

        paths = get_pdd_file_paths(basename, language)
        diffs = {ftype: "" for ftype in ['prompt', 'code', 'test', 'example']}
        
        for file_type in changed_files:
            if file_type in paths:
                diffs[file_type] = get_git_diff(paths[file_type])

        # Format the prompt for the LLM
        formatted_prompt = prompt_template.format(
            fingerprint=json.dumps(asdict(fingerprint), indent=2),
            changed_files_list=", ".join(changed_files),
            prompt_diff=diffs['prompt'],
            code_diff=diffs['code'],
            test_diff=diffs['test'],
            example_diff=diffs['example']
        )

        # Invoke the LLM
        llm_response = llm_invoke(prompt=formatted_prompt)
        response_obj = llm_response.get('result')

        # Validate the response object
        if not isinstance(response_obj, LLMConflictResolutionOutput):
            return SyncDecision(
                operation="fail_and_request_manual_merge",
                reason=f"LLM did not return the expected Pydantic object. Got type: {type(response_obj).__name__}",
                details={"raw_response": str(response_obj)}
            )

        next_op = response_obj.next_operation
        reason = response_obj.reason
        confidence = response_obj.confidence

        if confidence < 0.75:
            return SyncDecision(
                operation="fail_and_request_manual_merge",
                reason=f"LLM analysis confidence ({confidence:.2f}) is below threshold. "
                       f"LLM suggestion was: '{next_op}' - {reason}",
                details=asdict(response_obj)
            )
        
        return SyncDecision(
            operation=next_op,
            reason=f"LLM analysis: {reason}",
            details=asdict(response_obj)
        )

    except Exception as e:
        return SyncDecision(
            operation="fail_and_request_manual_merge",
            reason=f"LLM conflict analysis failed: {e}",
            details={"raw_response": str(locals().get('llm_response', {}).get('result'))}
        )


# --- Main Decision Function ---

def determine_sync_operation(
    basename: str,
    language: str,
    target_coverage: float = 80.0
) -> SyncDecision:
    """
    Analyzes a PDD unit's state and determines the next operation.

    This function is the core of the `pdd sync` command, providing a deterministic,
    reliable, and safe decision based on runtime signals and file fingerprints.

    Args:
        basename: The base name of the PDD unit (e.g., 'calculator').
        language: The programming language of the unit (e.g., 'python').
        target_coverage: The desired test coverage percentage.

    Returns:
        A SyncDecision object with the recommended operation and reason.
    """
    with SyncLock(basename, language):
        # 1. Check Runtime Signals First (highest priority)
        run_report = read_run_report(basename, language)
        if run_report:
            if run_report.exit_code != 0:
                return SyncDecision(
                    operation='crash',
                    reason=f"The last run exited with a non-zero code ({run_report.exit_code}). "
                           "This indicates a crash that must be fixed.",
                    details=asdict(run_report)
                )
            if run_report.tests_failed > 0:
                return SyncDecision(
                    operation='fix',
                    reason=f"The last test run had {run_report.tests_failed} failing tests. "
                           "These must be fixed.",
                    details=asdict(run_report)
                )
            if run_report.coverage < target_coverage:
                return SyncDecision(
                    operation='test',
                    reason=f"Current test coverage ({run_report.coverage}%) is below the "
                           f"target ({target_coverage}%). More tests are needed.",
                    details=asdict(run_report)
                )

        # 2. Analyze File State
        paths = get_pdd_file_paths(basename, language)
        fingerprint = read_fingerprint(basename, language)
        current_hashes = calculate_current_hashes(paths)
        
        # 3. Implement the Decision Tree
        
        # Case: No Fingerprint (new or untracked unit)
        if not fingerprint:
            if paths['prompt'].exists():
                return SyncDecision(
                    operation='generate',
                    reason="No fingerprint file found, but a prompt exists. This appears to be a new PDD unit."
                )
            else:
                return SyncDecision(
                    operation='nothing',
                    reason="No PDD fingerprint and no prompt file found. Nothing to do."
                )

        # Compare current hashes with fingerprint
        fingerprint_hashes = {
            'prompt_hash': fingerprint.prompt_hash,
            'code_hash': fingerprint.code_hash,
            'example_hash': fingerprint.example_hash,
            'test_hash': fingerprint.test_hash,
        }
        
        changed_files = [
            file_type.replace('_hash', '')
            for file_type, f_hash in fingerprint_hashes.items()
            if current_hashes.get(file_type) != f_hash
        ]
        
        # Case: No Changes
        if not changed_files:
            return SyncDecision(
                operation='nothing',
                reason="All files are synchronized with the last known good state."
            )

        details = {"changed_files": changed_files}
        # Case: Simple Changes (Single File Modified)
        if len(changed_files) == 1:
            change = changed_files[0]
            if change == 'prompt':
                return SyncDecision('generate', "The prompt has been modified. Code should be regenerated.", details)
            if change == 'code':
                return SyncDecision('update', "The code has been modified manually. The prompt should be updated.", details)
            if change == 'test':
                return SyncDecision('test', "The test file has been modified. The new tests should be run.", details)
            if change == 'example':
                # 'verify' is a pdd command to run the example file
                return SyncDecision('verify', "The example file has been modified. It should be verified.", details)

        # Case: Complex Changes (Multiple Files Modified / Conflicts)
        if len(changed_files) > 1:
            return SyncDecision(
                operation='analyze_conflict',
                reason=f"Multiple files have been modified since the last sync: {', '.join(changed_files)}.",
                details=details
            )
            
        # Fallback, should not be reached
        return SyncDecision('nothing', 'Analysis complete, no operation required.')