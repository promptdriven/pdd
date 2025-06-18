# sync_determine_operation_python.py

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
{
  "next_operation": "your_recommendation",
  "reason": "A clear, concise explanation of why you chose this operation.",
  "confidence": 0.9
}
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
    # Here, we return a canned response for 'update' as a default.
    response_json = {
        "next_operation": "update",
        "reason": "Mock LLM analysis determined that the manual code changes are significant and should be preserved by updating the prompt.",
        "confidence": 0.85
    }
    return {
        "result": json.dumps(response_json),
        "cost": 0.001,
        "model_name": "mock-gpt-4"
    }


# --- Locking Mechanism ---

_lock_registry = threading.local()

class SyncLock:
    """
    A robust, re-entrant, PID-aware file lock for synchronizing operations.
    Ensures only one process can operate on a PDD unit at a time.
    """
    def __init__(self, basename: str, language: str):
        self.lock_dir = Path(".pdd/locks")
        self.lock_dir.mkdir(parents=True, exist_ok=True)
        self.lock_path = self.lock_dir / f"{basename}_{language}.lock"
        self._lock_file_descriptor = None

    def _is_locked_by_current_process(self) -> bool:
        """Checks if the current process already holds the lock."""
        return getattr(_lock_registry, str(self.lock_path), False)

    def _set_locked_by_current_process(self, locked: bool):
        """Marks the lock as held/not held by the current process."""
        setattr(_lock_registry, str(self.lock_path), locked)

    def acquire(self):
        """
        Acquires an exclusive lock, handling stale locks from crashed processes.
        Raises TimeoutError if the lock is held by another active process.
        """
        if self._is_locked_by_current_process():  # Re-entrancy
            return

        if self.lock_path.exists():
            try:
                pid_str = self.lock_path.read_text().strip()
                if pid_str:
                    pid = int(pid_str)
                    if psutil.pid_exists(pid):
                        raise TimeoutError(
                            f"Sync operation is already running for this unit "
                            f"by process {pid}."
                        )
                    else:
                        # Stale lock file, remove it
                        self.lock_path.unlink()
            except (ValueError, FileNotFoundError):
                # Corrupt or concurrently removed lock file, try to acquire
                pass

        # Acquire the lock
        self._lock_file_descriptor = os.open(self.lock_path, os.O_CREAT | os.O_WRONLY)
        
        try:
            if sys.platform == 'win32':
                msvcrt.locking(self._lock_file_descriptor, msvcrt.LK_NBLCK, 1)
            else:
                fcntl.flock(self._lock_file_descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except (IOError, BlockingIOError):
            os.close(self._lock_file_descriptor)
            raise TimeoutError(
                "Failed to acquire lock; another process may have just started."
            )

        # Write current PID to the lock file
        os.write(self._lock_file_descriptor, str(os.getpid()).encode())
        os.fsync(self._lock_file_descriptor) # Ensure it's written to disk
        self._set_locked_by_current_process(True)

    def release(self):
        """Releases the lock and cleans up the lock file."""
        if not self._is_locked_by_current_process():
            return

        if self._lock_file_descriptor:
            if sys.platform != 'win32':
                 fcntl.flock(self._lock_file_descriptor, fcntl.LOCK_UN)
            os.close(self._lock_file_descriptor)
            self._lock_file_descriptor = None
        
        try:
            if self.lock_path.exists():
                self.lock_path.unlink()
        except OSError:
            pass # Ignore errors on cleanup
        
        self._set_locked_by_current_process(False)

    def __enter__(self):
        self.acquire()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.release()


# --- State Analysis Functions ---

LANG_EXT_MAP = {
    "python": "py",
    "javascript": "js",
    "typescript": "ts",
    "rust": "rs",
    "go": "go",
}

def get_pdd_file_paths(basename: str, language: str) -> Dict[str, Path]:
    """Returns a dictionary mapping file types to their expected paths."""
    ext = LANG_EXT_MAP.get(language, language)
    return {
        'prompt': Path(f"prompts/{basename}_{language}.prompt"),
        'code': Path(f"src/{basename}.{ext}"),
        'example': Path(f"examples/{basename}_example.{ext}"),
        'test': Path(f"tests/test_{basename}.{ext}"),
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
            # Basic check to see if keys match dataclass fields
            if all(key in data for key in data_class.__annotations__):
                 return data_class(**data)
            return None # Data doesn't match expected structure
    except (json.JSONDecodeError, TypeError):
        return None # Corrupt file or type mismatch

def read_fingerprint(basename: str, language: str) -> Optional[Fingerprint]:
    """Reads and validates the JSON fingerprint file."""
    meta_dir = Path(".pdd/meta")
    fingerprint_path = meta_dir / f"{basename}_{language}.json"
    return _read_json_file(fingerprint_path, Fingerprint)

def read_run_report(basename: str, language: str) -> Optional[RunReport]:
    """Reads and validates the JSON run report file."""
    meta_dir = Path(".pdd/meta")
    report_path = meta_dir / f"{basename}_{language}_run.json"
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
        return "File does not exist."
    
    # Use 'git status' to check if the file is tracked
    try:
        status_result = subprocess.run(
            ['git', 'status', '--porcelain', str(file_path)],
            capture_output=True, text=True, check=True, encoding='utf-8'
        )
        is_untracked = status_result.stdout.strip().startswith('??')
    except (subprocess.CalledProcessError, FileNotFoundError):
        # Not a git repo or git not found, return file content
        return f"(Not a git repo) Current content:\n{file_path.read_text(encoding='utf-8')}"

    command = ['git', 'diff']
    if is_untracked:
        # Diff against nothing to show the whole file as an addition
        command.extend(['--no-index', '/dev/null', str(file_path)])
    else:
        # Diff against the last commit
        command.extend(['HEAD', '--', str(file_path)])
        
    try:
        diff_result = subprocess.run(
            command, capture_output=True, text=True, check=True, encoding='utf-8'
        )
        return diff_result.stdout or "(No changes)"
    except subprocess.CalledProcessError as e:
        return f"Error getting diff: {e.stderr}"

def analyze_conflict_with_llm(
    basename: str,
    language: str,
    fingerprint: Fingerprint,
    changed_files: List[str]
) -> SyncDecision:
    """
    Uses an LLM to analyze a complex sync conflict and recommend an operation.
    """
    prompt_template = load_prompt_template("sync_analysis_LLM.prompt")
    if not prompt_template:
        return SyncDecision(
            operation="fail_and_request_manual_merge",
            reason="LLM analysis prompt template 'sync_analysis_LLM.prompt' not found."
        )

    paths = get_pdd_file_paths(basename, language)
    diffs = {ftype: "" for ftype in ['prompt', 'code', 'test', 'example']}
    
    for file_type in changed_files:
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

    # Parse and validate the response
    try:
        response_data = json.loads(llm_response['result'])
        next_op = response_data.get("next_operation")
        reason = response_data.get("reason")
        confidence = response_data.get("confidence", 0.0)

        if not all([next_op, reason]):
            raise ValueError("LLM response missing required keys.")

        if confidence < 0.75:
            return SyncDecision(
                operation="fail_and_request_manual_merge",
                reason=f"LLM analysis confidence ({confidence:.2f}) is too low. "
                       f"LLM suggestion was: '{next_op}' - {reason}",
                details=response_data
            )
        
        return SyncDecision(
            operation=next_op,
            reason=f"LLM analysis: {reason}",
            details=response_data
        )

    except (json.JSONDecodeError, ValueError) as e:
        return SyncDecision(
            operation="fail_and_request_manual_merge",
            reason=f"Failed to parse or validate LLM response: {e}",
            details={"raw_response": llm_response.get('result')}
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
            return SyncDecision(
                operation='generate',
                reason="No fingerprint file found. This appears to be a new or untracked PDD unit."
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

        # Case: Simple Changes (Single File Modified)
        if len(changed_files) == 1:
            change = changed_files[0]
            details = {"changed_file": change}
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
                details={"changed_files": changed_files, "fingerprint": asdict(fingerprint)}
            )
            
        # Fallback, should not be reached
        return SyncDecision('nothing', 'Analysis complete, no operation required.')


# --- Example Usage and Demonstration ---

def setup_test_environment(scenario: str, basename="calculator", language="python"):
    """Creates dummy files to simulate different states."""
    print(f"\n--- Setting up scenario: {scenario} ---")
    # Clean up previous state
    for d in [".pdd/locks", ".pdd/meta", "prompts", "src", "examples", "tests"]:
        if Path(d).exists():
            for f in Path(d).glob(f"{basename}*"): f.unlink(missing_ok=True)
            for f in Path(d).glob(f"test_{basename}*"): f.unlink(missing_ok=True)
            for f in Path(d).glob(f"*.lock"): f.unlink(missing_ok=True)
            
    # Create directories
    for d in [".pdd/meta", "prompts", "src", "examples", "tests"]:
        Path(d).mkdir(parents=True, exist_ok=True)

    paths = get_pdd_file_paths(basename, language)
    
    if scenario == "new_unit":
        paths['prompt'].write_text("Create a calculator that can add two numbers.")
    
    elif scenario in ["synced", "prompt_changed", "code_changed", "conflict"]:
        # Create a base synced state
        paths['prompt'].write_text("p1")
        paths['code'].write_text("c1")
        paths['example'].write_text("e1")
        paths['test'].write_text("t1")
        
        fingerprint_data = {
            "pdd_version": "1.0", "timestamp": datetime.now(timezone.utc).isoformat(), "command": "generate",
            "prompt_hash": calculate_sha256(paths['prompt']),
            "code_hash": calculate_sha256(paths['code']),
            "example_hash": calculate_sha256(paths['example']),
            "test_hash": calculate_sha256(paths['test']),
        }
        with open(f".pdd/meta/{basename}_{language}.json", "w") as f:
            json.dump(fingerprint_data, f)
            
        if scenario == "prompt_changed":
            paths['prompt'].write_text("p2 - changed")
        elif scenario == "code_changed":
            paths['code'].write_text("c2 - changed")
        elif scenario == "conflict":
            paths['prompt'].write_text("p2 - changed")
            paths['code'].write_text("c2 - changed")

    elif scenario == "tests_failed":
        run_report_data = {"timestamp": datetime.now(timezone.utc).isoformat(), "exit_code": 0, "tests_passed": 5, "tests_failed": 2, "coverage": 90.0}
        with open(f".pdd/meta/{basename}_{language}_run.json", "w") as f:
            json.dump(run_report_data, f)
            
    elif scenario == "program_crashed":
        run_report_data = {"timestamp": datetime.now(timezone.utc).isoformat(), "exit_code": 139, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0}
        with open(f".pdd/meta/{basename}_{language}_run.json", "w") as f:
            json.dump(run_report_data, f)

def run_demonstration():
    """Runs through several scenarios to demonstrate the logic."""
    basename = "calculator"
    language = "python"
    
    scenarios = [
        "new_unit",
        "synced",
        "prompt_changed",
        "code_changed",
        "tests_failed",
        "program_crashed",
        "conflict"
    ]
    
    for scenario in scenarios:
        setup_test_environment(scenario, basename, language)
        
        try:
            decision = determine_sync_operation(basename, language)
            print(f"Decision: {decision.operation}")
            print(f"Reason: {decision.reason}")
            
            # If the decision is to analyze a conflict, run the next step
            if decision.operation == 'analyze_conflict':
                print("\n--- Running conflict analysis ---")
                fingerprint = read_fingerprint(basename, language)
                conflict_decision = analyze_conflict_with_llm(
                    basename, language, fingerprint, decision.details['changed_files']
                )
                print(f"Conflict Decision: {conflict_decision.operation}")
                print(f"Conflict Reason: {conflict_decision.reason}")

        except TimeoutError as e:
            print(f"Error: {e}")
        except Exception as e:
            print(f"An unexpected error occurred: {e}")

if __name__ == "__main__":
    run_demonstration()
