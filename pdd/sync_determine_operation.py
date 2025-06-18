import dataclasses
import datetime
import hashlib
import json
import os
import pathlib
import platform
import subprocess
import sys
import time
from typing import Any, Dict, List, Optional, Tuple, Union

# Platform-specific locking
if platform.system() == "Windows":
    import msvcrt
else:
    import fcntl

# Try to import psutil, make it optional for SyncLock robustness but highly recommended.
try:
    import psutil
except ImportError:
    psutil = None
    # print("Warning: psutil library not found. Stale lock detection will be less robust.", file=sys.stderr)


# Placeholder for PDD version, to be stored in fingerprints.
PDD_VERSION = "0.1.0" 

# --- Mock/Placeholder Internal Modules ---
# In a real PDD system, these would be imported from pdd.utils or similar.
def load_prompt_template(prompt_name: str) -> Optional[str]:
    """Mocks loading a prompt template for LLM interaction."""
    # print(f"[MOCK] pdd.load_prompt_template: Loading '{prompt_name}'")
    if prompt_name == "sync_analysis_LLM.prompt":
        return """
Analyze the PDD unit state to resolve synchronization conflicts.
Fingerprint: {fingerprint}
Changed Files: {changed_files_list}

Prompt Diff (Current vs HEAD):
```diff
{prompt_diff}
```

Code Diff (Current vs HEAD):
```diff
{code_diff}
```

Example Diff (Current vs HEAD):
```diff
{example_diff}
```

Test Diff (Current vs HEAD):
```diff
{test_diff}
```

Based on this information, provide the recommended next PDD operation, a reason for it,
and your confidence in this recommendation (0.0 to 1.0).
Return ONLY a JSON object with keys "next_operation", "reason", and "confidence".
Example operations: 'generate', 'update', 'fix', 'test', 'verify', 'manual_review'.
"""
    return None

def llm_invoke(
    prompt: str, 
    input_json: Optional[Dict[str, Any]] = None, 
    strength: float = 0.5, # Example parameter
    temperature: float = 0.7, # Example parameter
    verbose: bool = False, # Example parameter
    output_pydantic: Optional[Any] = None # Example parameter
) -> Dict[str, Any]:
    """Mocks an LLM invocation call."""
    # print(f"[MOCK] pdd.llm_invoke: Called with strength={strength}, temperature={temperature}")
    # if verbose:
    #     print(f"[MOCK] Full prompt for LLM:\n{prompt}")
    
    # Simplified mock response for conflict analysis
    mock_llm_response_json_str = json.dumps({
        "next_operation": "update", # Default mock action
        "reason": "LLM mock: Detected changes in both prompt and code. Suggesting 'update' to reconcile.",
        "confidence": 0.80 
    })
    
    return {
        "result": mock_llm_response_json_str, # LLM is expected to return a JSON string for this use case
        "cost": 0.0005, # Mock cost
        "model_name": "mock_llm_model_v1" # Mock model name
    }
# --- End Mock/Placeholder Internal Modules ---


# 1. Data Structures
@dataclasses.dataclass
class Fingerprint:
    pdd_version: str
    timestamp: str  # ISO 8601 format
    command: str  # The PDD command that generated this fingerprint (e.g., "generate", "fix")
    prompt_hash: Optional[str]
    code_hash: Optional[str]
    example_hash: Optional[str]
    test_hash: Optional[str]

@dataclasses.dataclass
class RunReport:
    timestamp: str # ISO 8601 format
    exit_code: int
    tests_passed: int
    tests_failed: int
    coverage: float # Range 0.0 to 1.0

@dataclasses.dataclass
class SyncDecision:
    operation: str  # e.g., 'generate', 'fix', 'update', 'test', 'crash', 'analyze_conflict', 'nothing', 'verify', 'fail_and_request_manual_merge'
    reason: str
    confidence: float = 1.0 # Confidence in the decision (0.0 to 1.0)
    details: Dict[str, Any] = dataclasses.field(default_factory=dict) # Optional extra info

# Language specific configurations (extensible)
LANGUAGE_CONFIG = {
    "python": {"extension": ".py", "prompt_extension": ".prompt"},
    "javascript": {"extension": ".js", "prompt_extension": ".prompt"},
}

# 2. Locking Mechanism
class SyncLock:
    def __init__(self, lock_file_path: pathlib.Path):
        self.lock_file_path = lock_file_path
        self._lock_fd: Optional[int] = None
        self._acquired_by_current_lock_instance = False # For re-entrancy of this specific instance
        self.lock_file_path.parent.mkdir(parents=True, exist_ok=True)

    def _is_pid_running(self, pid: int) -> bool:
        if pid == os.getpid(): # Current process is always running
            return True
        if psutil:
            return psutil.pid_exists(pid)
        if platform.system() != "Windows": # POSIX: use os.kill
            try:
                os.kill(pid, 0)
                return True
            except OSError: # ESRCH (No such process), EPERM (No permission, but process exists)
                return False # Simplification: assume ESRCH means not running
        # Fallback: On Windows without psutil, or if os.kill fails due to EPERM,
        # it's hard to be certain. Assume running to be safe (prevents removing active lock).
        # print(f"Warning: Cannot reliably check if PID {pid} is running (psutil not found or OS limitation).", file=sys.stderr)
        return True 

    def acquire(self, timeout: float = 10.0) -> None: # Default timeout 10s
        if self._acquired_by_current_lock_instance: # Re-entrancy for this instance
            return

        current_pid = os.getpid()
        start_time = time.monotonic()

        while True:
            elapsed_time = time.monotonic() - start_time
            if timeout > 0 and elapsed_time >= timeout:
                raise TimeoutError(f"Timeout ({timeout}s) acquiring lock on {self.lock_file_path}.")

            # Check existing lock file
            if self.lock_file_path.exists():
                try:
                    lock_content = self.lock_file_path.read_text()
                    locked_pid = int(lock_content)
                    
                    if not self._is_pid_running(locked_pid):
                        # print(f"Stale lock file {self.lock_file_path} (PID {locked_pid} not running). Removing.")
                        try:
                            self.lock_file_path.unlink()
                        except FileNotFoundError:
                            pass # Race condition: already removed
                        except OSError as e:
                            raise OSError(f"Could not remove stale lock file {self.lock_file_path}: {e}")
                        # Retry acquiring immediately after removing stale lock
                        continue
                    elif locked_pid == current_pid:
                        # Another part of this same process (different SyncLock instance) holds the lock.
                        # This instance cannot acquire the OS lock if already held.
                        # This is not true re-entrancy across SyncLock instances, but expected for file locks.
                        # Fall through to attempt OS lock, which will likely fail (BlockingIOError).
                        pass
                    else: # Lock held by another, running process
                        if timeout == 0: # Non-blocking requested
                            raise TimeoutError(f"Lock {self.lock_file_path} held by active PID {locked_pid}.")
                        # print(f"Lock {self.lock_file_path} held by PID {locked_pid}. Waiting...")
                        time.sleep(min(0.1, timeout - elapsed_time if timeout > 0 else 0.1))
                        continue # Retry check
                except (ValueError, FileNotFoundError): # Malformed or file gone (race)
                    time.sleep(0.05) # Brief pause before retry
                    continue
                except Exception as e:
                    raise RuntimeError(f"Error reading existing lock file {self.lock_file_path}: {e}")
            
            # Attempt to acquire the lock by creating the file and getting an OS lock
            try:
                # Open file descriptor
                self._lock_fd = os.open(str(self.lock_file_path), os.O_CREAT | os.O_RDWR)
                
                # Acquire exclusive, non-blocking OS lock
                if platform.system() == "Windows":
                    msvcrt.locking(self._lock_fd, msvcrt.LK_NBLCK, 1) # Lock 1 byte
                else:
                    fcntl.flock(self._lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                
                # Lock acquired. Write current PID to the lock file.
                os.ftruncate(self._lock_fd, 0) # Clear content if any
                os.lseek(self._lock_fd, 0, os.SEEK_SET) # Rewind
                os.write(self._lock_fd, str(current_pid).encode())
                os.fsync(self._lock_fd) # Ensure PID is written to disk

                self._acquired_by_current_lock_instance = True
                return # Successfully acquired
            
            except (IOError, OSError) as e: # Covers BlockingIOError if lock is held by another process/fd
                if self._lock_fd is not None:
                    os.close(self._lock_fd)
                    self._lock_fd = None
                
                # If lock failed, another process might have just created it. Loop to check.
                if timeout == 0: # Non-blocking requested and failed
                    raise TimeoutError(f"Failed to acquire lock on {self.lock_file_path} (possibly held). Error: {e}")
                time.sleep(min(0.1, timeout - elapsed_time if timeout > 0 else 0.1))
                # Continue loop to re-evaluate or timeout
            except Exception as e: # Catch any other unexpected error during lock acquisition
                if self._lock_fd is not None:
                    os.close(self._lock_fd)
                    self._lock_fd = None
                raise RuntimeError(f"Unexpected error acquiring lock for {self.lock_file_path}: {e}")

    def release(self) -> None:
        if not self._acquired_by_current_lock_instance:
            return
        
        if self._lock_fd is not None:
            # Release OS lock
            if platform.system() == "Windows":
                os.lseek(self._lock_fd, 0, os.SEEK_SET)
                msvcrt.locking(self._lock_fd, msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(self._lock_fd, fcntl.LOCK_UN)
            os.close(self._lock_fd)
            self._lock_fd = None
        
        # Remove the lock file if this process still conceptually owns it
        try:
            if self.lock_file_path.exists():
                # Sanity check: ensure PID in file matches current process before unlinking
                # This helps prevent accidental deletion if state is complex (e.g. manual file edits)
                pid_in_file = int(self.lock_file_path.read_text())
                if pid_in_file == os.getpid():
                    self.lock_file_path.unlink()
                # else:
                    # print(f"Warning: Lock file {self.lock_file_path} PID ({pid_in_file}) differs from current PID ({os.getpid()}) during release. Not unlinking.", file=sys.stderr)
        except FileNotFoundError:
            pass # Already gone
        except (ValueError, OSError) as e: # Error reading PID or unlinking
            # print(f"Error during lock file cleanup for {self.lock_file_path}: {e}", file=sys.stderr)
            pass # Logged, but don't let cleanup failure break everything

        self._acquired_by_current_lock_instance = False

    def __enter__(self):
        self.acquire() # Uses default timeout
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.release()

# 3. State Analysis Functions
def get_language_config(language: str) -> Dict[str, str]:
    config = LANGUAGE_CONFIG.get(language.lower())
    if not config:
        raise ValueError(f"Language '{language}' is not configured. Supported: {list(LANGUAGE_CONFIG.keys())}")
    return config

def get_pdd_file_paths(
    basename: str, 
    language: str,
    prompts_dir: pathlib.Path,
    code_dir: pathlib.Path,
    examples_dir: pathlib.Path,
    tests_dir: pathlib.Path
) -> Dict[str, pathlib.Path]:
    lang_config = get_language_config(language)
    ext = lang_config["extension"]
    prompt_ext = lang_config["prompt_extension"]
    
    return {
        'prompt': prompts_dir.resolve() / f"{basename}_{language}{prompt_ext}",
        'code': code_dir.resolve() / f"{basename}{ext}",
        'example': examples_dir.resolve() / f"{basename}_example{ext}",
        'test': tests_dir.resolve() / f"test_{basename}{ext}",
    }

def calculate_sha256(file_path: pathlib.Path) -> Optional[str]:
    if not file_path.is_file(): # Checks existence and if it's a file
        return None
    sha256_hash = hashlib.sha256()
    try:
        with open(file_path, "rb") as f:
            for byte_block in iter(lambda: f.read(8192), b""): # Read in 8KB chunks
                sha256_hash.update(byte_block)
        return sha256_hash.hexdigest()
    except IOError:
        # print(f"Warning: Could not calculate SHA256 for {file_path} due to IOError.", file=sys.stderr)
        return None

def _read_json_file_as_dict(file_path: pathlib.Path) -> Optional[Dict[str, Any]]:
    if not file_path.is_file():
        return None
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except (json.JSONDecodeError, IOError):
        # print(f"Warning: Could not read or parse JSON from {file_path}.", file=sys.stderr)
        return None

def read_fingerprint(basename: str, language: str, pdd_meta_dir: pathlib.Path) -> Optional[Fingerprint]:
    fp_path = pdd_meta_dir / f"{basename}_{language}.json"
    data = _read_json_file_as_dict(fp_path)
    if data:
        try:
            # Ensure all optional fields exist for dataclass construction
            for field_name in Fingerprint.__annotations__:
                 if field_name not in data and isinstance(Fingerprint.__annotations__[field_name], type(Optional[str])):
                      data[field_name] = None # Add missing optional fields as None
            return Fingerprint(**data)
        except TypeError as e: # Mismatch between data and Fingerprint fields
            # print(f"Warning: Invalid data in fingerprint file {fp_path}. Error: {e}", file=sys.stderr)
            return None
    return None

def read_run_report(basename: str, language: str, pdd_meta_dir: pathlib.Path) -> Optional[RunReport]:
    report_path = pdd_meta_dir / f"{basename}_{language}_run.json"
    data = _read_json_file_as_dict(report_path)
    if data:
        try:
            return RunReport(**data)
        except TypeError as e: # Mismatch between data and RunReport fields
            # print(f"Warning: Invalid data in run report file {report_path}. Error: {e}", file=sys.stderr)
            return None
    return None

def calculate_current_hashes(paths: Dict[str, pathlib.Path]) -> Dict[str, Optional[str]]:
    current_hashes = {}
    for file_type_key, path_obj in paths.items(): # file_type_key is 'prompt', 'code', etc.
        current_hashes[file_type_key + '_hash'] = calculate_sha256(path_obj)
    return current_hashes

def get_git_repo_root(start_path: pathlib.Path) -> Optional[pathlib.Path]:
    """Finds the root of the git repository containing start_path."""
    try:
        result = subprocess.run(
            ['git', 'rev-parse', '--show-toplevel'],
            cwd=start_path,
            capture_output=True, text=True, check=True, encoding='utf-8'
        )
        return pathlib.Path(result.stdout.strip())
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None # Not in a git repo or git not found

def get_git_diff(file_path: pathlib.Path, project_root_dir: pathlib.Path) -> str:
    """Generates a diff for file_path against its HEAD version within the git repo."""
    git_root = get_git_repo_root(project_root_dir)
    if not git_root:
        return "Error: Not a git repository or git command not found."

    abs_file_path = file_path.resolve()
    try:
        relative_file_path_str = str(abs_file_path.relative_to(git_root))
    except ValueError:
        return f"Error: File {abs_file_path} is not within the git repository {git_root}."

    try:
        # Check if file existed in HEAD (for correct diff of deleted files)
        is_in_head = False
        try:
            subprocess.run(
                ['git', 'cat-file', '-e', f'HEAD:{relative_file_path_str}'],
                cwd=git_root, check=True, capture_output=True
            )
            is_in_head = True
        except subprocess.CalledProcessError:
            pass # Not in HEAD or other error

        if not abs_file_path.exists() and not is_in_head:
            return "(file does not exist locally and was not in HEAD)"
        
        # Use 'git diff' which handles various cases (modified, new, deleted)
        # `git diff HEAD -- path` compares working tree `path` with `HEAD:path`.
        # If `path` is new, it's compared to an empty state in HEAD.
        # If `path` is deleted, it shows deletion from HEAD.
        result = subprocess.run(
            ['git', 'diff', 'HEAD', '--', relative_file_path_str],
            cwd=git_root, capture_output=True, text=True, encoding='utf-8',
            # `check=False` because `git diff` returns 1 if there are differences.
        )
        # `git diff` exit codes: 0 = no changes, 1 = changes found. >1 = error.
        if result.returncode > 1:
            # Fallback for untracked files if `git diff HEAD` failed or didn't show them
            status_res = subprocess.run(
                ['git', 'status', '--porcelain', '--', relative_file_path_str],
                cwd=git_root, capture_output=True, text=True, check=True, encoding='utf-8'
            )
            if status_res.stdout.strip().startswith("??"): # Untracked file
                # Create a diff as if it's a new file added from /dev/null
                file_content = abs_file_path.read_text(encoding='utf-8')
                return f"--- a/{relative_file_path_str}\n+++ b/{relative_file_path_str}\n@@ -0,0 +1,{len(file_content.splitlines())} @@\n+{'+'.join(file_content.splitlines(True))}"

            return f"Error generating diff for {relative_file_path_str} (git diff exit code {result.returncode}): {result.stderr or result.stdout}"
        return result.stdout
    except subprocess.CalledProcessError as e: # For git status or cat-file
        return f"Git command error for {relative_file_path_str}: {e.stderr or e.stdout}"
    except FileNotFoundError:
        return "Error: git command not found. Cannot generate diffs."
    except Exception as e:
        return f"Unexpected error generating diff for {relative_file_path_str}: {str(e)}"


# 4. The Main `determine_sync_operation` Function
def determine_sync_operation(
    basename: str, 
    language: str, 
    target_coverage: float,
    prompts_dir: pathlib.Path,
    code_dir: pathlib.Path,
    examples_dir: pathlib.Path,
    tests_dir: pathlib.Path,
    pdd_working_dir: pathlib.Path, 
    project_root_dir: pathlib.Path,
    skip_tests: bool = False,
    skip_verify: bool = False
) -> SyncDecision:

    pdd_locks_dir = pdd_working_dir.resolve() / "locks"
    pdd_meta_dir = pdd_working_dir.resolve() / "meta"
    
    pdd_locks_dir.mkdir(parents=True, exist_ok=True)
    pdd_meta_dir.mkdir(parents=True, exist_ok=True)

    lock_file_path = pdd_locks_dir / f"{basename}_{language}.lock"
    
    file_paths = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)

    with SyncLock(lock_file_path):
        # 1. Check Runtime Signals First (from last run report)
        run_report = read_run_report(basename, language, pdd_meta_dir)
        if run_report:
            if run_report.exit_code != 0:
                return SyncDecision(
                    operation='crash',
                    reason=f"Last run ended with non-zero exit code ({run_report.exit_code}). Investigation needed.",
                    details={'run_report': dataclasses.asdict(run_report)}
                )
            if not skip_tests: # Only consider test-related signals if not skipping tests
                if run_report.tests_failed > 0:
                    return SyncDecision(
                        operation='fix',
                        reason=f"{run_report.tests_failed} test(s) failed in the last run. Needs fixing.",
                        details={'run_report': dataclasses.asdict(run_report)}
                    )
                if run_report.coverage < target_coverage:
                    return SyncDecision(
                        operation='test',
                        reason=f"Current test coverage ({run_report.coverage:.2%}) is below target ({target_coverage:.2%}). More tests needed.",
                        details={'run_report': dataclasses.asdict(run_report)}
                    )
        
        # 2. Analyze File State against Fingerprint
        fingerprint = read_fingerprint(basename, language, pdd_meta_dir)
        current_hashes = calculate_current_hashes(file_paths)

        # 3. Decision Tree based on Fingerprint and Hashes
        if not fingerprint: # No fingerprint exists
            if current_hashes['prompt_hash']: # Prompt file exists
                return SyncDecision(
                    operation='generate',
                    reason="No PDD fingerprint found, but a prompt file exists. Initial generation is recommended."
                )
            else: # No fingerprint and no prompt file
                return SyncDecision(
                    operation='nothing', 
                    reason="No PDD fingerprint or prompt file found. Please create a prompt file to begin."
                )

        # Fingerprint exists, compare hashes
        changed_map = {
            'prompt': current_hashes['prompt_hash'] != fingerprint.prompt_hash,
            'code': current_hashes['code_hash'] != fingerprint.code_hash,
            'example': current_hashes['example_hash'] != fingerprint.example_hash,
            'test': current_hashes['test_hash'] != fingerprint.test_hash,
        }
        
        changed_file_types = [ftype for ftype, changed in changed_map.items() if changed]
        num_changes = len(changed_file_types)

        if num_changes == 0: # All hashes match fingerprint
            return SyncDecision(
                operation='nothing',
                reason="All files match the last known PDD fingerprint. System is synchronized."
            )

        if num_changes == 1: # Single file changed
            changed_type = changed_file_types[0]
            if changed_type == 'prompt':
                # Special handling if prompt was deleted
                if not current_hashes['prompt_hash'] and fingerprint.prompt_hash:
                    return SyncDecision(
                        operation='analyze_conflict', # Deleting a tracked prompt is a conflict
                        reason="Prompt file was deleted while being tracked by PDD fingerprint.",
                        details={'changed_files': ['prompt'], 'fingerprint': dataclasses.asdict(fingerprint), 'change_details': 'prompt_deleted'}
                    )
                return SyncDecision(operation='generate', reason="Prompt file has changed since last PDD fingerprint.")
            
            elif changed_type == 'code':
                return SyncDecision(operation='update', reason="Code file has changed since last PDD fingerprint.")
            
            elif changed_type == 'test':
                if skip_tests:
                    return SyncDecision(
                        operation='nothing',
                        reason="Test file has changed, but tests are currently skipped by user preference.",
                        details={'suppressed_operation': 'test', 'changed_files': ['test']}
                    )
                return SyncDecision(operation='test', reason="Test file has changed. Running tests is recommended.")
            
            elif changed_type == 'example':
                if skip_verify:
                     return SyncDecision(
                        operation='nothing',
                        reason="Example file has changed, but verification is currently skipped by user preference.",
                        details={'suppressed_operation': 'verify', 'changed_files': ['example']}
                    )
                return SyncDecision(operation='verify', reason="Example file has changed. Verification is recommended.")
        
        # Multiple files changed: This is a complex conflict
        if num_changes > 1:
            return SyncDecision(
                operation='analyze_conflict',
                reason=f"Multiple PDD files ({', '.join(changed_file_types)}) have changed since the last fingerprint.",
                details={'changed_files': changed_file_types, 'fingerprint': dataclasses.asdict(fingerprint)}
            )
        
        # Fallback, should ideally not be reached if logic is exhaustive
        return SyncDecision(
            operation='nothing',
            reason="An unexpected state was encountered during sync analysis. No clear operation determined.",
            confidence=0.0, 
            details={'current_hashes': current_hashes, 'fingerprint': dataclasses.asdict(fingerprint) if fingerprint else None, 'num_changes': num_changes}
        )

# 5. LLM-based Conflict Analysis Function
def analyze_conflict_with_llm(
    basename: str, 
    language: str, 
    fingerprint_data: Dict[str, Any], # Passed as a dict from SyncDecision.details
    changed_files: List[str], # List of file types that changed, e.g., ['prompt', 'code']
    file_paths: Dict[str, pathlib.Path], # Paths to all relevant PDD files
    pdd_working_dir: pathlib.Path,
    project_root_dir: pathlib.Path
) -> SyncDecision:

    pdd_locks_dir = pdd_working_dir.resolve() / "locks"
    lock_file_path = pdd_locks_dir / f"{basename}_{language}.lock"

    with SyncLock(lock_file_path): # Ensure exclusive operation during LLM analysis
        # 1. Load LLM Prompt Template
        prompt_template_str = load_prompt_template("sync_analysis_LLM.prompt")
        if not prompt_template_str:
            return SyncDecision(
                operation='fail_and_request_manual_merge', 
                reason="Critical error: LLM prompt template 'sync_analysis_LLM.prompt' could not be loaded.",
                confidence=0.0
            )

        # 2. Gather Diffs for Changed Files
        diffs_for_prompt = {}
        for ftype_key in ['prompt', 'code', 'example', 'test']: # Iterate all possible file types
            path_to_diff = file_paths.get(ftype_key)
            if path_to_diff:
                 # Only generate diffs for files reported as changed, or if file exists for context
                if ftype_key in changed_files or path_to_diff.exists():
                    diffs_for_prompt[f"{ftype_key}_diff"] = get_git_diff(path_to_diff, project_root_dir)
                else:
                    diffs_for_prompt[f"{ftype_key}_diff"] = "(file does not exist and was not reported as changed)"
            else: # Should not happen if file_paths is correctly populated
                diffs_for_prompt[f"{ftype_key}_diff"] = "(file path not provided)"
        
        # 3. Format the Prompt for LLM
        prompt_context = {
            "fingerprint": json.dumps(fingerprint_data, indent=2),
            "changed_files_list": ", ".join(changed_files) if changed_files else "None reported",
            **diffs_for_prompt
        }
        
        try:
            full_llm_prompt = prompt_template_str.format(**prompt_context)
        except KeyError as e:
             return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason=f"Error formatting LLM prompt template. Missing placeholder: {e}. Check template and context.",
                confidence=0.0
            )

        # 4. Invoke LLM
        try:
            # LLM invocation should ideally be deterministic (e.g., cached) for reliable sync logic
            llm_response_package = llm_invoke(
                prompt=full_llm_prompt,
                temperature=0.1, # Low temperature for more deterministic/factual JSON output
                strength=0.8 # Example strength, tune as needed
            )
            llm_json_result_str = llm_response_package.get('result')
            if not isinstance(llm_json_result_str, str):
                raise ValueError("LLM response 'result' field is not a string as expected for JSON output.")

        except Exception as e: # Catch broad exceptions from llm_invoke
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason=f"LLM invocation failed: {str(e)}",
                confidence=0.0,
                details={"llm_error_details": str(e)}
            )

        # 5. Parse LLM's JSON Response
        try:
            llm_parsed_output = json.loads(llm_json_result_str)
            if not isinstance(llm_parsed_output, dict):
                raise ValueError("LLM JSON response did not parse into a dictionary.")
        except json.JSONDecodeError as e:
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason=f"Failed to parse LLM's JSON response: {e}. Raw response (first 500 chars): '{llm_json_result_str[:500]}...'",
                confidence=0.0,
                details={"llm_raw_response": llm_json_result_str}
            )
        except ValueError as e: # For the isinstance check
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason=str(e), # Contains "LLM JSON response did not parse into a dictionary."
                confidence=0.0,
                details={"llm_raw_response": llm_json_result_str}
            )

        # 6. Validate LLM Response and Return SyncDecision
        op = llm_parsed_output.get('next_operation')
        rsn = llm_parsed_output.get('reason')
        conf = llm_parsed_output.get('confidence', 0.5) # Default confidence if LLM doesn't provide it

        if not (op and rsn and isinstance(op, str) and isinstance(rsn, str) and isinstance(conf, (float, int))):
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason="LLM response JSON is missing required fields ('next_operation', 'reason') or fields have invalid types.",
                confidence=0.0,
                details={"llm_parsed_response": llm_parsed_output}
            )
        
        # Apply safety threshold for LLM confidence
        MIN_LLM_CONFIDENCE_THRESHOLD = 0.75 
        if float(conf) < MIN_LLM_CONFIDENCE_THRESHOLD:
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason=f"LLM confidence ({conf:.2f}) is below threshold ({MIN_LLM_CONFIDENCE_THRESHOLD:.2f}). Manual review advised. LLM's original reason: {rsn}",
                confidence=float(conf), # Report the LLM's actual confidence
                details={"llm_parsed_response": llm_parsed_output, "original_llm_reason": rsn}
            )

        return SyncDecision(
            operation=op,
            reason=rsn,
            confidence=float(conf),
            details={"llm_analysis_data": llm_parsed_output}
        )

# Example Usage (illustrative, adjust paths as needed for actual testing)
if __name__ == "__main__":
    # Setup a mock project structure for testing
    # Create a temporary directory for the mock project
    import tempfile
    import shutil
    temp_dir_obj = tempfile.TemporaryDirectory()
    mock_project_root = pathlib.Path(temp_dir_obj.name)
    
    print(f"Mock project root: {mock_project_root}")

    prompts_d = mock_project_root / "prompts"
    src_d = mock_project_root / "src"
    examples_d = mock_project_root / "examples"
    tests_d = mock_project_root / "tests"
    pdd_work_d = mock_project_root / ".pdd" # Main .pdd directory

    for d_path in [prompts_d, src_d, examples_d, tests_d, pdd_work_d]:
        d_path.mkdir(parents=True, exist_ok=True)
    
    # Initialize git repo for diff testing
    if not (mock_project_root / ".git").exists():
        try:
            subprocess.run(["git", "init"], cwd=mock_project_root, check=True, capture_output=True)
            subprocess.run(["git", "config", "user.name", "Test User"], cwd=mock_project_root, check=True, capture_output=True)
            subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=mock_project_root, check=True, capture_output=True)
            # Initial commit to make HEAD exist
            (mock_project_root / ".gitkeep").touch()
            subprocess.run(["git", "add", ".gitkeep"], cwd=mock_project_root, check=True, capture_output=True)
            subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=mock_project_root, check=True, capture_output=True)

        except (subprocess.CalledProcessError, FileNotFoundError) as e_git:
            print(f"Warning: Could not initialize git repo in mock_pdd_project: {e_git}. Git-dependent tests might behave differently.", file=sys.stderr)

    bn_main = "calculator"
    lang_main = "python"
    
    # Common parameters for determine_sync_operation
    common_params = {
        "basename": bn_main, "language": lang_main, "target_coverage": 0.80,
        "prompts_dir": prompts_d, "code_dir": src_d, 
        "examples_dir": examples_d, "tests_dir": tests_d,
        "pdd_working_dir": pdd_work_d, "project_root_dir": mock_project_root
    }

    print("\n--- Test Case 1: New unit, no prompt, no fingerprint ---")
    decision1 = determine_sync_operation(**common_params)
    print(f"Decision: {decision1.operation}, Reason: {decision1.reason}")
    assert decision1.operation == 'nothing' 
    assert "create a prompt file" in decision1.reason.lower()

    print("\n--- Test Case 2: New unit, prompt exists, no fingerprint ---")
    prompt_f = get_pdd_file_paths(**common_params)['prompt']
    prompt_f.write_text("Design a simple calculator.")
    decision2 = determine_sync_operation(**common_params)
    print(f"Decision: {decision2.operation}, Reason: {decision2.reason}")
    assert decision2.operation == 'generate'
    prompt_f.unlink() # Clean up

    print("\n--- Test Case 3: Failing run report (exit code != 0) ---")
    meta_dir = pdd_work_d / "meta"
    meta_dir.mkdir(parents=True, exist_ok=True) # Ensure meta dir exists
    run_report_f = meta_dir / f"{bn_main}_{lang_main}_run.json"
    failing_rep_data = RunReport(timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(), exit_code=1, tests_passed=0, tests_failed=0, coverage=0.0)
    with open(run_report_f, 'w') as f_out:
        json.dump(dataclasses.asdict(failing_rep_data), f_out)
    
    decision3 = determine_sync_operation(**common_params)
    print(f"Decision: {decision3.operation}, Reason: {decision3.reason}")
    assert decision3.operation == 'crash'
    run_report_f.unlink()

    print("\n--- Test Case 4: Files match fingerprint (nothing to do) ---")
    prompt_f.write_text("Initial prompt content.")
    code_f = get_pdd_file_paths(**common_params)['code']
    code_f.write_text("Initial code content.")
    
    # Commit these files to HEAD for stable diff base
    try:
        subprocess.run(["git", "add", str(prompt_f.relative_to(mock_project_root)), str(code_f.relative_to(mock_project_root))], cwd=mock_project_root, check=True, capture_output=True)
        subprocess.run(["git", "commit", "-m", "Add calculator files for test 4"], cwd=mock_project_root, check=True, capture_output=True)
    except Exception as e_git_commit:
        print(f"Git commit failed for test 4: {e_git_commit}")


    fp_obj = Fingerprint(
        pdd_version=PDD_VERSION, timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(), command="generate",
        prompt_hash=calculate_sha256(prompt_f),
        code_hash=calculate_sha256(code_f),
        example_hash=None, test_hash=None
    )
    fingerprint_f = meta_dir / f"{bn_main}_{lang_main}.json"
    with open(fingerprint_f, 'w') as f_out:
        json.dump(dataclasses.asdict(fp_obj), f_out)

    decision4 = determine_sync_operation(**common_params)
    print(f"Decision: {decision4.operation}, Reason: {decision4.reason}")
    assert decision4.operation == 'nothing'

    print("\n--- Test Case 5: Prompt changed (simple change) ---")
    prompt_f.write_text("Updated prompt content.") # Modify prompt
    decision5 = determine_sync_operation(**common_params)
    print(f"Decision: {decision5.operation}, Reason: {decision5.reason}")
    assert decision5.operation == 'generate'
    
    # Update fingerprint to reflect "Updated prompt content" for next test
    fp_obj.prompt_hash = calculate_sha256(prompt_f)
    with open(fingerprint_f, 'w') as f_out:
        json.dump(dataclasses.asdict(fp_obj), f_out)


    print("\n--- Test Case 6: Multiple files changed (prompt and code) -> analyze_conflict ---")
    prompt_f.write_text("Prompt changed again for conflict test.")
    code_f.write_text("Code content also changed for conflict test.")
    
    decision6 = determine_sync_operation(**common_params)
    print(f"Decision: {decision6.operation}, Reason: {decision6.reason}")
    assert decision6.operation == 'analyze_conflict'
    
    if decision6.operation == 'analyze_conflict':
        print("\n--- Test Case 7: LLM analysis for conflict ---")
        changed_files_list_conflict = decision6.details['changed_files']
        fp_dict_conflict = decision6.details['fingerprint']
        
        current_file_paths_conflict = get_pdd_file_paths(**common_params)

        llm_decision = analyze_conflict_with_llm(
            basename=bn_main, language=lang_main,
            fingerprint_data=fp_dict_conflict,
            changed_files=changed_files_list_conflict,
            file_paths=current_file_paths_conflict,
            pdd_working_dir=pdd_work_d,
            project_root_dir=mock_project_root
        )
        print(f"LLM Decision: {llm_decision.operation}, Reason: {llm_decision.reason}, Confidence: {llm_decision.confidence:.2f}")
        assert llm_decision.operation is not None # Check LLM gave some operation

    # Clean up files created for tests
    prompt_f.unlink(missing_ok=True)
    code_f.unlink(missing_ok=True)
    fingerprint_f.unlink(missing_ok=True)
    
    print("\nAll illustrative tests completed.")
    
    # Clean up the temporary directory
    try:
        temp_dir_obj.cleanup()
        print(f"Cleaned up temporary directory: {mock_project_root}")
    except Exception as e_cleanup:
        print(f"Error cleaning up temporary directory {mock_project_root}: {e_cleanup}", file=sys.stderr)
