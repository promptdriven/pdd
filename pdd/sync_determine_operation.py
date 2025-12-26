"""
sync_determine_operation.py
~~~~~~~~~~~~~~~~~~~~~~~~~

Core decision-making logic for the `pdd sync` command.
Implements fingerprint-based state analysis and deterministic operation selection.
"""

import os
import sys
import json
import hashlib
import subprocess
from pathlib import Path
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any
from datetime import datetime
import psutil

# Platform-specific imports for file locking
try:
    import fcntl
    HAS_FCNTL = True
except ImportError:
    HAS_FCNTL = False

try:
    import msvcrt
    HAS_MSVCRT = True
except ImportError:
    HAS_MSVCRT = False

# Import PDD internal modules
from pdd.construct_paths import construct_paths
from pdd.load_prompt_template import load_prompt_template
from pdd.llm_invoke import llm_invoke
from pdd.get_language import get_language

# Constants - Use functions for dynamic path resolution
def get_pdd_dir():
    """Get the .pdd directory relative to current working directory."""
    return Path.cwd() / '.pdd'

def get_meta_dir():
    """Get the metadata directory."""
    return get_pdd_dir() / 'meta'

def get_locks_dir():
    """Get the locks directory."""
    return get_pdd_dir() / 'locks'

# For backward compatibility
PDD_DIR = get_pdd_dir()
META_DIR = get_meta_dir()
LOCKS_DIR = get_locks_dir()

# Export constants for other modules
__all__ = ['PDD_DIR', 'META_DIR', 'LOCKS_DIR', 'Fingerprint', 'RunReport', 'SyncDecision',
           'sync_determine_operation', 'analyze_conflict_with_llm', 'read_run_report', 'get_pdd_file_paths',
           '_check_example_success_history']


def _safe_basename(basename: str) -> str:
    """Sanitize basename for use in metadata filenames.

    Replaces '/' with '_' to prevent path interpretation when the basename
    contains subdirectory components (e.g., 'core/cloud' -> 'core_cloud').
    """
    return basename.replace('/', '_')


def _extract_name_part(basename: str) -> tuple:
    """Extract directory and name parts from a subdirectory basename.

    For subdirectory basenames like 'core/cloud', separates the directory
    prefix from the actual name so that filename patterns can be applied
    correctly.

    Args:
        basename: The full basename, possibly containing subdirectory path.

    Returns:
        Tuple of (dir_prefix, name_part):
        - 'core/cloud' -> ('core/', 'cloud')
        - 'calculator' -> ('', 'calculator')
    """
    if '/' in basename:
        dir_part, name_part = basename.rsplit('/', 1)
        return dir_part + '/', name_part
    return '', basename


@dataclass
class Fingerprint:
    """Represents the last known good state of a PDD unit."""
    pdd_version: str
    timestamp: str  # ISO 8601 format
    command: str    # e.g., "generate", "fix"
    prompt_hash: Optional[str]
    code_hash: Optional[str]
    example_hash: Optional[str]
    test_hash: Optional[str]  # Keep for backward compat (primary test file)
    test_files: Optional[Dict[str, str]] = None  # Bug #156: {"test_foo.py": "hash1", ...}


@dataclass
class RunReport:
    """Represents the results from the last test run."""
    timestamp: str
    exit_code: int
    tests_passed: int
    tests_failed: int
    coverage: float
    test_hash: Optional[str] = None  # Hash of test file when tests were run (for staleness detection)
    test_files: Optional[Dict[str, str]] = None  # Bug #156: {"test_foo.py": "hash1", ...}


@dataclass
class SyncDecision:
    """Represents a decision about what PDD operation to run next."""
    operation: str  # 'auto-deps', 'generate', 'example', 'crash', 'verify', 'test', 'fix', 'update', 'analyze_conflict', 'nothing', 'all_synced', 'error', 'fail_and_request_manual_merge'
    reason: str  # A human-readable explanation for the decision
    confidence: float = 1.0  # Confidence level in the decision, 0.0 to 1.0, default 1.0 for deterministic decisions
    estimated_cost: float = 0.0  # Estimated cost for the operation in dollars, default 0.0
    details: Optional[Dict[str, Any]] = None  # Extra context for logging and debugging, default None
    prerequisites: Optional[List[str]] = None  # List of operations that should be completed first, default None


class SyncLock:
    """Context manager for handling file-descriptor based locking."""
    
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.lock_file = get_locks_dir() / f"{_safe_basename(basename)}_{language}.lock"
        self.fd = None
        self.current_pid = os.getpid()
    
    def __enter__(self):
        self.acquire()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        self.release()
    
    def acquire(self):
        """Acquire the lock, handling stale locks and re-entrancy."""
        # Ensure lock directory exists
        self.lock_file.parent.mkdir(parents=True, exist_ok=True)
        
        try:
            # Check if lock file exists
            if self.lock_file.exists():
                try:
                    # Read PID from lock file
                    stored_pid = int(self.lock_file.read_text().strip())
                    
                    # Check if this is the same process (re-entrancy)
                    if stored_pid == self.current_pid:
                        return
                    
                    # Check if the process is still running
                    if psutil.pid_exists(stored_pid):
                        raise TimeoutError(f"Lock held by running process {stored_pid}")
                    
                    # Stale lock - remove it
                    self.lock_file.unlink(missing_ok=True)
                    
                except (ValueError, FileNotFoundError):
                    # Invalid lock file - remove it
                    self.lock_file.unlink(missing_ok=True)
            
            # Create lock file and acquire file descriptor lock
            self.lock_file.touch()
            self.fd = open(self.lock_file, 'w')
            
            if HAS_FCNTL:
                # POSIX systems
                fcntl.flock(self.fd.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            elif HAS_MSVCRT:
                # Windows systems
                msvcrt.locking(self.fd.fileno(), msvcrt.LK_NBLCK, 1)
            
            # Write current PID to lock file
            self.fd.write(str(self.current_pid))
            self.fd.flush()
            
        except (IOError, OSError) as e:
            if self.fd:
                self.fd.close()
                self.fd = None
            raise TimeoutError(f"Failed to acquire lock: {e}")
    
    def release(self):
        """Release the lock and clean up."""
        if self.fd:
            try:
                if HAS_FCNTL:
                    fcntl.flock(self.fd.fileno(), fcntl.LOCK_UN)
                elif HAS_MSVCRT:
                    msvcrt.locking(self.fd.fileno(), msvcrt.LK_UNLCK, 1)
                
                self.fd.close()
                self.fd = None
                
                # Remove lock file
                self.lock_file.unlink(missing_ok=True)
                
            except (IOError, OSError):
                # Best effort cleanup
                pass


def get_extension(language: str) -> str:
    """Get file extension for a programming language."""
    extensions = {
        'python': 'py',
        'javascript': 'js', 
        'typescript': 'ts',
        'java': 'java',
        'cpp': 'cpp',
        'c': 'c',
        'ruby': 'rb',
        'go': 'go',
        'rust': 'rs',
        'php': 'php',
        'swift': 'swift',
        'kotlin': 'kt',
        'scala': 'scala',
        'csharp': 'cs',
        'css': 'css',
        'html': 'html',
        'sql': 'sql',
        'shell': 'sh',
        'bash': 'sh',
        'powershell': 'ps1',
        'r': 'r',
        'matlab': 'm',
        'lua': 'lua',
        'perl': 'pl',
    }
    return extensions.get(language.lower(), language.lower())


def get_pdd_file_paths(basename: str, language: str, prompts_dir: str = "prompts", context_override: Optional[str] = None) -> Dict[str, Path]:
    """Returns a dictionary mapping file types to their expected Path objects."""
    import logging
    logger = logging.getLogger(__name__)
    logger.info(f"get_pdd_file_paths called: basename={basename}, language={language}, prompts_dir={prompts_dir}")
    
    try:
        # Use construct_paths to get configuration-aware paths
        prompt_filename = f"{basename}_{language}.prompt"
        prompt_path = str(Path(prompts_dir) / prompt_filename)
        logger.info(f"Checking prompt_path={prompt_path}, exists={Path(prompt_path).exists()}")
        
        # Check if prompt file exists - if not, we still need configuration-aware paths
        if not Path(prompt_path).exists():
            # Use construct_paths with minimal inputs to get configuration-aware paths
            # even when prompt doesn't exist
            extension = get_extension(language)
            try:
                # Call construct_paths with empty input_file_paths to get configured output paths
                resolved_config, _, output_paths, _ = construct_paths(
                    input_file_paths={},  # Empty dict since files don't exist yet
                    force=True,
                    quiet=True,
                    command="sync",
                    command_options={"basename": basename, "language": language},
                    context_override=context_override
                )
                
                import logging
                logger = logging.getLogger(__name__)
                logger.info(f"resolved_config: {resolved_config}")
                logger.info(f"output_paths: {output_paths}")
                
                # Extract directory configuration from resolved_config
                # Note: construct_paths sets tests_dir, examples_dir, code_dir keys
                test_dir = resolved_config.get('tests_dir', 'tests/')
                example_dir = resolved_config.get('examples_dir', 'examples/')
                code_dir = resolved_config.get('code_dir', './')
                
                logger.info(f"Extracted dirs - test: {test_dir}, example: {example_dir}, code: {code_dir}")
                
                # Ensure directories end with /
                if test_dir and not test_dir.endswith('/'):
                    test_dir = test_dir + '/'
                if example_dir and not example_dir.endswith('/'):
                    example_dir = example_dir + '/'
                if code_dir and not code_dir.endswith('/'):
                    code_dir = code_dir + '/'
                
                # Extract directory and name parts for subdirectory basename support
                dir_prefix, name_part = _extract_name_part(basename)

                # Construct the full paths (preserving subdirectory structure)
                test_path = f"{test_dir}{dir_prefix}test_{name_part}.{extension}"
                example_path = f"{example_dir}{dir_prefix}{name_part}_example.{extension}"
                code_path = f"{code_dir}{dir_prefix}{name_part}.{extension}"

                logger.debug(f"Final paths: test={test_path}, example={example_path}, code={code_path}")

                # Convert to Path objects
                test_path = Path(test_path)
                example_path = Path(example_path)
                code_path = Path(code_path)

                # Bug #156: Find all matching test files
                test_dir_path = test_path.parent
                test_stem = f"test_{name_part}"
                if test_dir_path.exists():
                    matching_test_files = sorted(test_dir_path.glob(f"{test_stem}*.{extension}"))
                else:
                    matching_test_files = [test_path] if test_path.exists() else []

                result = {
                    'prompt': Path(prompt_path),
                    'code': code_path,
                    'example': example_path,
                    'test': test_path,
                    'test_files': matching_test_files or [test_path]  # Bug #156
                }
                logger.debug(f"get_pdd_file_paths returning (prompt missing): test={test_path}")
                return result
            except Exception as e:
                # If construct_paths fails, fall back to current directory paths
                # This maintains backward compatibility
                import logging
                logger = logging.getLogger(__name__)
                logger.debug(f"construct_paths failed for non-existent prompt, using defaults: {e}")
                dir_prefix, name_part = _extract_name_part(basename)
                fallback_test_path = Path(f"{dir_prefix}test_{name_part}.{extension}")
                # Bug #156: Find matching test files even in fallback
                if Path('.').exists():
                    fallback_matching = sorted(Path('.').glob(f"{dir_prefix}test_{name_part}*.{extension}"))
                else:
                    fallback_matching = [fallback_test_path] if fallback_test_path.exists() else []
                return {
                    'prompt': Path(prompt_path),
                    'code': Path(f"{dir_prefix}{name_part}.{extension}"),
                    'example': Path(f"{dir_prefix}{name_part}_example.{extension}"),
                    'test': fallback_test_path,
                    'test_files': fallback_matching or [fallback_test_path]  # Bug #156
                }
        
        input_file_paths = {
            "prompt_file": prompt_path
        }
        
        # Call construct_paths to get configuration-aware paths
        resolved_config, input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_file_paths,
            force=True,  # Use force=True to avoid interactive prompts during sync
            quiet=True,
            command="sync",  # Use sync command to get more tolerant path handling
            command_options={"basename": basename, "language": language},
            context_override=context_override
        )
        
        # For sync command, output_file_paths contains the configured paths
        # Extract the code path from output_file_paths
        code_path = output_file_paths.get('generate_output_path', '')
        if not code_path:
            # Try other possible keys
            code_path = output_file_paths.get('output', output_file_paths.get('code_file', ''))
        if not code_path:
            # Fallback to constructing from basename with configuration
            extension = get_extension(language)
            code_dir = resolved_config.get('generate_output_path', './')
            if code_dir and not code_dir.endswith('/'):
                code_dir = code_dir + '/'
            dir_prefix, name_part = _extract_name_part(basename)
            code_path = f"{code_dir}{dir_prefix}{name_part}.{extension}"
        
        # Get configured paths for example and test files using construct_paths
        # Note: construct_paths requires files to exist, so we need to handle the case
        # where code file doesn't exist yet (during initial sync startup)
        try:
            # Create a temporary empty code file if it doesn't exist for path resolution
            code_path_obj = Path(code_path)
            temp_code_created = False
            if not code_path_obj.exists():
                code_path_obj.parent.mkdir(parents=True, exist_ok=True)
                code_path_obj.touch()
                temp_code_created = True
            
            try:
                # Get example path using example command
                # Pass path_resolution_mode="cwd" so paths resolve relative to CWD (not project root)
                # Pass basename in command_options to preserve subdirectory structure
                _, _, example_output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path, "code_file": code_path},
                    force=True, quiet=True, command="example",
                    command_options={"basename": basename},
                    context_override=context_override,
                    path_resolution_mode="cwd"
                )
                dir_prefix, name_part = _extract_name_part(basename)
                example_path = Path(example_output_paths.get('output', f"{dir_prefix}{name_part}_example.{get_extension(language)}"))

                # Get test path using test command - handle case where test file doesn't exist yet
                # Pass basename in command_options to preserve subdirectory structure
                try:
                    _, _, test_output_paths, _ = construct_paths(
                        input_file_paths={"prompt_file": prompt_path, "code_file": code_path},
                        force=True, quiet=True, command="test",
                        command_options={"basename": basename},
                        context_override=context_override,
                        path_resolution_mode="cwd"
                    )
                    test_path = Path(test_output_paths.get('output', f"{dir_prefix}test_{name_part}.{get_extension(language)}"))
                except FileNotFoundError:
                    # Test file doesn't exist yet - create default path
                    test_path = Path(f"{dir_prefix}test_{name_part}.{get_extension(language)}")
                
            finally:
                # Clean up temporary file if we created it
                if temp_code_created and code_path_obj.exists() and code_path_obj.stat().st_size == 0:
                    code_path_obj.unlink()
            
        except Exception as e:
            # Log the specific exception that's causing fallback to wrong paths
            import logging
            logger = logging.getLogger(__name__)
            logger.warning(f"construct_paths failed in get_pdd_file_paths: {type(e).__name__}: {e}")
            logger.warning(f"Falling back to .pddrc-aware path construction")
            logger.warning(f"prompt_path: {prompt_path}, code_path: {code_path}")
            
            # Improved fallback: try to use construct_paths with just prompt_file to get proper directory configs
            try:
                # Get configured directories by using construct_paths with just the prompt file
                # Pass path_resolution_mode="cwd" so paths resolve relative to CWD (not project root)
                # Pass basename in command_options to preserve subdirectory structure
                _, _, example_output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path},
                    force=True, quiet=True, command="example",
                    command_options={"basename": basename},
                    context_override=context_override,
                    path_resolution_mode="cwd"
                )
                dir_prefix, name_part = _extract_name_part(basename)
                example_path = Path(example_output_paths.get('output', f"{dir_prefix}{name_part}_example.{get_extension(language)}"))

                try:
                    _, _, test_output_paths, _ = construct_paths(
                        input_file_paths={"prompt_file": prompt_path},
                        force=True, quiet=True, command="test",
                        command_options={"basename": basename},
                        context_override=context_override,
                        path_resolution_mode="cwd"
                    )
                    test_path = Path(test_output_paths.get('output', f"{dir_prefix}test_{name_part}.{get_extension(language)}"))
                except Exception:
                    # If test path construction fails, use default naming
                    test_path = Path(f"{dir_prefix}test_{name_part}.{get_extension(language)}")
                
            except Exception:
                # Final fallback to deriving from code path if all else fails
                code_path_obj = Path(code_path)
                code_dir = code_path_obj.parent
                code_stem = code_path_obj.stem
                code_ext = code_path_obj.suffix
                example_path = code_dir / f"{code_stem}_example{code_ext}"
                test_path = code_dir / f"test_{code_stem}{code_ext}"
        
        # Ensure all paths are Path objects
        if isinstance(code_path, str):
            code_path = Path(code_path)
        
        # Keep paths as they are (absolute or relative as returned by construct_paths)
        # This ensures consistency with how construct_paths expects them

        # Bug #156: Find all matching test files
        test_dir = test_path.parent
        _, name_part_for_glob = _extract_name_part(basename)
        test_stem = f"test_{name_part_for_glob}"
        extension = get_extension(language)
        if test_dir.exists():
            matching_test_files = sorted(test_dir.glob(f"{test_stem}*.{extension}"))
        else:
            matching_test_files = [test_path] if test_path.exists() else []

        return {
            'prompt': Path(prompt_path),
            'code': code_path,
            'example': example_path,
            'test': test_path,
            'test_files': matching_test_files or [test_path]  # Bug #156: All matching test files
        }

    except Exception as e:
        # Fallback to simple naming if construct_paths fails
        extension = get_extension(language)
        dir_prefix, name_part = _extract_name_part(basename)
        test_path = Path(f"{dir_prefix}test_{name_part}.{extension}")
        # Bug #156: Try to find matching test files even in fallback
        test_dir = Path('.')
        test_stem = f"{dir_prefix}test_{name_part}"
        if test_dir.exists():
            matching_test_files = sorted(test_dir.glob(f"{test_stem}*.{extension}"))
        else:
            matching_test_files = [test_path] if test_path.exists() else []
        return {
            'prompt': Path(prompts_dir) / f"{basename}_{language}.prompt",
            'code': Path(f"{dir_prefix}{name_part}.{extension}"),
            'example': Path(f"{dir_prefix}{name_part}_example.{extension}"),
            'test': test_path,
            'test_files': matching_test_files or [test_path]  # Bug #156: All matching test files
        }


def calculate_sha256(file_path: Path) -> Optional[str]:
    """Calculates the SHA256 hash of a file if it exists."""
    if not file_path.exists():
        return None
    
    try:
        hasher = hashlib.sha256()
        with open(file_path, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hasher.update(chunk)
        return hasher.hexdigest()
    except (IOError, OSError):
        return None


def read_fingerprint(basename: str, language: str) -> Optional[Fingerprint]:
    """Reads and validates the JSON fingerprint file."""
    meta_dir = get_meta_dir()
    meta_dir.mkdir(parents=True, exist_ok=True)
    fingerprint_file = meta_dir / f"{_safe_basename(basename)}_{language}.json"
    
    if not fingerprint_file.exists():
        return None
    
    try:
        with open(fingerprint_file, 'r') as f:
            data = json.load(f)
        
        return Fingerprint(
            pdd_version=data['pdd_version'],
            timestamp=data['timestamp'],
            command=data['command'],
            prompt_hash=data.get('prompt_hash'),
            code_hash=data.get('code_hash'),
            example_hash=data.get('example_hash'),
            test_hash=data.get('test_hash'),
            test_files=data.get('test_files')  # Bug #156
        )
    except (json.JSONDecodeError, KeyError, IOError):
        return None


def read_run_report(basename: str, language: str) -> Optional[RunReport]:
    """Reads and validates the JSON run report file."""
    meta_dir = get_meta_dir()
    meta_dir.mkdir(parents=True, exist_ok=True)
    run_report_file = meta_dir / f"{_safe_basename(basename)}_{language}_run.json"
    
    if not run_report_file.exists():
        return None
    
    try:
        with open(run_report_file, 'r') as f:
            data = json.load(f)
        
        return RunReport(
            timestamp=data['timestamp'],
            exit_code=data['exit_code'],
            tests_passed=data['tests_passed'],
            tests_failed=data['tests_failed'],
            coverage=data['coverage'],
            test_hash=data.get('test_hash'),  # Optional for backward compatibility
            test_files=data.get('test_files')  # Bug #156
        )
    except (json.JSONDecodeError, KeyError, IOError):
        return None


def calculate_current_hashes(paths: Dict[str, Any]) -> Dict[str, Any]:
    """Computes the hashes for all current files on disk."""
    # Return hash keys that match what the fingerprint expects
    hashes = {}
    for file_type, file_path in paths.items():
        if file_type == 'test_files':
            # Bug #156: Calculate hashes for all test files
            hashes['test_files'] = {
                f.name: calculate_sha256(f)
                for f in file_path
                if isinstance(f, Path) and f.exists()
            }
        elif isinstance(file_path, Path):
            hashes[f"{file_type}_hash"] = calculate_sha256(file_path)
    return hashes


def get_git_diff(file_path: Path) -> str:
    """Get git diff for a file against HEAD."""
    try:
        result = subprocess.run(
            ['git', 'diff', 'HEAD', str(file_path)],
            capture_output=True,
            text=True,
            cwd=file_path.parent if file_path.parent.exists() else Path.cwd()
        )
        
        if result.returncode == 0:
            return result.stdout
        else:
            return ""
    except (subprocess.SubprocessError, FileNotFoundError):
        return ""


def estimate_operation_cost(operation: str, language: str = "python") -> float:
    """Returns estimated cost in dollars for each operation based on typical LLM usage."""
    cost_map = {
        'auto-deps': 0.10,
        'generate': 0.50,
        'example': 0.30,
        'crash': 0.40,
        'verify': 0.35,
        'test': 0.60,
        'test_extend': 0.60,  # Same cost as test - generates additional tests
        'fix': 0.45,
        'update': 0.25,
        'analyze_conflict': 0.20,
        'nothing': 0.0,
        'all_synced': 0.0,
        'error': 0.0,
        'fail_and_request_manual_merge': 0.0
    }
    return cost_map.get(operation, 0.0)


def validate_expected_files(fingerprint: Optional[Fingerprint], paths: Dict[str, Path]) -> Dict[str, bool]:
    """
    Validate that files expected to exist based on fingerprint actually exist.
    
    Args:
        fingerprint: The last known good state fingerprint
        paths: Dict mapping file types to their expected Path objects
    
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
    
    Args:
        missing_files: List of file types that are missing
        paths: Dict mapping file types to their expected Path objects
        fingerprint: The last known good state fingerprint
        basename: The base name for the PDD unit
        language: The programming language
        prompts_dir: Directory containing prompt files
        skip_tests: If True, skip test generation
        skip_verify: If True, skip verification operations
    
    Returns:
        SyncDecision object with the appropriate recovery operation
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
                    confidence=1.0,
                    estimated_cost=estimate_operation_cost('auto-deps'),
                    details={
                        'decision_type': 'heuristic',
                        'missing_files': missing_files, 
                        'prompt_path': str(paths['prompt']),
                        'has_dependencies': True
                    }
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='Code file missing - regenerate from prompt',
                    confidence=1.0,
                    estimated_cost=estimate_operation_cost('generate'),
                    details={
                        'decision_type': 'heuristic',
                        'missing_files': missing_files, 
                        'prompt_path': str(paths['prompt']),
                        'has_dependencies': False
                    }
                )
    
    elif 'example' in missing_files and paths['code'].exists():
        # Code exists but example missing
        return SyncDecision(
            operation='example',
            reason='Example file missing - regenerate example',
            confidence=1.0,
            estimated_cost=estimate_operation_cost('example'),
            details={
                'decision_type': 'heuristic',
                'missing_files': missing_files, 
                'code_path': str(paths['code'])
            }
        )
    
    elif 'test' in missing_files and paths['code'].exists() and paths['example'].exists():
        # Code and example exist but test missing
        if skip_tests:
            # Skip test generation if --skip-tests flag is used
            return SyncDecision(
                operation='nothing',
                reason='Test file missing but --skip-tests specified - workflow complete',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('nothing'),
                details={
                    'decision_type': 'heuristic',
                    'missing_files': missing_files, 
                    'skip_tests': True
                }
            )
        else:
            return SyncDecision(
                operation='test',
                reason='Test file missing - regenerate tests',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('test'),
                details={
                    'decision_type': 'heuristic',
                    'missing_files': missing_files, 
                    'code_path': str(paths['code'])
                }
            )
    
    # Fallback - regenerate everything
    return SyncDecision(
        operation='generate',
        reason='Multiple files missing - regenerate from prompt',
        confidence=1.0,
        estimated_cost=estimate_operation_cost('generate'),
        details={
            'decision_type': 'heuristic',
            'missing_files': missing_files
        }
    )


def _is_workflow_complete(paths: Dict[str, Path], skip_tests: bool = False, skip_verify: bool = False,
                          basename: str = None, language: str = None) -> bool:
    """
    Check if workflow is complete considering skip flags.

    Args:
        paths: Dict mapping file types to their expected Path objects
        skip_tests: If True, test files are not required for completion
        skip_verify: If True, verification operations are not required
        basename: Module basename (required for run_report check)
        language: Module language (required for run_report check)

    Returns:
        True if all required files exist AND have been validated (run_report exists)
    """
    required_files = ['code', 'example']

    if not skip_tests:
        required_files.append('test')

    # Check all required files exist
    if not all(paths[f].exists() for f in required_files):
        return False

    # Also check that run_report exists and code works (exit_code == 0)
    # Without this, newly generated code would incorrectly be marked as "complete"
    if basename and language:
        run_report = read_run_report(basename, language)
        if not run_report or run_report.exit_code != 0:
            return False

        # Check that run_report corresponds to current test files (staleness detection)
        # If any test file changed since run_report was created, we can't trust the results
        if not skip_tests:
            # Bug #156: Check ALL test files, not just the primary one
            if 'test_files' in paths and run_report.test_files:
                # New multi-file comparison
                current_test_hashes = {
                    f.name: calculate_sha256(f)
                    for f in paths['test_files']
                    if f.exists()
                }
                stored_test_hashes = run_report.test_files

                # Check if any test file changed or new ones added/removed
                if set(current_test_hashes.keys()) != set(stored_test_hashes.keys()):
                    return False  # Test files added or removed

                for fname, current_hash in current_test_hashes.items():
                    if stored_test_hashes.get(fname) != current_hash:
                        return False  # Test file content changed
            elif 'test' in paths and paths['test'].exists():
                # Backward compat: single file check
                current_test_hash = calculate_sha256(paths['test'])
                if run_report.test_hash and current_test_hash != run_report.test_hash:
                    # run_report was created for a different version of the test file
                    return False
                if not run_report.test_hash:
                    # Legacy run_report without test_hash - check fingerprint timestamp as fallback
                    fingerprint = read_fingerprint(basename, language)
                    if fingerprint:
                        # If fingerprint is newer than run_report, run_report might be stale
                        from datetime import datetime
                        try:
                            fp_time = datetime.fromisoformat(fingerprint.timestamp.replace('Z', '+00:00'))
                            rr_time = datetime.fromisoformat(run_report.timestamp.replace('Z', '+00:00'))
                            if fp_time > rr_time:
                                return False  # run_report predates fingerprint, might be stale
                        except (ValueError, AttributeError):
                            pass  # If timestamps can't be parsed, skip this check

        # Check verify has been done (unless skip_verify)
        # Without this, workflow would be "complete" after crash even though verify hasn't run
        # Bug #23 fix: Also check for 'skip:' prefix which indicates operation was skipped, not executed
        if not skip_verify:
            fingerprint = read_fingerprint(basename, language)
            if fingerprint:
                # If command starts with 'skip:', the operation was skipped, not completed
                if fingerprint.command.startswith('skip:'):
                    return False
                if fingerprint.command not in ['verify', 'test', 'fix', 'update']:
                    return False

        # CRITICAL FIX: Check tests have been run (unless skip_tests)
        # Without this, workflow would be "complete" after verify even though tests haven't run
        # This prevents false positive success when skip_verify=True but tests are still required
        # Bug #23 fix: Also check for 'skip:' prefix which indicates operation was skipped, not executed
        if not skip_tests:
            fp = read_fingerprint(basename, language)
            if fp:
                # If command starts with 'skip:', the operation was skipped, not completed
                if fp.command.startswith('skip:'):
                    return False
                if fp.command not in ['test', 'fix', 'update']:
                    return False

    return True


def check_for_dependencies(prompt_content: str) -> bool:
    """Check if prompt contains actual dependency indicators that need auto-deps processing."""
    # Only check for specific XML tags that indicate actual dependencies
    xml_dependency_indicators = [
        '<include>',
        '<web>',
        '<shell>'
    ]
    
    # Check for explicit dependency management mentions
    explicit_dependency_indicators = [
        'auto-deps',
        'auto_deps',
        'dependencies needed',
        'requires dependencies',
        'include dependencies'
    ]
    
    prompt_lower = prompt_content.lower()
    
    # Check for XML tags (case-sensitive for proper XML)
    has_xml_deps = any(indicator in prompt_content for indicator in xml_dependency_indicators)
    
    # Check for explicit dependency mentions
    has_explicit_deps = any(indicator in prompt_lower for indicator in explicit_dependency_indicators)
    
    return has_xml_deps or has_explicit_deps


def _check_example_success_history(basename: str, language: str) -> bool:
    """
    Check if the example has run successfully before by examining historical fingerprints and run reports.
    
    Args:
        basename: The base name for the PDD unit
        language: The programming language
    
    Returns:
        True if the example has run successfully before, False otherwise
    """
    meta_dir = get_meta_dir()
    
    # Strategy 1: Check if there's a fingerprint with 'verify' command (indicates successful example run)
    # Cache fingerprint and run report to avoid redundant I/O operations
    fingerprint = read_fingerprint(basename, language)
    current_run_report = read_run_report(basename, language)
    
    # Strategy 1: Check if there's a fingerprint with 'verify' command (indicates successful example run)
    if fingerprint and fingerprint.command == 'verify':
        return True
    
    # Strategy 2: Check current run report for successful runs (exit_code == 0)
    # Note: We check the current run report for successful history since it's updated
    # This allows for a simple check of recent success
    if current_run_report and current_run_report.exit_code == 0:
        return True
    
    # Strategy 2b: Look for historical run reports with exit_code == 0
    # Check all run report files in the meta directory that match the pattern
    run_report_pattern = f"{_safe_basename(basename)}_{language}_run"
    for file in meta_dir.glob(f"{run_report_pattern}*.json"):
        try:
            with open(file, 'r') as f:
                data = json.load(f)
            
            # If we find any historical run with exit_code == 0, the example has run successfully
            if data.get('exit_code') == 0:
                return True
        except (json.JSONDecodeError, KeyError, IOError):
            continue
    
    # Strategy 3: Check if fingerprint has example_hash and was created after successful operations
    # Commands that indicate example was working: 'example', 'verify', 'test', 'fix'
    if fingerprint and fingerprint.example_hash:
        successful_commands = {'example', 'verify', 'test', 'fix'}
        if fingerprint.command in successful_commands:
            # If the fingerprint was created after these commands, the example likely worked
            return True
    
    return False


def sync_determine_operation(basename: str, language: str, target_coverage: float, budget: float = 10.0, log_mode: bool = False, prompts_dir: str = "prompts", skip_tests: bool = False, skip_verify: bool = False, context_override: Optional[str] = None) -> SyncDecision:
    """
    Core decision-making function for sync operations with skip flag awareness.
    
    Args:
        basename: The base name for the PDD unit
        language: The programming language
        target_coverage: Desired test coverage percentage
        budget: Maximum budget for operations
        log_mode: If True, skip locking entirely for read-only analysis
        prompts_dir: Directory containing prompt files
        skip_tests: If True, skip test generation and execution
        skip_verify: If True, skip verification operations
    
    Returns:
        SyncDecision object with the recommended operation
    """
    
    if log_mode:
        # Skip locking for read-only analysis
        return _perform_sync_analysis(basename, language, target_coverage, budget, prompts_dir, skip_tests, skip_verify, context_override)
    else:
        # Normal exclusive locking for actual operations
        with SyncLock(basename, language) as lock:
            return _perform_sync_analysis(basename, language, target_coverage, budget, prompts_dir, skip_tests, skip_verify, context_override)


def _perform_sync_analysis(basename: str, language: str, target_coverage: float, budget: float, prompts_dir: str = "prompts", skip_tests: bool = False, skip_verify: bool = False, context_override: Optional[str] = None) -> SyncDecision:
    """
    Perform the sync state analysis without locking concerns.
    
    Args:
        basename: The base name for the PDD unit
        language: The programming language
        target_coverage: Desired test coverage percentage
        budget: Maximum budget for operations
        prompts_dir: Directory containing prompt files
        skip_tests: If True, skip test generation and execution
        skip_verify: If True, skip verification operations
    
    Returns:
        SyncDecision object with the recommended operation
    """
    # 1. Check Runtime Signals First (Highest Priority)
    # Workflow Order (from whitepaper):
    # 1. auto-deps (find context/dependencies)
    # 2. generate (create code module)  
    # 3. example (create usage example)
    # 4. crash (resolve crashes if code doesn't run)
    # 5. verify (verify example runs correctly after crash fix)
    # 6. test (generate unit tests)
    # 7. fix (resolve bugs found by tests)
    # 8. update (sync changes back to prompt)
    
    # Read fingerprint early since we need it for crash verification
    fingerprint = read_fingerprint(basename, language)

    # Check if auto-deps just completed - ALWAYS regenerate code after auto-deps
    # This must be checked early, before any run_report processing, because:
    # 1. Old run_report (if exists) is stale and should be ignored
    # 2. auto-deps updates dependencies but doesn't regenerate code
    if fingerprint and fingerprint.command == 'auto-deps':
        paths = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
        return SyncDecision(
            operation='generate',
            reason='Auto-deps completed - regenerate code with updated prompt',
            confidence=0.90,
            estimated_cost=estimate_operation_cost('generate'),
            details={
                'decision_type': 'heuristic',
                'previous_command': 'auto-deps',
                'code_exists': paths['code'].exists() if paths.get('code') else False,
                'regenerate_after_autodeps': True
            }
        )

    run_report = read_run_report(basename, language)
    # Only process runtime signals (crash/fix/test) if we have a fingerprint
    # Without a fingerprint, run_report is stale/orphaned and should be ignored
    if run_report and fingerprint:
        # Check for prompt changes FIRST - prompt changes take priority over runtime signals
        # If the user modified the prompt, we need to regenerate regardless of runtime state
        if fingerprint:
            paths = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
            current_prompt_hash = calculate_sha256(paths['prompt'])
            if current_prompt_hash and current_prompt_hash != fingerprint.prompt_hash:
                prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore') if paths['prompt'].exists() else ""
                has_deps = check_for_dependencies(prompt_content)
                return SyncDecision(
                    operation='auto-deps' if has_deps else 'generate',
                    reason='Prompt changed - regenerating (takes priority over runtime signals)',
                    confidence=0.95,
                    estimated_cost=estimate_operation_cost('generate'),
                    details={
                        'decision_type': 'heuristic',
                        'prompt_changed': True,
                        'previous_command': fingerprint.command,
                        'runtime_state_ignored': True
                    }
                )

        # Check if we just completed a crash operation and need verification FIRST
        # This takes priority over test failures because we need to verify the crash fix worked
        # BUT only proceed to verify if exit_code == 0 (crash fix succeeded)
        if fingerprint and fingerprint.command == 'crash' and not skip_verify:
            if run_report.exit_code != 0:
                # Crash fix didn't work - need to re-run crash
                return SyncDecision(
                    operation='crash',
                    reason=f'Previous crash operation failed (exit_code={run_report.exit_code}) - retry crash fix',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('crash'),
                    details={
                        'decision_type': 'heuristic',
                        'previous_command': 'crash',
                        'exit_code': run_report.exit_code,
                        'workflow_stage': 'crash_retry'
                    }
                )
            return SyncDecision(
                operation='verify',
                reason='Previous crash operation completed - verify example runs correctly',
                confidence=0.90,
                estimated_cost=estimate_operation_cost('verify'),
                details={
                    'decision_type': 'heuristic',
                    'previous_command': 'crash',
                    'current_exit_code': run_report.exit_code,
                    'fingerprint_command': fingerprint.command
                }
            )
        
        # Check test failures (after crash verification check)
        if run_report.tests_failed > 0:
            # First check if the test file actually exists
            pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
            test_file = pdd_files.get('test')
            
            # Only suggest 'fix' if test file exists
            if test_file and test_file.exists():
                return SyncDecision(
                    operation='fix',
                    reason=f'Test failures detected: {run_report.tests_failed} failed tests',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('fix'),
                    details={
                        'decision_type': 'heuristic',
                        'tests_failed': run_report.tests_failed,
                        'exit_code': run_report.exit_code,
                        'coverage': run_report.coverage
                    }
                )
            # If test file doesn't exist but we have test failures in run report,
            # we need to generate the test first
            else:
                return SyncDecision(
                    operation='test',
                    reason='Test failures reported but test file missing - need to generate tests',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'run_report_shows_failures': True,
                        'test_file_exists': False
                    }
                )
        
        # Then check for runtime crashes (only if no test failures)
        if run_report.exit_code != 0:
            # Context-aware decision: prefer 'fix' over 'crash' when example has run successfully before
            has_example_run_successfully = _check_example_success_history(basename, language)
            
            if has_example_run_successfully:
                return SyncDecision(
                    operation='fix',
                    reason='Runtime error detected but example has run successfully before - prefer fix over crash',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('fix'),
                    details={
                        'decision_type': 'heuristic',
                        'exit_code': run_report.exit_code,
                        'timestamp': run_report.timestamp,
                        'example_success_history': True,
                        'decision_rationale': 'prefer_fix_over_crash'
                    }
                )
            else:
                return SyncDecision(
                    operation='crash',
                    reason='Runtime error detected in last run - no successful example history',
                    confidence=0.95,
                    estimated_cost=estimate_operation_cost('crash'),
                    details={
                        'decision_type': 'heuristic',
                        'exit_code': run_report.exit_code,
                        'timestamp': run_report.timestamp,
                        'example_success_history': False,
                        'decision_rationale': 'crash_without_history'
                    }
                )
        
        if run_report.coverage < target_coverage:
            if skip_tests:
                # When tests are skipped but coverage is low, consider workflow complete
                # since we can't improve coverage without running tests
                return SyncDecision(
                    operation='all_synced',
                    reason=f'Coverage {run_report.coverage:.1f}% below target {target_coverage:.1f}% but tests skipped',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('all_synced'),
                    details={
                        'decision_type': 'heuristic',
                        'current_coverage': run_report.coverage,
                        'target_coverage': target_coverage,
                        'tests_skipped': True,
                        'skip_tests': True
                    }
                )
            elif run_report.tests_failed == 0 and run_report.tests_passed > 0:
                # Tests pass but coverage is below target
                # Return 'test_extend' to signal we need to ADD more tests, not regenerate
                return SyncDecision(
                    operation='test_extend',
                    reason=f'Tests pass ({run_report.tests_passed} passed) but coverage {run_report.coverage:.1f}% below target {target_coverage:.1f}% - extending tests',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'current_coverage': run_report.coverage,
                        'target_coverage': target_coverage,
                        'tests_passed': run_report.tests_passed,
                        'tests_failed': run_report.tests_failed,
                        'extend_tests': True
                    }
                )
            else:
                return SyncDecision(
                    operation='test',
                    reason=f'Coverage {run_report.coverage:.1f}% below target {target_coverage:.1f}%',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'current_coverage': run_report.coverage,
                        'target_coverage': target_coverage,
                        'tests_passed': run_report.tests_passed,
                        'tests_failed': run_report.tests_failed
                    }
                )
    
    # 2. Analyze File State
    paths = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    current_hashes = calculate_current_hashes(paths)
    
    # 3. Implement the Decision Tree
    if not fingerprint:
        # No Fingerprint (New or Untracked Unit)
        if paths['prompt'].exists():
            prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
            if check_for_dependencies(prompt_content):
                return SyncDecision(
                    operation='auto-deps',
                    reason='New prompt with dependencies detected',
                    confidence=0.80,
                    estimated_cost=estimate_operation_cost('auto-deps'),
                    details={
                        'decision_type': 'heuristic',
                        'prompt_path': str(paths['prompt']),
                        'fingerprint_found': False,
                        'has_dependencies': True
                    }
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='New prompt ready for code generation',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('generate'),
                    details={
                        'decision_type': 'heuristic',
                        'prompt_path': str(paths['prompt']),
                        'fingerprint_found': False,
                        'has_dependencies': False
                    }
                )
        else:
            return SyncDecision(
                operation='nothing',
                reason='No prompt file and no history - nothing to do',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('nothing'),
                details={
                    'decision_type': 'heuristic',
                    'prompt_exists': False,
                    'fingerprint_found': False
                }
            )
    
    # CRITICAL FIX: Validate expected files exist before hash comparison
    if fingerprint:
        file_validation = validate_expected_files(fingerprint, paths)
        missing_expected_files = [
            file_type for file_type, exists in file_validation.items() 
            if not exists
        ]
        
        if missing_expected_files:
            # Files are missing that should exist - need to regenerate
            # This prevents the incorrect analyze_conflict decision
            return _handle_missing_expected_files(
                missing_expected_files, paths, fingerprint, basename, language, prompts_dir, skip_tests, skip_verify
            )
    
    # Compare hashes only for files that actually exist (prevents None != "hash" false positives)
    changes = []
    if fingerprint:
        if current_hashes.get('prompt_hash') != fingerprint.prompt_hash:
            changes.append('prompt')
        # Only compare hashes for files that exist
        if paths['code'].exists() and current_hashes.get('code_hash') != fingerprint.code_hash:
            changes.append('code')
        if paths['example'].exists() and current_hashes.get('example_hash') != fingerprint.example_hash:
            changes.append('example')
        if paths['test'].exists() and current_hashes.get('test_hash') != fingerprint.test_hash:
            changes.append('test')
    
    if not changes:
        # No Changes (Hashes Match Fingerprint) - Progress workflow with skip awareness
        if _is_workflow_complete(paths, skip_tests, skip_verify, basename, language):
            return SyncDecision(
                operation='nothing',
                reason=f'All required files synchronized (skip_tests={skip_tests}, skip_verify={skip_verify})',
                confidence=1.0,
                estimated_cost=estimate_operation_cost('nothing'),
                details={
                    'decision_type': 'heuristic',
                    'skip_tests': skip_tests,
                    'skip_verify': skip_verify,
                    'workflow_complete': True
                }
            )

        # Handle incomplete workflow when all files exist (including test)
        # This addresses the blind spot where crash/verify/test logic only runs when test is missing
        if (paths['code'].exists() and paths['example'].exists() and paths['test'].exists()):
            run_report = read_run_report(basename, language)

            # BUG 4 & 1: No run_report OR crash detected (exit_code != 0)
            if not run_report or run_report.exit_code != 0:
                return SyncDecision(
                    operation='crash',
                    reason='All files exist but needs validation' +
                           (' - no run_report' if not run_report else f' - exit_code={run_report.exit_code}'),
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('crash'),
                    details={
                        'decision_type': 'heuristic',
                        'all_files_exist': True,
                        'run_report_missing': not run_report,
                        'exit_code': None if not run_report else run_report.exit_code,
                        'workflow_stage': 'post_regeneration_validation'
                    }
                )

            # BUG 2: Verify not run yet (run_report exists, exit_code=0, but command != verify/test)
            if fingerprint and fingerprint.command not in ['verify', 'test', 'fix', 'update'] and not skip_verify:
                return SyncDecision(
                    operation='verify',
                    reason='All files exist but verification not completed',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('verify'),
                    details={
                        'decision_type': 'heuristic',
                        'all_files_exist': True,
                        'last_command': fingerprint.command,
                        'workflow_stage': 'verification_pending'
                    }
                )

            # Stale run_report detected: _is_workflow_complete returned False but all other conditions passed
            # This happens when run_report.test_hash doesn't match current test file, or
            # when fingerprint timestamp > run_report timestamp (legacy detection)
            # Need to re-run tests to get accurate results
            if run_report and run_report.exit_code == 0:
                return SyncDecision(
                    operation='test',
                    reason='Run report is stale - need to re-run tests to verify current state',
                    confidence=0.9,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'all_files_exist': True,
                        'run_report_stale': True,
                        'run_report_test_hash': run_report.test_hash,
                        'workflow_stage': 'revalidation'
                    }
                )

        # Progress workflow considering skip flags
        if paths['code'].exists() and not paths['example'].exists():
            return SyncDecision(
                operation='example',
                reason='Code exists but example missing - progress workflow',
                confidence=0.85,
                estimated_cost=estimate_operation_cost('example'),
                details={
                    'decision_type': 'heuristic',
                    'code_path': str(paths['code']),
                    'code_exists': True,
                    'example_exists': False
                }
            )
        
        if (paths['code'].exists() and paths['example'].exists() and 
            not skip_tests and not paths['test'].exists()):
            
            # Check if example has been crash-tested and verified before allowing test generation
            run_report = read_run_report(basename, language)
            if not run_report and not skip_verify:
                # No run report exists - need to test the example first
                # But if skip_verify is True, skip crash/verify and go to test generation
                return SyncDecision(
                    operation='crash',
                    reason='Example exists but needs runtime testing before test generation',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('crash'),
                    details={
                        'decision_type': 'heuristic',
                        'code_path': str(paths['code']),
                        'example_path': str(paths['example']),
                        'no_run_report': True,
                        'workflow_stage': 'crash_validation'
                    }
                )
            elif run_report and run_report.exit_code != 0 and not skip_verify:
                # Example crashed - fix it before proceeding
                # But if skip_verify is True, skip crash fix and proceed
                return SyncDecision(
                    operation='crash',
                    reason='Example crashes - fix runtime errors before test generation',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('crash'),
                    details={
                        'decision_type': 'heuristic',
                        'exit_code': run_report.exit_code,
                        'workflow_stage': 'crash_fix'
                    }
                )
            elif fingerprint and fingerprint.command != 'verify' and not skip_verify:
                # Example runs but hasn't been verified yet
                return SyncDecision(
                    operation='verify',
                    reason='Example runs but needs verification before test generation',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('verify'),
                    details={
                        'decision_type': 'heuristic',
                        'exit_code': run_report.exit_code,
                        'last_command': fingerprint.command,
                        'workflow_stage': 'verify_validation'
                    }
                )
            else:
                # Example runs and is verified (or verify is skipped) - now safe to generate tests
                return SyncDecision(
                    operation='test',
                    reason='Example validated - ready for test generation',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'code_path': str(paths['code']),
                        'example_path': str(paths['example']),
                        'code_exists': True,
                        'example_exists': True,
                        'test_exists': False,
                        'workflow_stage': 'test_generation'
                    }
                )
        
        # Some files are missing but no changes detected
        if not paths['code'].exists():
            if paths['prompt'].exists():
                # CRITICAL FIX: Check if auto-deps was just completed to prevent infinite loop
                if fingerprint and fingerprint.command == 'auto-deps':
                    return SyncDecision(
                        operation='generate',
                        reason='Auto-deps completed, now generate missing code file',
                        confidence=0.90,
                        estimated_cost=estimate_operation_cost('generate'),
                        details={
                            'decision_type': 'heuristic',
                            'prompt_path': str(paths['prompt']),
                            'code_exists': False,
                            'auto_deps_completed': True,
                            'previous_command': fingerprint.command
                        }
                    )
                
                prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
                if check_for_dependencies(prompt_content):
                    return SyncDecision(
                        operation='auto-deps',
                        reason='Missing code file, prompt has dependencies',
                        confidence=0.80,
                        estimated_cost=estimate_operation_cost('auto-deps'),
                        details={
                            'decision_type': 'heuristic',
                            'prompt_path': str(paths['prompt']),
                            'code_exists': False,
                            'has_dependencies': True
                        }
                    )
                else:
                    return SyncDecision(
                        operation='generate',
                        reason='Missing code file - generate from prompt',
                        confidence=0.90,
                        estimated_cost=estimate_operation_cost('generate'),
                        details={
                            'decision_type': 'heuristic',
                            'prompt_path': str(paths['prompt']),
                            'code_exists': False,
                            'has_dependencies': False
                        }
                    )
    
    elif len(changes) == 1:
        # Simple Changes (Single File Modified)
        change = changes[0]
        
        if change == 'prompt':
            prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
            if check_for_dependencies(prompt_content):
                return SyncDecision(
                    operation='auto-deps',
                    reason='Prompt changed and dependencies need updating',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('auto-deps'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_file': 'prompt',
                        'has_dependencies': True,
                        'prompt_changed': True
                    }
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='Prompt changed - regenerate code',
                    confidence=0.90,
                    estimated_cost=estimate_operation_cost('generate'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_file': 'prompt',
                        'has_dependencies': False,
                        'prompt_changed': True
                    }
                )
        
        elif change == 'code':
            return SyncDecision(
                operation='update',
                reason='Code changed - update prompt to reflect changes',
                confidence=0.85,
                estimated_cost=estimate_operation_cost('update'),
                details={
                    'decision_type': 'heuristic',
                    'changed_file': 'code',
                    'code_changed': True
                }
            )
        
        elif change == 'test':
            return SyncDecision(
                operation='test',
                reason='Test changed - run new tests',
                confidence=0.80,
                estimated_cost=estimate_operation_cost('test'),
                details={
                    'decision_type': 'heuristic',
                    'changed_file': 'test',
                    'test_changed': True
                }
            )
        
        elif change == 'example':
            return SyncDecision(
                operation='verify',
                reason='Example changed - verify new example',
                confidence=0.80,
                estimated_cost=estimate_operation_cost('verify'),
                details={
                    'decision_type': 'heuristic',
                    'changed_file': 'example',
                    'example_changed': True
                }
            )
    
    else:
        # Complex Changes (Multiple Files Modified)
        # CRITICAL: Only treat as conflict if prompt changed along with derived artifacts
        # If only derived artifacts changed (code, example, test), this is NOT a conflict
        # per PDD doctrine - all are derived from the unchanged prompt

        if 'prompt' in changes:
            # True conflict: prompt (source of truth) changed along with derived artifacts
            return SyncDecision(
                operation='analyze_conflict',
                reason='Prompt and derived files changed - requires conflict analysis',
                confidence=0.70,
                estimated_cost=estimate_operation_cost('analyze_conflict'),
                details={
                    'decision_type': 'heuristic',
                    'changed_files': changes,
                    'num_changes': len(changes),
                    'prompt_changed': True
                }
            )
        else:
            # Only derived artifacts changed - prompt (source of truth) is unchanged
            # Continue workflow from where it was interrupted

            # If code changed, need to re-verify
            if 'code' in changes:
                return SyncDecision(
                    operation='verify',
                    reason='Derived files changed (prompt unchanged) - verify code works',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('verify'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_files': changes,
                        'num_changes': len(changes),
                        'prompt_changed': False,
                        'workflow_stage': 'continue_after_interruption'
                    }
                )
            # If only example/test changed
            elif 'example' in changes:
                return SyncDecision(
                    operation='verify',
                    reason='Example changed (prompt unchanged) - verify example runs',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('verify'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_files': changes,
                        'prompt_changed': False
                    }
                )
            elif 'test' in changes:
                return SyncDecision(
                    operation='test',
                    reason='Test changed (prompt unchanged) - run tests',
                    confidence=0.85,
                    estimated_cost=estimate_operation_cost('test'),
                    details={
                        'decision_type': 'heuristic',
                        'changed_files': changes,
                        'prompt_changed': False
                    }
                )
    
    # Fallback - should not reach here normally
    return SyncDecision(
        operation='nothing',
        reason='No clear operation determined',
        confidence=0.50,
        estimated_cost=estimate_operation_cost('nothing'),
        details={
            'decision_type': 'heuristic',
            'fingerprint_exists': fingerprint is not None,
            'changes': changes,
            'fallback': True
        }
    )


def analyze_conflict_with_llm(
    basename: str,
    language: str,
    fingerprint: Fingerprint,
    changed_files: List[str],
    prompts_dir: str = "prompts",
    context_override: Optional[str] = None,
) -> SyncDecision:
    """
    Resolve complex sync conflicts using an LLM.
    
    Args:
        basename: The base name for the PDD unit
        language: The programming language
        fingerprint: The last known good state
        changed_files: List of files that have changed
        prompts_dir: Directory containing prompt files
    
    Returns:
        SyncDecision object with LLM-recommended operation
    """
    
    try:
        # 1. Load LLM Prompt
        prompt_template = load_prompt_template("sync_analysis_LLM")
        if not prompt_template:
            # Fallback if template not found
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason='LLM analysis template not found - manual merge required',
                confidence=0.0,
                estimated_cost=estimate_operation_cost('fail_and_request_manual_merge'),
                details={
                    'decision_type': 'llm',
                    'error': 'Template not available',
                    'changed_files': changed_files
                }
            )
        
        # 2. Gather file paths and diffs
        paths = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
        
        # Generate diffs for changed files
        diffs = {}
        for file_type in changed_files:
            if file_type in paths and paths[file_type].exists():
                diffs[f"{file_type}_diff"] = get_git_diff(paths[file_type])
                diffs[f"{file_type}_path"] = str(paths[file_type])
            else:
                diffs[f"{file_type}_diff"] = ""
                diffs[f"{file_type}_path"] = str(paths.get(file_type, ''))
        
        # 3. Format the prompt
        formatted_prompt = prompt_template.format(
            fingerprint=json.dumps({
                'pdd_version': fingerprint.pdd_version,
                'timestamp': fingerprint.timestamp,
                'command': fingerprint.command,
                'prompt_hash': fingerprint.prompt_hash,
                'code_hash': fingerprint.code_hash,
                'example_hash': fingerprint.example_hash,
                'test_hash': fingerprint.test_hash
            }, indent=2),
            changed_files_list=', '.join(changed_files),
            prompt_diff=diffs.get('prompt_diff', ''),
            code_diff=diffs.get('code_diff', ''),
            example_diff=diffs.get('example_diff', ''),
            test_diff=diffs.get('test_diff', ''),
            prompt_path=diffs.get('prompt_path', ''),
            code_path=diffs.get('code_path', ''),
            example_path=diffs.get('example_path', ''),
            test_path=diffs.get('test_path', '')
        )
        
        # 4. Invoke LLM with caching for determinism
        response = llm_invoke(
            prompt=formatted_prompt,
            input_json={},
            strength=0.7,  # Use a consistent strength for determinism
            temperature=0.0,  # Use temperature 0 for deterministic output
            verbose=False
        )
        
        # 5. Parse and validate response
        try:
            llm_result = json.loads(response['result'])
            
            # Validate required keys
            required_keys = ['next_operation', 'reason', 'confidence']
            if not all(key in llm_result for key in required_keys):
                raise ValueError("Missing required keys in LLM response")
            
            # Check confidence threshold
            confidence = float(llm_result.get('confidence', 0.0))
            if confidence < 0.75:
                return SyncDecision(
                    operation='fail_and_request_manual_merge',
                    reason=f'LLM confidence too low ({confidence:.2f}) - manual merge required',
                    confidence=confidence,
                    estimated_cost=response.get('cost', 0.0),
                    details={
                        'decision_type': 'llm',
                        'llm_response': llm_result,
                        'changed_files': changed_files,
                        'confidence_threshold': 0.75
                    }
                )
            
            # Extract operation and details
            operation = llm_result['next_operation']
            reason = llm_result['reason']
            merge_strategy = llm_result.get('merge_strategy', {})
            follow_up_operations = llm_result.get('follow_up_operations', [])
            
            return SyncDecision(
                operation=operation,
                reason=f"LLM analysis: {reason}",
                confidence=confidence,
                estimated_cost=response.get('cost', 0.0),
                details={
                    'decision_type': 'llm',
                    'llm_response': llm_result,
                    'changed_files': changed_files,
                    'merge_strategy': merge_strategy,
                    'follow_up_operations': follow_up_operations
                },
                prerequisites=follow_up_operations
            )
            
        except (json.JSONDecodeError, ValueError, KeyError) as e:
            # Invalid LLM response - fallback to manual merge
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason=f'Invalid LLM response: {e} - manual merge required',
                confidence=0.0,
                estimated_cost=response.get('cost', 0.0),
                details={
                    'decision_type': 'llm',
                    'error': str(e),
                    'raw_response': response.get('result', ''),
                    'changed_files': changed_files,
                    'llm_error': True
                }
            )
    
    except Exception as e:
        # Any other error - fallback to manual merge
        return SyncDecision(
            operation='fail_and_request_manual_merge',
            reason=f'Error during LLM analysis: {e} - manual merge required',
            confidence=0.0,
            estimated_cost=estimate_operation_cost('fail_and_request_manual_merge'),
            details={
                'decision_type': 'llm',
                'error': str(e),
                'changed_files': changed_files,
                'llm_error': True
            }
        )


if __name__ == "__main__":
    # Example usage
    if len(sys.argv) < 3 or len(sys.argv) > 4:
        print("Usage: python sync_determine_operation.py <basename> <language> [target_coverage]")
        sys.exit(1)
    
    basename = sys.argv[1]
    language = sys.argv[2]
    target_coverage = float(sys.argv[3]) if len(sys.argv) == 4 else 90.0
    
    decision = sync_determine_operation(basename, language, target_coverage)
    
    print(f"Operation: {decision.operation}")
    print(f"Reason: {decision.reason}")
    print(f"Estimated Cost: ${decision.estimated_cost:.2f}")
    print(f"Confidence: {decision.confidence:.2f}")
    if decision.details:
        print(f"Details: {json.dumps(decision.details, indent=2)}")
