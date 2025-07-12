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
           'sync_determine_operation', 'analyze_conflict_with_llm']


@dataclass
class Fingerprint:
    """Represents the last known good state of a PDD unit."""
    pdd_version: str
    timestamp: str  # ISO 8601 format
    command: str    # e.g., "generate", "fix"
    prompt_hash: Optional[str]
    code_hash: Optional[str]
    example_hash: Optional[str]
    test_hash: Optional[str]


@dataclass
class RunReport:
    """Represents the results from the last test run."""
    timestamp: str
    exit_code: int
    tests_passed: int
    tests_failed: int
    coverage: float


@dataclass
class SyncDecision:
    """Represents a decision about what PDD operation to run next."""
    operation: str  # 'auto-deps', 'generate', 'example', 'crash', 'verify', 'test', 'fix', 'update', 'analyze_conflict', 'nothing'
    reason: str
    details: Dict[str, Any] = field(default_factory=dict)
    estimated_cost: float = 0.0
    confidence: float = 1.0
    prerequisites: List[str] = field(default_factory=list)


class SyncLock:
    """Context manager for handling file-descriptor based locking."""
    
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.lock_file = get_locks_dir() / f"{basename}_{language}.lock"
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


def get_pdd_file_paths(basename: str, language: str, prompts_dir: str = "prompts") -> Dict[str, Path]:
    """Returns a dictionary mapping file types to their expected Path objects."""
    try:
        # Use construct_paths to get configuration-aware paths
        prompt_filename = f"{basename}_{language}.prompt"
        prompt_path = str(Path(prompts_dir) / prompt_filename)
        
        # Check if prompt file exists - if not, we can't proceed with construct_paths
        if not Path(prompt_path).exists():
            # Fall back to default path construction if prompt doesn't exist
            extension = get_extension(language)
            return {
                'prompt': Path(prompt_path),
                'code': Path(f"{basename}.{extension}"),
                'example': Path(f"{basename}_example.{extension}"),
                'test': Path(f"test_{basename}.{extension}")
            }
        
        input_file_paths = {
            "prompt_file": prompt_path
        }
        
        # Only call construct_paths if the prompt file exists
        resolved_config, input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_file_paths,
            force=True,  # Use force=True to avoid interactive prompts during sync
            quiet=True,
            command="generate",
            command_options={}
        )
        
        # Extract paths from config as specified in the spec
        # The spec shows: return { 'prompt': Path(config['prompt_file']), ... }
        # But we need to map the output_file_paths keys to our expected structure
        
        # For generate command, construct_paths returns these in output_file_paths:
        # - 'output' or 'code_file' for the generated code
        # For other commands, we need to construct the full set of paths
        
        # Get the code file path from output_file_paths
        code_path = output_file_paths.get('output', output_file_paths.get('code_file', ''))
        if not code_path:
            # Fallback to constructing from basename
            extension = get_extension(language)
            code_path = f"{basename}.{extension}"
        
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
                _, _, example_output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path, "code_file": code_path},
                    force=True, quiet=True, command="example", command_options={}
                )
                example_path = Path(example_output_paths.get('output', f"{basename}_example.{get_extension(language)}"))
                
                # Get test path using test command  
                _, _, test_output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path, "code_file": code_path},
                    force=True, quiet=True, command="test", command_options={}
                )
                test_path = Path(test_output_paths.get('output', f"test_{basename}.{get_extension(language)}"))
                
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
                _, _, example_output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path},
                    force=True, quiet=True, command="example", command_options={}
                )
                example_path = Path(example_output_paths.get('output', f"{basename}_example.{get_extension(language)}"))
                
                _, _, test_output_paths, _ = construct_paths(
                    input_file_paths={"prompt_file": prompt_path},
                    force=True, quiet=True, command="test", command_options={}
                )
                test_path = Path(test_output_paths.get('output', f"test_{basename}.{get_extension(language)}"))
                
            except Exception:
                # Final fallback to deriving from code path if all else fails
                code_path_obj = Path(code_path)
                code_dir = code_path_obj.parent
                code_stem = code_path_obj.stem
                code_ext = code_path_obj.suffix
                example_path = code_dir / f"{code_stem}_example{code_ext}"
                test_path = code_dir / f"test_{code_stem}{code_ext}"
        
        return {
            'prompt': Path(prompt_path),
            'code': Path(code_path),
            'example': example_path,
            'test': test_path
        }
        
    except Exception as e:
        # Fallback to simple naming if construct_paths fails
        extension = get_extension(language)
        return {
            'prompt': Path(prompts_dir) / f"{basename}_{language}.prompt",
            'code': Path(f"{basename}.{extension}"),
            'example': Path(f"{basename}_example.{extension}"),
            'test': Path(f"test_{basename}.{extension}")
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
    fingerprint_file = meta_dir / f"{basename}_{language}.json"
    
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
            test_hash=data.get('test_hash')
        )
    except (json.JSONDecodeError, KeyError, IOError):
        return None


def read_run_report(basename: str, language: str) -> Optional[RunReport]:
    """Reads and validates the JSON run report file."""
    meta_dir = get_meta_dir()
    meta_dir.mkdir(parents=True, exist_ok=True)
    run_report_file = meta_dir / f"{basename}_{language}_run.json"
    
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
            coverage=data['coverage']
        )
    except (json.JSONDecodeError, KeyError, IOError):
        return None


def calculate_current_hashes(paths: Dict[str, Path]) -> Dict[str, Optional[str]]:
    """Computes the hashes for all current files on disk."""
    # Return hash keys that match what the fingerprint expects
    return {
        f"{file_type}_hash": calculate_sha256(file_path)
        for file_type, file_path in paths.items()
    }


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


def _is_workflow_complete(paths: Dict[str, Path], skip_tests: bool = False, skip_verify: bool = False) -> bool:
    """
    Check if workflow is complete considering skip flags.
    
    Args:
        paths: Dict mapping file types to their expected Path objects
        skip_tests: If True, test files are not required for completion
        skip_verify: If True, verification operations are not required
    
    Returns:
        True if all required files exist for the current workflow configuration
    """
    required_files = ['code', 'example']
    
    if not skip_tests:
        required_files.append('test')
        
    return all(paths[f].exists() for f in required_files)


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


def sync_determine_operation(basename: str, language: str, target_coverage: float, budget: float = 10.0, log_mode: bool = False, prompts_dir: str = "prompts", skip_tests: bool = False, skip_verify: bool = False) -> SyncDecision:
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
        return _perform_sync_analysis(basename, language, target_coverage, budget, prompts_dir, skip_tests, skip_verify)
    else:
        # Normal exclusive locking for actual operations
        with SyncLock(basename, language) as lock:
            return _perform_sync_analysis(basename, language, target_coverage, budget, prompts_dir, skip_tests, skip_verify)


def _perform_sync_analysis(basename: str, language: str, target_coverage: float, budget: float, prompts_dir: str = "prompts", skip_tests: bool = False, skip_verify: bool = False) -> SyncDecision:
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
    
    run_report = read_run_report(basename, language)
    if run_report:
        # Check test failures first (higher priority than exit code)
        if run_report.tests_failed > 0:
            return SyncDecision(
                operation='fix',
                reason=f'Test failures detected: {run_report.tests_failed} failed tests',
                details={'tests_failed': run_report.tests_failed},
                estimated_cost=1.5,
                confidence=0.90
            )
        
        # Then check for runtime crashes (only if no test failures)
        if run_report.exit_code != 0:
            # Check if this was from a crash fix that needs verification
            if fingerprint and fingerprint.command == 'crash':
                return SyncDecision(
                    operation='verify',
                    reason='Previous crash was fixed - verify example runs correctly',
                    details={'previous_command': 'crash', 'previous_exit_code': run_report.exit_code},
                    estimated_cost=0.7,
                    confidence=0.90
                )
            else:
                return SyncDecision(
                    operation='crash',
                    reason='Runtime error detected in last run',
                    details={'exit_code': run_report.exit_code},
                    estimated_cost=2.0,
                    confidence=0.95
                )
        
        if run_report.coverage < target_coverage:
            if skip_tests:
                # When tests are skipped but coverage is low, consider workflow complete
                # since we can't improve coverage without running tests
                return SyncDecision(
                    operation='all_synced',
                    reason=f'Coverage {run_report.coverage:.1f}% below target {target_coverage:.1f}% but tests skipped',
                    details={'current_coverage': run_report.coverage, 'target_coverage': target_coverage, 'tests_skipped': True},
                    estimated_cost=0.0,
                    confidence=0.90
                )
            else:
                return SyncDecision(
                    operation='test',
                    reason=f'Coverage {run_report.coverage:.1f}% below target {target_coverage:.1f}%',
                    details={'current_coverage': run_report.coverage, 'target_coverage': target_coverage},
                    estimated_cost=1.0,
                    confidence=0.85
                )
    
    # 2. Analyze File State
    paths = get_pdd_file_paths(basename, language, prompts_dir)
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
                    details={'prompt_path': str(paths['prompt'])},
                    estimated_cost=0.5,
                    confidence=0.80
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='New prompt ready for code generation',
                    details={'prompt_path': str(paths['prompt'])},
                    estimated_cost=1.0,
                    confidence=0.90
                )
        else:
            return SyncDecision(
                operation='nothing',
                reason='No prompt file and no history - nothing to do',
                details={},
                estimated_cost=0.0,
                confidence=1.0
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
        if _is_workflow_complete(paths, skip_tests, skip_verify):
            return SyncDecision(
                operation='nothing',
                reason=f'All required files synchronized (skip_tests={skip_tests}, skip_verify={skip_verify})',
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
        
        # Some files are missing but no changes detected
        if not paths['code'].exists():
            if paths['prompt'].exists():
                prompt_content = paths['prompt'].read_text(encoding='utf-8', errors='ignore')
                if check_for_dependencies(prompt_content):
                    return SyncDecision(
                        operation='auto-deps',
                        reason='Missing code file, prompt has dependencies',
                        details={'prompt_path': str(paths['prompt'])},
                        estimated_cost=0.5,
                        confidence=0.80
                    )
                else:
                    return SyncDecision(
                        operation='generate',
                        reason='Missing code file - generate from prompt',
                        details={'prompt_path': str(paths['prompt'])},
                        estimated_cost=1.0,
                        confidence=0.90
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
                    details={'changed_file': 'prompt'},
                    estimated_cost=0.5,
                    confidence=0.85
                )
            else:
                return SyncDecision(
                    operation='generate',
                    reason='Prompt changed - regenerate code',
                    details={'changed_file': 'prompt'},
                    estimated_cost=1.0,
                    confidence=0.90
                )
        
        elif change == 'code':
            return SyncDecision(
                operation='update',
                reason='Code changed - update prompt to reflect changes',
                details={'changed_file': 'code'},
                estimated_cost=0.8,
                confidence=0.85
            )
        
        elif change == 'test':
            return SyncDecision(
                operation='test',
                reason='Test changed - run new tests',
                details={'changed_file': 'test'},
                estimated_cost=0.5,
                confidence=0.80
            )
        
        elif change == 'example':
            return SyncDecision(
                operation='verify',
                reason='Example changed - verify new example',
                details={'changed_file': 'example'},
                estimated_cost=0.7,
                confidence=0.80
            )
    
    else:
        # Complex Changes (Multiple Files Modified / Conflicts)
        return SyncDecision(
            operation='analyze_conflict',
            reason='Multiple files changed - requires conflict analysis',
            details={'changed_files': changes},
            estimated_cost=2.0,
            confidence=0.70
        )
    
    # Fallback - should not reach here normally
    return SyncDecision(
        operation='nothing',
        reason='No clear operation determined',
        details={'fingerprint_exists': fingerprint is not None, 'changes': changes},
        estimated_cost=0.0,
        confidence=0.50
    )


def analyze_conflict_with_llm(basename: str, language: str, fingerprint: Fingerprint, changed_files: List[str], prompts_dir: str = "prompts") -> SyncDecision:
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
                details={'error': 'Template not available'},
                estimated_cost=0.0,
                confidence=0.0
            )
        
        # 2. Gather file paths and diffs
        paths = get_pdd_file_paths(basename, language, prompts_dir)
        
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
                    details={'llm_response': llm_result, 'changed_files': changed_files},
                    estimated_cost=response.get('cost', 0.0),
                    confidence=confidence
                )
            
            # Extract operation and details
            operation = llm_result['next_operation']
            reason = llm_result['reason']
            merge_strategy = llm_result.get('merge_strategy', {})
            follow_up_operations = llm_result.get('follow_up_operations', [])
            
            return SyncDecision(
                operation=operation,
                reason=f"LLM analysis: {reason}",
                details={
                    'llm_response': llm_result,
                    'changed_files': changed_files,
                    'merge_strategy': merge_strategy,
                    'follow_up_operations': follow_up_operations
                },
                estimated_cost=response.get('cost', 0.0),
                confidence=confidence,
                prerequisites=follow_up_operations
            )
            
        except (json.JSONDecodeError, ValueError, KeyError) as e:
            # Invalid LLM response - fallback to manual merge
            return SyncDecision(
                operation='fail_and_request_manual_merge',
                reason=f'Invalid LLM response: {e} - manual merge required',
                details={'error': str(e), 'raw_response': response.get('result', ''), 'changed_files': changed_files},
                estimated_cost=response.get('cost', 0.0),
                confidence=0.0
            )
    
    except Exception as e:
        # Any other error - fallback to manual merge
        return SyncDecision(
            operation='fail_and_request_manual_merge',
            reason=f'Error during LLM analysis: {e} - manual merge required',
            details={'error': str(e), 'changed_files': changed_files},
            estimated_cost=0.0,
            confidence=0.0
        )


if __name__ == "__main__":
    # Example usage
    if len(sys.argv) != 3:
        print("Usage: python sync_determine_operation.py <basename> <language>")
        sys.exit(1)
    
    basename = sys.argv[1]
    language = sys.argv[2]
    
    decision = sync_determine_operation(basename, language, target_coverage=90.0)
    
    print(f"Operation: {decision.operation}")
    print(f"Reason: {decision.reason}")
    print(f"Estimated Cost: ${decision.estimated_cost:.2f}")
    print(f"Confidence: {decision.confidence:.2f}")
    if decision.details:
        print(f"Details: {json.dumps(decision.details, indent=2)}")
