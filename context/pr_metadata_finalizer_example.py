import os
import sys
import subprocess
from pathlib import Path

# Import the functions from the pdd module
from pdd.pr_metadata_finalizer import (
    finalize_pr_metadata,
    stage_paths_scoped,
    is_pdd_meta_artifact
)


def main():
    """
    Example script demonstrating the usage of the PR metadata finalizer functions.
    These functions are typically used during CLI PR creation/update flows to ensure
    PDD fingerprints are up to date and correctly staged.
    """
    print("--- PDD PR Metadata Finalizer Example ---\n")

    # 1. Setup a dummy repository in the output directory
    repo_root = Path("./output/example_repo").resolve()
    repo_root.mkdir(parents=True, exist_ok=True)
    
    # Initialize a git repository so git commands inside the module don't fail
    subprocess.run(["git", "init"], cwd=repo_root, capture_output=True, check=False)

    # 2. Demonstrate is_pdd_meta_artifact
    # This function checks if a given path falls under the '.pdd/meta' directory.
    # Input: path (str) - The file path to check.
    # Output: (bool) - True if the path is a metadata artifact.
    print("Testing 'is_pdd_meta_artifact':")
    sample_paths = [
        ".pdd/meta/my_module_python.json",
        "src/main.py",
        "./.pdd/meta/another_module.json"
    ]
    for path_str in sample_paths:
        is_meta = is_pdd_meta_artifact(path_str)
        print(f"  '{path_str}' -> {is_meta}")
    print()

    # 3. Create a dummy file to stage
    dummy_file = repo_root / "example_code.py"
    dummy_file.write_text("print('Hello, world!')\n")

    # 4. Demonstrate stage_paths_scoped
    # Stages precise pathspecs via git, with an option to exclude metadata files.
    # Inputs:
    #   - repo_root: Path to the git repository
    #   - paths: Iterable of file paths to stage
    #   - force: boolean to use 'git add -f' (default: False)
    #   - exclude_pdd_meta: boolean to skip staging '.pdd/meta' files (default: True)
    # Outputs:
    #   - Tuple[bool, str]: Success boolean and error message (if any)
    print("Testing 'stage_paths_scoped':")
    ok, error_msg = stage_paths_scoped(
        repo_root=repo_root, 
        paths=["example_code.py"], 
        force=False, 
        exclude_pdd_meta=True
    )
    if ok:
        print("  Successfully staged 'example_code.py'.")
    else:
        print(f"  Failed to stage: {error_msg}")
    print()

    # 5. Demonstrate finalize_pr_metadata
    # Detects changed files, generates/verifies PDD fingerprints for touched modules,
    # and stages the resulting fingerprint JSON files.
    # Inputs:
    #   - repo_root: Path to the git repository
    #   - changed_paths: Iterable of changed files (if None, discovers via git status)
    #   - stage: boolean indicating whether to stage the resulting fingerprint files
    # Outputs:
    #   - PRMetadataFinalizationResult: Contains success status, touched modules, and a message.
    print("Testing 'finalize_pr_metadata':")
    result = finalize_pr_metadata(
        repo_root=repo_root, 
        changed_paths=["example_code.py"],
        stage=True
    )
    
    print(f"  Success: {result.ok}")
    print(f"  Message: {result.message}")
    print(f"  Touched Modules: {result.touched_modules}")
    print(f"  Metadata Paths Staged: {result.metadata_paths}")


if __name__ == "__main__":
    main()