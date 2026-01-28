def _commit_and_push(
    cwd: Path,
    issue_number: int,
    issue_title: str,
    initial_file_hashes: Dict[str, Optional[str]],
    quiet: bool = False
) -> Tuple[bool, str]:
    """
    Commits only files that changed during the workflow and pushes.

    Uses hash comparison to detect actual content changes, avoiding
    staging pre-existing modified/untracked files.

    The PR was already created by `pdd bug`, so pushing
    automatically updates it.

    Args:
        cwd: Working directory
        issue_number: GitHub issue number
        issue_title: Issue title for commit message
        initial_file_hashes: File hashes from before workflow started
        quiet: Suppress output

    Returns:
        (success, message)
    """
    # Get current file hashes
    current_hashes = _get_file_hashes(cwd)

    # Find files that changed during workflow
    files_to_commit: List[str] = []
    for filepath, current_hash in current_hashes.items():
        if filepath not in initial_file_hashes:
            # New file created during workflow
            files_to_commit.append(filepath)
        elif initial_file_hashes[filepath] != current_hash:
            # Content changed during workflow
            files_to_commit.append(filepath)

    # Check for unpushed commits
    unpushed_commits_count = subprocess.run(
        ["git", "rev-list", "--count", "HEAD", "^origin/main"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    
    if unpushed_commits_count.returncode == 0 and int(unpushed_commits_count.stdout.strip()) > 0:
        # There are unpushed commits
        if not files_to_commit:
            return True, "No changes to commit, but there are unpushed commits."

        # Stage only workflow-changed files
        for filepath in files_to_commit:
            stage_result = subprocess.run(
                ["git", "add", filepath],
                cwd=cwd,
                capture_output=True,
                text=True
            )
            if stage_result.returncode != 0:
                return False, f"Failed to stage {filepath}: {stage_result.stderr}"

        # Commit with message referencing issue
        commit_msg = f"fix: {issue_title}\n\nFixes #{issue_number}"
        commit_result = subprocess.run(
            ["git", "commit", "-m", commit_msg],
            cwd=cwd,
            capture_output=True,
            text=True
        )
        if commit_result.returncode != 0:
            return False, f"Failed to commit: {commit_result.stderr}"

        # Push to remote (branch already exists from pdd bug)
        push_result = subprocess.run(
            ["git", "push"],
            cwd=cwd,
            capture_output=True,
            text=True
        )

        if push_result.returncode == 0:
            return True, f"Committed and pushed {len(files_to_commit)} file(s)"
        else:
            return False, f"Push failed: {push_result.stderr}"

    return True, "No changes to commit and no unpushed commits."