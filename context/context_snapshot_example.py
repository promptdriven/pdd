# /workspace/public-pdd/context/context_snapshot_example.py
from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import Any

# Use rich.console for all printing as per requirements
from rich.console import Console

from pdd.context_snapshot import replay_snapshot, start_snapshot_run

# Initialize the rich console for clean, formatted output
console = Console()


def run_snapshot_example() -> None:
    """Demonstrates recording an expanded prompt context snapshot and replaying it."""
    # 1. Setup workspace directories under ./output
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    evidence_root = output_dir / "evidence"
    prompt_path = output_dir / "system_prompt.md"

    # Define a mock prompt that references a secret we want to ensure gets redacted
    raw_prompt_content = (
        "You are an assistant. Use this authorization key: Bearer secret-token-123456\n"
        "Include the config: <include query='database_schema'>"
    )
    prompt_path.write_text(raw_prompt_content, encoding="utf-8")

    console.print(
        f"[bold blue]Step 1:[/bold blue] Created temporary prompt file at [yellow]{prompt_path}[/yellow]"
    )

    # 2. Start a new snapshot run
    # This generates a unique run_id and creates the snapshot storage directories.
    recorder = start_snapshot_run(
        prompt_path=prompt_path,
        evidence_root=evidence_root,
        command="pdd generate --prompt system_prompt.md",
    )
    console.print(
        f"[bold blue]Step 2:[/bold blue] Started snapshot run with ID: [green]{recorder.run_id}[/green]"
    )

    # 3. Record the prompt source
    # This automatically detects declared dynamic tags and registers redaction behaviors
    recorder.record_prompt_source(raw_prompt_content)

    # 4. Record dynamic and static context components
    # Record an include resolution
    include_file = output_dir / "schema.sql"
    include_file.write_text(
        "CREATE TABLE users (id INT, secret_api_key VARCHAR(50));",
        encoding="utf-8",
    )
    recorder.record_include(
        source_path=include_file,
        content="CREATE TABLE users (id INT, secret_api_key VARCHAR(50));",
        query="database_schema",
    )

    # Record a shell command snapshot (simulating dynamic tool output)
    recorder.record_shell(
        command="env | grep API_KEY",
        stdout="API_KEY=sk-abc123XYZ7890\nOTHER_VAR=public_value",
        stderr="",
        exit_code=0,
    )

    # Record a web page fetch snapshot
    recorder.record_web(
        url="https://api.example.com/status?token=ghp_dummyGitHubToken12345",
        content="System Status: Fully Operational",
        fetcher="httpx",
        status=200,
    )

    console.print(
        "[bold blue]Step 3:[/bold blue] Recorded simulated include, shell, and web contexts (with secrets)."
    )

    # 5. Finalize the run and generate the expanded prompt
    # In real workflows, this is the final prompt concatenated with all resolved context
    final_expanded_prompt = (
        "You are an assistant. Use this authorization key: [REDACTED]\n"
        "DATABASE SCHEMA:\n"
        "CREATE TABLE users (id INT, secret_api_key VARCHAR(50));\n"
        "SHELL OUTPUT:\nSTDOUT:\nAPI_KEY=[REDACTED]\nOTHER_VAR=public_value\n"
        "WEB CONTENT:\nSystem Status: Fully Operational"
    )

    manifest = recorder.finalize(
        expanded_prompt=final_expanded_prompt,
        prompt_text=raw_prompt_content,
        model="gpt-4o",
        provider="openai",
    )

    manifest_path = recorder.run_artifact
    console.print(
        f"[bold blue]Step 4:[/bold blue] Manifest successfully written to [yellow]{manifest_path}[/yellow]"
    )
    console.print(
        f"        Redaction Applied: [bold red]{manifest['redaction']['applied']}[/bold red]"
    )
    console.print(
        f"        Redaction Patterns: {manifest['redaction']['patterns']}"
    )

    # 6. Replay and verify the context snapshot
    # This loads the manifest, re-reads the serialized expanded prompt, and verifies the SHA-256 hash.
    console.print(
        "[bold blue]Step 5:[/bold blue] Replaying the snapshot to verify integrity..."
    )
    replay_result = replay_snapshot(manifest_path)

    console.print("\n[bold green]Replay Successful![/bold green]")
    console.print(f"Verified: [green]{replay_result['verified']}[/green]")
    console.print(f"Expected Hash: [cyan]{replay_result['expanded_sha256']}[/cyan]")
    console.print(
        f"Expanded Prompt Preview:\n---\n[dim]{replay_result['expanded_prompt'][:180]}...[/dim]\n---"
    )


if __name__ == "__main__":
    # Ensure PDD_PATH or virtual env executes normally
    run_snapshot_example()