"""Registers the pdd policy CLI command group for side-effect enforcement."""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Optional

import click

from ..policy_check import run_policy_check, PolicyResult
from ..path_resolution import get_default_resolver
from ..evidence_manifest import write_evidence_manifest

@click.group(name="policy")
def policy_group():
    """Side-effect policy enforcement group."""
    pass

@policy_group.command(name="check")
@click.argument("target", type=click.Path(exists=True, path_type=Path))
@click.option("--prompt", "prompt_path", type=click.Path(exists=True, path_type=Path), help="Explicitly specify the prompt file.")
@click.option("--json", "as_json", is_flag=True, help="Output results in JSON format.")
@click.option("--strict", is_flag=True, help="Enable strict mode.")
@click.option("--evidence", is_flag=True, help="Write findings to an evidence manifest.")
def check(target: Path, prompt_path: Optional[Path], as_json: bool, strict: bool, evidence: bool):
    """Scan files or directories for policy violations."""
    targets = [target] if target.is_file() else list(target.rglob("*.py"))
    
    results: list[PolicyResult] = []
    any_violations = False
    system_errors = False
    
    resolver = get_default_resolver()
    
    for t in targets:
        current_prompt = prompt_path
        if not current_prompt:
            # Use PathResolver for standard prompt discovery
            try:
                # heuristic: find prompt matching the code file's name
                prompt_name = f"{t.stem}_python.prompt"
                current_prompt = resolver.resolve_prompt_template(prompt_name)
            except Exception:
                current_prompt = None
        
        result = run_policy_check(t, current_prompt, strict=strict)
        results.append(result)
        if not result.passed:
            any_violations = True
            if any(i.category == "system" for i in result.issues):
                system_errors = True

    if as_json:
        output = [
            {
                "target": str(r.target_path),
                "passed": r.passed,
                "capabilities": [
                    {
                        "modal": cap.modal,
                        "text": cap.text,
                        "line": cap.line,
                        "is_must_not": cap.is_must_not,
                    }
                    for cap in r.capabilities
                ],
                "issues": [
                    {"category": i.category, "message": i.message, "line": i.line, "col": i.col}
                    for i in r.issues
                ],
            }
            for r in results
        ]
        click.echo(json.dumps(output, indent=2))
    else:
        for r in results:
            if r.passed:
                click.secho(f"PASS: {r.target_path}", fg="green")
            else:
                color = "red" if strict or any(i.category == "system" for i in r.issues) else "yellow"
                click.secho(f"FAIL: {r.target_path}", fg=color)
                for i in r.issues:
                    click.echo(f"  [{i.category}] {i.message} (line {i.line})")

    if evidence:
        # Consolidate evidence into a single manifest
        all_validation = {}
        all_outputs = []
        for r in results:
            all_validation[f"policy_{r.target_path.name}"] = "passed" if r.passed else "failed"
            all_outputs.append(r.target_path)
        
        write_evidence_manifest(
            command="pdd policy check",
            prompt_file=prompt_path, # Single prompt override or None
            output_files=all_outputs,
            validation=all_validation,
        )

    if any_violations:
        if strict or system_errors:
            sys.exit(2)
        else:
            sys.exit(1)
    
    sys.exit(0)
