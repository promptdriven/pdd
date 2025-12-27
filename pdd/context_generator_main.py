from __future__ import annotations
import ast
import asyncio
import json
import os
import sys
from pathlib import Path
from typing import Optional, Tuple, Dict, Any
import click
import httpx
from rich.console import Console
from rich.panel import Panel
from .construct_paths import construct_paths
from .context_generator import context_generator
from .core.cloud import CloudConfig
# get_jwt_token imports removed - using CloudConfig.get_jwt_token() instead
from .preprocess import preprocess
from . import DEFAULT_STRENGTH, DEFAULT_TEMPERATURE

console = Console()
CLOUD_TIMEOUT_SECONDS = 400.0

def _validate_and_fix_python_syntax(code: str, quiet: bool) -> str:
    try:
        ast.parse(code)
        return code
    except SyntaxError:
        if not quiet:
            console.print("[yellow]Warning: Generated code has syntax errors. Attempting to fix...[/yellow]")
    lines = code.splitlines()
    json_markers = ['"explanation":', '"focus":', '"description":', '"code":', '"filename":']
    cut_index = -1
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()
        if any(marker in line for marker in json_markers) or line == "}" or line == "},":
            cut_index = i
    if cut_index != -1:
        candidate = "\n".join(lines[:cut_index])
        try:
            ast.parse(candidate)
            if not quiet:
                console.print("[green]Fix successful: Removed trailing metadata.[/green]")
            return candidate
        except SyntaxError:
            pass
    low = 0
    high = cut_index if cut_index != -1 else len(lines)
    valid_len = 0
    while low < high:
        mid = (low + high + 1) // 2
        candidate = "\n".join(lines[:mid])
        try:
            ast.parse(candidate)
            valid_len = mid
            low = mid
        except SyntaxError:
            high = mid - 1
    for i in range(len(lines), max(0, len(lines) - 50), -1):
        candidate = "\n".join(lines[:i])
        try:
            ast.parse(candidate)
            if not quiet:
                console.print("[green]Fix successful: Truncated invalid tail content.[/green]")
            return candidate
        except SyntaxError:
            continue
    if not quiet:
        console.print("[red]Fix failed: Could not automatically repair syntax.[/red]")
    return code

async def _run_cloud_generation(prompt_content: str, code_content: str, language: str, strength: float, temperature: float, verbose: bool, pdd_env: str) -> Tuple[Optional[str], float, str]:
    try:
        processed_prompt = preprocess(prompt_content, recursive=True, double_curly_brackets=False)
    except Exception as e:
        return None, 0.0, f"Preprocessing failed: {e}"
    # Use CloudConfig.get_jwt_token() which checks PDD_JWT_TOKEN first
    token = CloudConfig.get_jwt_token(verbose=verbose)
    if not token:
        return None, 0.0, "Failed to obtain JWT token."
    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}
    payload = {"promptContent": processed_prompt, "codeContent": code_content, "language": language, "strength": strength, "temperature": temperature, "verbose": verbose}
    async with httpx.AsyncClient(timeout=CLOUD_TIMEOUT_SECONDS) as client:
        try:
            cloud_url = CloudConfig.get_endpoint_url("generateExample")
            response = await client.post(cloud_url, json=payload, headers=headers)
            response.raise_for_status()
            data = response.json()
            generated_code = data.get("generatedExample", "")
            total_cost = float(data.get("totalCost", 0.0))
            model_name = data.get("modelName", "cloud-model")
            if not generated_code:
                return None, 0.0, "Cloud function returned empty code."
            return generated_code, total_cost, model_name
        except Exception as e:
            return None, 0.0, f"Cloud error: {e}"

def context_generator_main(ctx: click.Context, prompt_file: str, code_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    try:
        input_file_paths = {"prompt_file": prompt_file, "code_file": code_file}
        command_options = {"output": output}
        resolved_config, input_strings, output_file_paths, language = construct_paths(input_file_paths=input_file_paths, force=ctx.obj.get('force', False), quiet=ctx.obj.get('quiet', False), command="example", command_options=command_options, context_override=ctx.obj.get('context'), confirm_callback=ctx.obj.get('confirm_callback'))
        prompt_content = input_strings.get("prompt_file", "")
        code_content = input_strings.get("code_file", "")
        if output and not output.endswith("/") and not Path(output).is_dir():
            resolved_output = output
        else:
            resolved_output = output_file_paths.get("output")
        is_local = ctx.obj.get("local", False)
        strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = ctx.obj.get('temperature', DEFAULT_TEMPERATURE)
        verbose = ctx.obj.get('verbose', False)
        quiet = ctx.obj.get('quiet', False)
        pdd_env = os.environ.get("PDD_ENV", "local")
        generated_code = None
        total_cost = 0.0
        model_name = ""
        if not is_local:
            try:
                generated_code, total_cost, model_name = asyncio.run(_run_cloud_generation(prompt_content, code_content, language, strength, temperature, verbose, pdd_env))
            except Exception:
                generated_code = None
            if generated_code is None:
                if not quiet:
                    console.print("[yellow]Cloud execution failed. Falling back to local.[/yellow]")
                is_local = True
        if is_local:
            source_file_path = str(Path(code_file).resolve())
            example_file_path = str(Path(resolved_output).resolve()) if resolved_output else ""
            module_name = Path(code_file).stem
            generated_code, total_cost, model_name = context_generator(code_module=code_content, prompt=prompt_content, language=language, strength=strength, temperature=temperature, verbose=not quiet, source_file_path=source_file_path, example_file_path=example_file_path, module_name=module_name, time=ctx.obj.get('time'))
        if not generated_code:
            raise click.UsageError("Example generation failed, no code produced.")
        if language and language.lower() == "python":
            generated_code = _validate_and_fix_python_syntax(generated_code, quiet)
        if resolved_output:
            out_path = Path(resolved_output)
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(generated_code, encoding="utf-8")
        if not quiet:
            console.print("[bold green]Example generation completed successfully.[/bold green]")
            console.print(f"[bold]Model used:[/bold] {model_name}")
            console.print(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
        return generated_code, total_cost, model_name
    except Exception as e:
        if not ctx.obj.get('quiet', False):
            console.print(f"[bold red]Error:[/bold red] {str(e)}")
        raise e