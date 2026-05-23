from __future__ import annotations

import ast
import asyncio
from pathlib import Path
from typing import Optional, Tuple

import click
from rich.console import Console
from rich.panel import Panel

from .construct_paths import construct_paths, BUILTIN_EXT_MAP
from .context_generator import context_generator
from .preprocess import preprocess
from .core.cloud import CloudConfig
from . import DEFAULT_STRENGTH

console = Console()


def _validate_and_fix_python_syntax(example_code: str, quiet: bool = False) -> str:
    """
    Validate that ``example_code`` parses as Python; if not, attempt a fix.

    Common LLM failure mode: trailing JSON metadata garbage (lines like
    ``"explanation":``, ``"focus":``, etc.) appended to the end of the file.
    Strategy: binary-search the trailing lines to find the longest prefix that
    parses with ``ast.parse``.

    Returns the fixed code, or the original ``example_code`` if no fix
    improves parseability.
    """
    try:
        ast.parse(example_code)
        return example_code
    except SyntaxError:
        if not quiet:
            console.print(
                "[bold yellow]Warning:[/bold yellow] Syntax error detected in generated "
                "Python code. Attempting to strip trailing JSON garbage..."
            )

    lines = example_code.split("\n")
    low = 0
    high = len(lines)
    best_valid_lines = 0

    while low <= high:
        mid = (low + high) // 2
        test_code = "\n".join(lines[:mid])
        try:
            ast.parse(test_code)
            best_valid_lines = mid
            low = mid + 1
        except SyntaxError:
            high = mid - 1

    if best_valid_lines > 0 and best_valid_lines < len(lines):
        fixed_code = "\n".join(lines[:best_valid_lines])
        if not quiet:
            console.print(
                "[bold green]Successfully stripped trailing garbage from Python output.[/bold green]"
            )
        return fixed_code

    # No improvement possible — preserve original so caller can inspect it.
    if not quiet:
        console.print(
            "[bold yellow]Could not auto-fix syntax error. Saving code as-is.[/bold yellow]"
        )
    return example_code


async def _run_cloud_generation(
    token: str,
    prompt_text: str,
    code_content: str,
    language: str,
    strength: float,
    temperature: float,
    verbose: bool,
) -> Tuple[str, float, str]:
    """
    Call the cloud example-generation endpoint.

    The JWT ``token`` must be obtained BEFORE entering ``asyncio.run`` and
    passed in as a parameter — see CloudConfig.get_jwt_token nested-event-loop
    notes in the spec.
    """
    import httpx

    endpoint = CloudConfig.get_endpoint_url("generateExample")
    processed_prompt = preprocess(prompt_text, recursive=True, double_curly_brackets=False)

    if verbose:
        console.print(Panel(processed_prompt[:500] + "...", title="Preprocessed Prompt for Cloud"))
        console.print(f"Attempting cloud example generation at {endpoint}...")

    payload = {
        "promptContent": processed_prompt,
        "codeContent": code_content,
        "language": language,
        "strength": strength,
        "temperature": temperature,
        "verbose": verbose,
    }

    headers = {"Authorization": f"Bearer {token}", "Content-Type": "application/json"}

    async with httpx.AsyncClient(timeout=400.0) as client:
        response = await client.post(endpoint, json=payload, headers=headers)

        if response.status_code == 401:
            raise click.UsageError("Authentication failed (401). Please login again.")
        elif response.status_code == 402:
            raise click.UsageError("Insufficient credits (402).")
        elif response.status_code == 403:
            raise click.UsageError("Access denied (403).")

        response.raise_for_status()
        data = response.json()

        generated_code = data.get("generatedExample", "")
        if not generated_code:
            raise ValueError("Cloud returned empty code content.")

        total_cost = float(data.get("totalCost", 0.0))
        model_name = data.get("modelName", "cloud-model")

        if verbose:
            console.print(
                Panel(
                    f"Model: {model_name}\nCost: ${total_cost:.6f}",
                    title="Cloud Success",
                    style="green",
                )
            )

        return generated_code, total_cost, model_name


def context_generator_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    output: Optional[str],
    format: Optional[str] = None,
) -> Tuple[str, float, str]:
    """
    CLI wrapper that generates example code from a prompt and code file.

    Honors user-supplied ``--output`` extensions per issue #1148: when
    ``format`` is ``None`` the user's path is used verbatim; otherwise the
    extension rules described in the spec apply.

    Args:
        ctx: Click context (uses ``ctx.obj`` for verbose/strength/temperature/
            time/force/quiet/local/context/confirm_callback).
        prompt_file: Path to the .prompt file that generated ``code_file``.
        code_file: Path to the existing code file.
        output: Optional path for the generated example. ``None`` →
            default naming convention computed by ``construct_paths``.
        format: Optional ``"code"`` or ``"md"`` constraint on the output
            extension. ``None`` means "honor user's --output verbatim".

    Returns:
        (example_code, total_cost, model_name)
    """
    obj = ctx.obj or {}
    verbose = obj.get("verbose", False)
    quiet = obj.get("quiet", False)
    force = obj.get("force", False)
    local = obj.get("local", False)
    strength = obj.get("strength", DEFAULT_STRENGTH if isinstance(DEFAULT_STRENGTH, float) else 0.5)
    if not isinstance(strength, (int, float)):
        strength = 0.5
    temperature = obj.get("temperature", 0.0)
    # `time` may be None — preserved here per spec note that `time` has no default.
    time_param = obj.get("time")
    context_override = obj.get("context")
    confirm_callback = obj.get("confirm_callback")

    input_file_paths = {
        "prompt_file": prompt_file,
        "code_file": code_file,
    }

    # Forward CLI options that construct_paths consumes (e.g. for default-path
    # computation and format-aware extension selection).
    command_options: dict = {}
    if output is not None:
        command_options["output"] = output
    if format is not None:
        command_options["format"] = format

    try:
        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=force,
            quiet=quiet,
            command="example",
            command_options=command_options,
            context_override=context_override,
            confirm_callback=confirm_callback,
        )
    except Exception as e:
        if not quiet:
            console.print(f"[bold red]Error resolving paths:[/bold red] {e}")
        raise

    prompt_content = input_strings.get("prompt_file", "")
    code_content = input_strings.get("code_file", "")

    # --- Resolve the final output path -------------------------------------
    default_output_path = output_file_paths.get("output", "") if output_file_paths else ""

    if output is None or output.endswith("/") or (Path(output).exists() and Path(output).is_dir()):
        # Use default path computed by construct_paths.
        final_output_path = Path(default_output_path) if default_output_path else Path("example_output.py")
    else:
        user_path = Path(output)
        if format is None:
            # Issue #1148: honor user-supplied path verbatim — no with_suffix,
            # no BUILTIN_EXT_MAP lookup. `foo.yml` stays `foo.yml`.
            final_output_path = user_path
        elif format == "md":
            # Honor .md verbatim; otherwise rewrite suffix to .md.
            if user_path.suffix == ".md":
                final_output_path = user_path
            else:
                final_output_path = user_path.with_suffix(".md")
        elif format == "code":
            # Honor any user-supplied suffix verbatim; only fall back to the
            # language-derived extension when no suffix was supplied.
            if user_path.suffix:
                final_output_path = user_path
            else:
                lang_key = (language or "python").lower()
                ext = BUILTIN_EXT_MAP.get(lang_key, f".{lang_key}")
                if not ext:
                    ext = ".py"
                final_output_path = user_path.with_suffix(ext)
        else:
            final_output_path = user_path

    source_file_path = str(Path(code_file).resolve())
    example_file_path = str(final_output_path.resolve()) if final_output_path else ""
    module_name = Path(code_file).stem

    example_code = ""
    total_cost = 0.0
    model_name = ""
    cloud_success = False

    # --- Cloud-first execution unless --local was requested ----------------
    if not local:
        token: Optional[str] = None
        try:
            # CRITICAL: get JWT BEFORE asyncio.run (see CloudConfig docs).
            token = CloudConfig.get_jwt_token(verbose=verbose)
        except click.UsageError:
            raise
        except Exception as e:
            if not quiet:
                console.print(
                    f"[bold yellow]Could not obtain auth token ({e}). "
                    "Falling back to local execution...[/bold yellow]"
                )
            token = None

        if token:
            if verbose:
                console.print("Attempting cloud example generation...")
            try:
                example_code, total_cost, model_name = asyncio.run(
                    _run_cloud_generation(
                        token=token,
                        prompt_text=prompt_content,
                        code_content=code_content,
                        language=language or "python",
                        strength=strength,
                        temperature=temperature,
                        verbose=verbose,
                    )
                )
                cloud_success = True
            except click.UsageError:
                raise
            except Exception as e:
                if not quiet:
                    console.print(
                        f"[bold yellow]Cloud generation failed ({e}). "
                        "Falling back to local execution...[/bold yellow]"
                    )
                cloud_success = False

    # --- Local fallback ----------------------------------------------------
    if not cloud_success:
        if verbose:
            console.print("Running local example generation...")
        try:
            # Try to pass the contextual path/name parameters; fall back
            # gracefully if the local context_generator signature doesn't
            # accept them.
            try:
                example_code, total_cost, model_name = context_generator(
                    code_module=code_content,
                    prompt=prompt_content,
                    language=language or "python",
                    strength=strength,
                    temperature=temperature,
                    source_file_path=source_file_path,
                    example_file_path=example_file_path,
                    module_name=module_name,
                )
            except TypeError:
                example_code, total_cost, model_name = context_generator(
                    code_module=code_content,
                    prompt=prompt_content,
                    language=language or "python",
                    strength=strength,
                    temperature=temperature,
                )
        except Exception as e:
            if not quiet:
                console.print(f"[bold red]Local generation error:[/bold red] {e}")
            raise

    if not example_code or not example_code.strip():
        raise click.UsageError("Example generation failed, no code produced.")

    # --- Optional Python syntax validation ---------------------------------
    # Skip for markdown output (format="md") — markdown is intentionally not
    # Python and would always fail ast.parse.
    if (language or "python").lower() == "python" and format != "md":
        example_code = _validate_and_fix_python_syntax(example_code, quiet=quiet)

    # --- Write output ------------------------------------------------------
    try:
        final_output_path.parent.mkdir(parents=True, exist_ok=True)
        final_output_path.write_text(example_code, encoding="utf-8")
        if not quiet:
            console.print(
                f"[bold green]Success:[/bold green] Example code written to {final_output_path}"
            )
            console.print(f"Model: {model_name} | Cost: ${total_cost:.6f}")
    except Exception as e:
        if not quiet:
            console.print(f"[bold red]Error writing output file:[/bold red] {e}")
        raise

    return example_code, total_cost, model_name
