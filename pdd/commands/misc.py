"""
Miscellaneous commands (preprocess).
"""
import click
from typing import Optional, Tuple

from ..preprocess_main import preprocess_main
from ..core.errors import handle_error

@click.command("preprocess")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the preprocessed prompt file (file or directory).",
)
@click.option(
    "--xml",
    is_flag=True,
    default=False,
    help="Insert XML delimiters for structure (minimal preprocessing).",
)
@click.option(
    "--recursive",
    is_flag=True,
    default=False,
    help="Recursively preprocess includes.",
)
@click.option(
    "--double",
    is_flag=True,
    default=False,
    help="Double curly brackets.",
)
@click.option(
    "--exclude",
    multiple=True,
    default=None,
    help="List of keys to exclude from curly bracket doubling.",
)
@click.pass_context
# No @track_cost as preprocessing is local, but return dummy tuple for callback
def preprocess(
    ctx: click.Context,
    prompt_file: str,
    output: Optional[str],
    xml: bool,
    recursive: bool,
    double: bool,
    exclude: Optional[Tuple[str, ...]],
) -> Optional[Tuple[str, float, str]]:
    """Preprocess a prompt file to prepare it for LLM use."""
    try:
        # Since preprocess is a local operation, we don't track cost
        # But we need to return a tuple in the expected format for result callback
        result = preprocess_main(
            ctx=ctx,
            prompt_file=prompt_file,
            output=output,
            xml=xml,
            recursive=recursive,
            double=double,
            exclude=list(exclude) if exclude else [],
        )
        
        # Handle the result from preprocess_main
        if result is None:
            # If preprocess_main returns None, still return a dummy tuple for the callback
            return "", 0.0, "local"
        else:
            # Unpack the return value from preprocess_main
            processed_prompt, total_cost, model_name = result
            return processed_prompt, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "preprocess", ctx.obj.get("quiet", False))
        return None
