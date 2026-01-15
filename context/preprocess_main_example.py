import click
from pathlib import Path
from pdd.preprocess_main import preprocess_main

@click.command()
@click.option(
    "--prompt-file",
    required=True,
    type=click.Path(exists=True),
    help="Path to the prompt file to preprocess.",
)
@click.option(
    "--output",
    default=None,
    help="Optional path to save the preprocessed prompt. Defaults to None."
)
@click.option(
    "--xml",
    is_flag=True,
    default=False,
    help="If set, insert XML delimiters for better structure."
)
@click.option(
    "--recursive",
    is_flag=True,
    default=False,
    help="If set, recursively preprocess all prompt files referenced in 'prompt_file'."
)
@click.option(
    "--double",
    is_flag=True,
    default=False,
    help="If set, double curly brackets in the prompt."
)
@click.option(
    "--exclude",
    multiple=True,
    help="List of keys to exclude from curly bracket doubling. Specify multiple with repeated --exclude."
)
@click.option(
    "--pdd-tags",
    is_flag=True,
    default=False,
    help="Inject PDD metadata tags from architecture.json before preprocessing."
)
@click.option(
    "--verbose",
    is_flag=True,
    default=False,
    help="Enable verbose logging for XML tagging if '--xml' is used."
)
@click.pass_context
def cli(ctx, prompt_file: Path, output: str, xml: bool, recursive: bool, double: bool, exclude: list, pdd_tags: bool, verbose: bool):
    """
    Example CLI command demonstrating usage of 'preprocess_main'.

    This command reads the prompt file specified by --prompt-file, optionally applies XML tagging,
    and writes the resulting preprocessed prompt to --output. Curly brackets can be doubled with --double,
    and certain keys can be excluded via --exclude. PDD metadata tags can be injected from
    architecture.json using --pdd-tags.
    """
    try:
        # Prepare the ctx.obj dictionary for preprocess_main usage
        # (In real usage, you might pull these from environment or config.)
        ctx.ensure_object(dict)
        ctx.obj["strength"] = 0.5
        ctx.obj["temperature"] = 0.0
        ctx.obj["verbose"] = verbose

        # Call the main preprocessing function
        processed_prompt, total_cost, model_name = preprocess_main(
            ctx=ctx,
            prompt_file=prompt_file,
            output=output,
            xml=xml,
            recursive=recursive,
            double=double,
            exclude=list(exclude),
            pdd_tags=pdd_tags,
        )

        # Display final results
        click.echo("Preprocessing completed!")
        click.echo(f"Processed prompt: {processed_prompt}")
        click.echo(f"Total cost: {total_cost}")
        click.echo(f"Model name: {model_name}")

    except Exception as e:
        click.echo(f"An error occurred during preprocessing: {str(e)}", err=True)

if __name__ == "__main__":
    cli()