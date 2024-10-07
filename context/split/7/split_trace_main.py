@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('code_line', type=int)
@click.option('--output', type=click.Path(), help='Specify where to save the trace analysis results.')
@click.pass_context
@track_cost
def trace(ctx, prompt_file: str, code_file: str, code_line: int, output: Optional[str]) -> Tuple[str, float, str]:
    """Find the associated line number between a prompt file and the generated code."""
    return trace_main(ctx, prompt_file, code_file, code_line, output) # This new function ('trace_main') will contain all the functionality of the 'trace' function and be split into a sub_prompt.