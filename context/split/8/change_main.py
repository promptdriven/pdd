@cli.command()
@click.argument('input_prompt_file', type=click.Path(exists=True), required=False)
@click.argument('input_code_file', type=click.Path(exists=True), required=False)
@click.argument('change_prompt_file', type=click.Path(exists=True), required=False)
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.option('--csv', type=click.Path(exists=True), help='Use a CSV file for the change prompts instead of a text file.')
@click.pass_context
@track_cost
def change(ctx, input_prompt_file: Optional[str], input_code_file: Optional[str], change_prompt_file: Optional[str], output: Optional[str], csv: Optional[str]) -> Tuple[str, float, str]:
    """Modify an input prompt file based on a change prompt and the corresponding input code."""
    return change_main(ctx, input_prompt_file, input_code_file, change_prompt_file, output) # This new function ('change_main') will contain all the functionality of the 'change' function and be split into a sub_prompt.