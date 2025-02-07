import sys
from typing import Tuple, Optional
import click
from rich import print as rprint

import requests   # <── Added at top level so the tests can patch pdd.code_generator_main.requests

from .construct_paths import construct_paths
from .code_generator import code_generator
from .get_jwt_token import get_jwt_token
from .preprocess import preprocess

def code_generator_main(ctx: click.Context, prompt_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """
    Main function to generate code from a prompt file.

    :param ctx: Click context containing command-line parameters.
    :param prompt_file: Path to the prompt file used to generate the code.
    :param output: Optional path to save the generated code.
    :return: A tuple containing the generated code, total cost, and model name used.
    """
    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file
        }
        command_options = {
            "output": output
        }
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="generate",
            command_options=command_options
        )

        # Load input file
        prompt_content = input_strings["prompt_file"]

        # Generate code
        strength = ctx.obj.get('strength', 0.5)
        temperature = ctx.obj.get('temperature', 0.0)
        verbose = not ctx.obj.get('quiet', False)
        local = ctx.obj.get('local', False)

        if local:
            print("Running in local mode")
            # Local execution
            generated_code, total_cost, model_name = code_generator(
                prompt_content,
                language,
                strength,
                temperature,
                verbose=verbose
            )
        else:
            # Cloud execution
            try:
                import asyncio
                import os
                # Get JWT token for cloud authentication
                jwt_token = asyncio.run(get_jwt_token(
                    firebase_api_key=os.environ.get("REACT_APP_FIREBASE_API_KEY"),
                    github_client_id=os.environ.get("GITHUB_CLIENT_ID"),
                    app_name="PDD Code Generator"
                ))
                # Call cloud code generator
                headers = {
                    "Authorization": f"Bearer {jwt_token}",
                    "Content-Type": "application/json"
                }
                # Preprocess the prompt
                processed_prompt = preprocess(prompt_content, recursive=False, double_curly_brackets=True)
                if verbose:
                    print(f"Processed prompt: {processed_prompt}")
                data = {
                    "promptContent": processed_prompt,
                    "language": language,
                    "strength": strength,
                    "temperature": temperature,
                    "verbose": verbose
                }
                response = requests.post(
                    "https://us-central1-prompt-driven-development.cloudfunctions.net/generateCode",
                    headers=headers,
                    json=data
                )
                response.raise_for_status()
                result = response.json()
                generated_code = result["generatedCode"]
                total_cost = result["totalCost"]
                model_name = result["modelName"]

            except Exception as e:
                if not ctx.obj.get('quiet', False):
                    rprint("[bold red]Cloud execution failed, falling back to local mode[/bold red]")
                generated_code, total_cost, model_name = code_generator(
                    prompt_content,
                    language,
                    strength,
                    temperature,
                    verbose=verbose
                )

        # Save results
        if output_file_paths["output"]:
            with open(output_file_paths["output"], 'w') as f:
                f.write(generated_code)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Code generation completed successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output:
                rprint(f"[bold]Code saved to:[/bold] {output_file_paths['output']}")

        return generated_code, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)