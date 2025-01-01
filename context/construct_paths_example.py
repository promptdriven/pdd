from pdd.construct_paths import construct_paths

def main() -> None:
    """
    Main function to demonstrate the usage of the construct_paths function.
    It sets up input parameters, calls the function, and handles its output.
    """
    # Define input file paths
    input_file_paths = { # Keys are the lower case version of the command inputs (e.g. "test" command would have the keys "code_file" and "prompt_file")
        "code_file": "pdd/unfinished_prompt.py",
        "prompt_file": "prompts/unfinished_prompt_python.prompt"
    }

    # Define command options
    command_options = { # This dictionary contains the command options that are passed to the construct_paths function. For instance the "test" command would have the keys "output" and "language".
        "output": None
    }

    # Call the construct_paths function
    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=False,  # Set to True to overwrite existing files
            quiet=False,  # Set to True to suppress output messages
            command="example",  # Command can be 'generate', 'test', etc.
            command_options=command_options
        )

        # Output the results
        print(f"Input Strings: {input_strings}") # This dictionary contains the contents of the input files with the same keys as input_file_paths. The construct_paths function reads the files and stores the contents in this dictionary.
        print(f"Output File Paths: {output_file_paths}")
        print(f"Language: {language}")

    except Exception as e:
        print(f"An error occurred: {e}")

    # Define input file paths
    input_file_paths = { # Keys are the lower case version of the command inputs (e.g. "test" command would have the keys "code_file" and "prompt_file")
        "prompt_file": "prompts/main_gen_prompt.prompt"
    }

    # Define command options
    command_options = { # This dictionary contains the command options that are passed to the construct_paths function. For instance the "test" command would have the keys "output" and "language".
        "output": 'pdd'
    }

    # Call the construct_paths function
    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=False,  # Set to True to overwrite existing files
            quiet=False,  # Set to True to suppress output messages
            command="generate",  # Command can be 'generate', 'test', etc.
            command_options=command_options
        )

        # Output the results
        print(f"Input Strings: {input_strings}") # This dictionary contains the contents of the input files with the same keys as input_file_paths. The construct_paths function reads the files and stores the contents in this dictionary.
        print(f"Output File Paths: {output_file_paths}")
        print(f"Language: {language}")

    except Exception as e:
        print(f"An error occurred: {e}")

    # Construct file paths
    input_file_paths = {
        "prompt_file": "output/factorial_prompt.txt",
        "code_file": "output/factorial.py",
        "program_file": "output/main.py",
        "error_file": "output/error.log"
    }
    command_options = {
        "output": "output/fixed_factorial.py",
        "output_program": "output/fixed_main.py"
    }
    input_strings, output_file_paths, _ = construct_paths(
        input_file_paths=input_file_paths,
        force=True,
        quiet=True,
        command="crash",
        command_options=command_options
    )
    # print(f"Input Strings: {input_strings}")
    print(f"Output File Paths: {output_file_paths}")

if __name__ == "__main__":
    main()