import os
from generate_output_paths import generate_output_paths


def main() -> None:
    """
    Main function to demonstrate the usage of generate_output_paths function.
    """
    # Define the command and parameters
    command: str = "generate"
    output_locations: dict = {
        "output": "/path/to/output/directory/",
    }
    basename: str = "my_file"
    language: str = "python"  # Not used for 'generate' command, but required for consistency
    file_extension: str = "py"

    try:
        # Generate output paths
        output_paths: dict = generate_output_paths(command, output_locations, basename, language, file_extension)

        # Print the generated output paths
        print(output_paths)
    except Exception as e:
        print(f"An error occurred: {e}")


if __name__ == "__main__":
    main()