import os
from pdd.summarize_directory import summarize_directory


def main() -> None:
    """
    Example usage of summarize_directory module
    
    This example will:
    1. Create a sample CSV file with existing summaries
    2. Summarize Python files in a directory
    3. Print the results
    """
    # Example existing CSV content (uses content_hash for cache invalidation)
    existing_csv = """full_path,file_summary,content_hash
context/change_example.py,"This is an old summary",a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2
context/click_example.py,"This is an old summary",f6e5d4c3b2a1f6e5d4c3b2a1f6e5d4c3b2a1f6e5d4c3b2a1f6e5d4c3b2a1f6e5"""

    try:
        # Call summarize_directory
        # directory_path: Path with wildcard to find files
        # strength: 0.7 (higher values use more capable but expensive models)
        # temperature: 0.5 (lower values make output more deterministic)
        # verbose: True to see detailed progress
        # csv_file: Optional existing CSV content
        csv_output, total_cost, model_name = summarize_directory(
            directory_path="context/c*.py",
            strength=0.5,
            temperature=0.0,
            verbose=True,
            csv_file=existing_csv
        )

        # Print results
        print("\nGenerated CSV content:")
        print(csv_output)
        print(f"\nTotal cost: ${total_cost:.4f}")  # Cost in USD
        print(f"Model used: {model_name}")

        # Ensure the output directory exists
        output_dir = 'output'
        os.makedirs(output_dir, exist_ok=True)
        
        # Define the output file path
        output_file_path = os.path.join(output_dir, 'output.csv')

        # save csv file to the output directory
        with open(output_file_path, 'w') as file:
            file.write(csv_output)

    except Exception as e:
        print(f"An error occurred: {e}")


if __name__ == "__main__":
    main()
