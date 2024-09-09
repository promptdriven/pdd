from pdd.process_csv_change import process_csv_change

# Example usage
csv_file: str = "/Users/gregtanaka/Documents/PDD/staging/regression/detect_results.csv"
strength: float = 0.7
temperature: float = 0.5
code_directory: str = "pdd"
language: str = "python"
extension: str = ".py"
budget: float = 10.0  # Maximum budget in dollars

try:
    success, modified_prompts, total_cost, model_name = process_csv_change(
        csv_file, strength, temperature, code_directory, language, extension, budget
    )

    if success:
        print(f"Changes applied successfully. Total cost: ${total_cost:.2f}")
        print(f"Model used: {model_name}")
        for item in modified_prompts:
            for file_name, prompt in item.items():
                print(f"Modified prompt for {file_name}:")
                print(prompt)
                print("---")
    else:
        print("Some errors occurred during the process. Check the console output for details.")
except FileNotFoundError:
    print("The specified CSV file or code directory was not found.")
except Exception as e:
    print(f"An unexpected error occurred: {e}")