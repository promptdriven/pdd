from code_generator import code_generator

def main():
    # Define the file path, file type, and strength
    prompt_file_path = 'path/to/prompt.txt'  # Path to the prompt file
    file_type = 'python'                      # Desired output file type (e.g., 'python', 'javascript')
    strength = 0.5                            # Strength parameter for model selection

    # Generate the code
    result_code = code_generator(prompt_file_path, file_type, strength)

    # Print the generated runnable code
    print(result_code)

if __name__ == "__main__":
    main()
