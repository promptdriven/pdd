from xml_tagger import xml_tagger  # Import the xml_tagger function


# Define input parameters
def main() -> None:
    """Main function to demonstrate the usage of xml_tagger."""
    # read prompts/split_LLM.prompt into raw_prompt
    raw_prompt = ""
    with open('prompts/split_LLM.prompt', 'r') as file:
        raw_prompt = file.read()
    strength: float = 1  # Strength parameter for LLM selection
    temperature: float = 0  # Temperature parameter for LLM selection

    # Call the xml_tagger function
    try:
        xml_tagged_output: str = xml_tagger(raw_prompt, strength, temperature)

        # Print the result
        if xml_tagged_output:
            print("XML Tagged Output:")
            print(xml_tagged_output)
        else:
            print("Failed to generate XML tagged output.")
    except Exception as e:
        print(f"Error during xml_tagger execution: {e}")

if __name__ == "__main__":
    main()