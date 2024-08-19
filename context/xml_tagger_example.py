import os
from xml_tagger import xml_tagger  # Import the xml_tagger function

def main() -> None:
    """
    Main function to demonstrate the usage of the xml_tagger function.
    It sets up the input parameters, calls the function, and prints the results.
    """
    # Define the raw prompt, strength, and temperature
    raw_prompt: str = "Write a story about a magical forest"
    strength: float = 0.7  # Strength parameter for LLM selection
    temperature: float = 0.5  # Temperature parameter for LLM selection

    try:
        # Call the xml_tagger function
        xml_tagged, total_cost = xml_tagger(raw_prompt, strength, temperature)

        # Print the results
        print("XML Tagged Output:")
        print(xml_tagged)
        print(f"Total Processing Cost: ${total_cost:.6f}")
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()