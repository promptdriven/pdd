from pdd.load_prompt_template import load_prompt_template
from rich import print

def main():
    prompt_name = "generate_test_LLM"  # Name of the prompt file without extension
    prompt = load_prompt_template(prompt_name)
    if prompt:
        print("[blue]Loaded Prompt Template:[/blue]")
        print(prompt)

if __name__ == "__main__":
    main()