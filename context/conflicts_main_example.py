from tabnanny import verbose
import click
from pdd.conflicts_main import conflicts_main


prompt1 = 'prompt1_LLM.prompt'
prompt2 = 'prompt2_LLM.prompt'

# Create example prompt files
with open(prompt1, 'w') as f:
    f.write("You are an AI assistant. Help the user with their tasks.")

with open(prompt2, 'w') as f:
    f.write("You are a helpful chatbot. Assist users with their queries.")

# Create a mock Click context
class MockContext:
    def __init__(self):
        self.params = {
            'force': True,
            'quiet': False,
            'strength': 0.5,
            'temperature': 0
        }
        self.obj = {}  # Add this line to include the 'obj' attribute

    def exit(self, code):
        print(f"Exiting with code {code}")

# Use the conflicts_main function
ctx = MockContext()

output = 'conflicts_output.csv'

conflicts, total_cost, model_name = conflicts_main(ctx, prompt1, prompt2, output, verbose=True)

print(f"Conflicts: {conflicts}")
print(f"Total cost: ${total_cost:.6f}")
print(f"Model used: {model_name}")

# The results will be saved in 'conflicts_output.csv'