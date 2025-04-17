
#!/bin/bash

# Check if the module argument is provided
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <module>"
    exit 1
fi

MODULE=$1
TMP_PROMPT="tmp_prompt.prompt"
PROMPT_FILE="prompts/generate_prompt.prompt"
OUTPUT_FILE="prompts/${MODULE}_python.prompt"

# Substitute the string in the prompt file
# Assuming the placeholder in the generate_prompt.prompt file is {module}
sed "s/{module}/$MODULE/g" "$PROMPT_FILE" > "$TMP_PROMPT"

# Run the command
pdd --strength .85 --temperature 1 generate --output "$OUTPUT_FILE" "$TMP_PROMPT"

# Remove the temporary prompt file
rm "$TMP_PROMPT"

echo "Prompt generated and saved to $OUTPUT_FILE"