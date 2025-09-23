#!/bin/bash

# Test script for pdd example command
# This script demonstrates how to run the pdd example command

echo "=== PDD Example Command Test ==="
echo

# Check if we're in the right directory
if [ ! -f "hello_python.prompt" ]; then
    echo "Error: Please run this script from the examples/hello directory"
    echo "Current directory: $(pwd)"
    exit 1
fi

echo "Current directory: $(pwd)"
echo "Input files:"
echo "  - Prompt: hello_python.prompt"
echo "  - Code: pdd/hello.py"
echo

# Check if API key is set
if [ -z "$GEMINI_API_KEY" ]; then
    echo "Warning: GEMINI_API_KEY not set. The command will fail without it."
    echo "Set it with: export GEMINI_API_KEY=your_key_here"
    echo
fi

echo "Running pdd example command..."
echo "Command: pdd example hello_python.prompt pdd/hello.py --output test_output.py"
echo

# Run the command
pdd example hello_python.prompt pdd/hello.py --output test_output.py

echo
echo "Command completed. Check test_output.py for the generated example."
echo

# If the file was created, show its contents
if [ -f "test_output.py" ]; then
    echo "Generated example file contents:"
    echo "=================================="
    cat test_output.py
    echo "=================================="
    echo
    echo "To run the example: python test_output.py"
else
    echo "No output file was created (likely due to API key or quota issues)"
fi
