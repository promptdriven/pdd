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
    head -20 test_output.py
    echo "=================================="
    echo
    echo "Testing if the example runs correctly..."
    
    # Test if the example runs
    if python test_output.py >/dev/null 2>&1; then
        echo "✅ Example runs successfully!"
        echo "Output:"
        python test_output.py
    else
        echo "❌ Example failed to run. Checking for common issues..."
        
        # Check for import issues
        if grep -q "from.*import" test_output.py; then
            echo "Found import statements. This might cause issues if the imported module doesn't exist."
            echo "You may need to fix the imports manually or run the fix script."
        fi
        
        echo "To debug: python test_output.py"
    fi
else
    echo "No output file was created (likely due to API key or quota issues)"
fi

echo
echo "If you have issues with the generated example, you can:"
echo "1. Run the fix script: python fix_example.py"
echo "2. Manually edit the example to remove problematic imports"
echo "3. Ensure the example is self-contained and doesn't depend on external modules"
