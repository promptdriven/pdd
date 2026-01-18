import os
import click
import shutil
from pdd.commands.analysis import detect_change, conflicts, bug, crash, trace

# Define the output directory relative to this script
OUTPUT_DIR = os.path.join(os.path.dirname(__file__), "output")
os.makedirs(OUTPUT_DIR, exist_ok=True)

def clean_output(path):
    """Removes the file or directory if it exists to prevent overwrite prompts."""
    if os.path.exists(path):
        if os.path.isdir(path):
            shutil.rmtree(path)
        else:
            os.remove(path)

def main():
    """
    Demonstrates how to use the analysis commands (detect, conflicts, bug, crash, trace)
    programmatically by invoking their Click command callbacks.
    """
    
    # 1. Setup a Click Context
    # The commands rely on a Click Context to access global configuration like
    # verbosity, model strength, and cost tracking settings.
    ctx = click.Context(click.Command('analysis'))
    ctx.obj = {
        'quiet': False,
        'verbose': True,
        'strength': 0.5,
        'temperature': 0.0,
        'output_cost': None  # Optional path for cost CSV
    }

    # IMPORTANT: Use the context manager to push the context to the stack.
    # This is required because the commands use @click.pass_context, which
    # retrieves the active context from the stack.
    with ctx:
        print("--- 1. Detect Change ---")
        # Detects if prompts need to be changed based on a description.
        
        prompt_1 = os.path.join(OUTPUT_DIR, "math_ops.prompt")
        prompt_2 = os.path.join(OUTPUT_DIR, "string_ops.prompt")
        change_desc = os.path.join(OUTPUT_DIR, "change_request.txt")
        detect_out = os.path.join(OUTPUT_DIR, "detect_results.csv")

        # Clean output to avoid overwrite prompt
        clean_output(detect_out)

        # Create dummy files
        with open(prompt_1, "w") as f: f.write("Create a function to add numbers.")
        with open(prompt_2, "w") as f: f.write("Create a function to concat strings.")
        with open(change_desc, "w") as f: f.write("Update all functions to include type hints.")

        # Invoke command callback
        # Note: We do NOT pass 'ctx' explicitly here. @click.pass_context injects it.
        result = detect_change.callback(
            files=(prompt_1, prompt_2, change_desc),
            output=detect_out
        )
        print(f"Detect Result: {result}")


        print("\n--- 2. Conflicts ---")
        # Checks for conflicts between two prompt files.
        
        # FIX: Use .txt extension to ensure language detection works (defaults to text)
        conflict_1 = os.path.join(OUTPUT_DIR, "theme_dark.txt")
        conflict_2 = os.path.join(OUTPUT_DIR, "theme_light.txt")
        conflicts_out = os.path.join(OUTPUT_DIR, "conflicts.csv")

        clean_output(conflicts_out)

        with open(conflict_1, "w") as f: f.write("Use dark theme default.")
        with open(conflict_2, "w") as f: f.write("Use light theme default.")

        result = conflicts.callback(
            prompt1=conflict_1,
            prompt2=conflict_2,
            output=conflicts_out
        )
        print(f"Conflicts Result: {result}")


        print("\n--- 3. Bug ---")
        # Generates a unit test reproducing a bug from inputs and outputs.
        
        bug_prompt = os.path.join(OUTPUT_DIR, "calc.prompt")
        bug_code = os.path.join(OUTPUT_DIR, "calc.py")
        bug_prog = os.path.join(OUTPUT_DIR, "run_calc.py")
        curr_out = os.path.join(OUTPUT_DIR, "actual.txt")
        des_out = os.path.join(OUTPUT_DIR, "expected.txt")
        test_out = os.path.join(OUTPUT_DIR, "test_calc_bug.py")

        clean_output(test_out)

        with open(bug_prompt, "w") as f: f.write("Function to multiply numbers.")
        with open(bug_code, "w") as f: f.write("def mul(a, b): return a + b # Bug")
        with open(bug_prog, "w") as f: f.write("from calc import mul\nprint(mul(2, 3))")
        with open(curr_out, "w") as f: f.write("5")
        with open(des_out, "w") as f: f.write("6")

        # FIX: Use correct arguments for bug command (manual=True, args=tuple)
        # Added timeout_adder and no_github_state to match function signature
        result = bug.callback(
            manual=True,
            args=(bug_prompt, bug_code, bug_prog, curr_out, des_out),
            output=test_out,
            language="Python",
            timeout_adder=0.0,
            no_github_state=False
        )
        print(f"Bug Result: {result}")


        print("\n--- 4. Crash ---")
        # Analyzes a crash and fixes the code and program.
        
        crash_prompt = os.path.join(OUTPUT_DIR, "div.prompt")
        crash_code = os.path.join(OUTPUT_DIR, "div.py")
        crash_prog = os.path.join(OUTPUT_DIR, "run_div.py")
        crash_err = os.path.join(OUTPUT_DIR, "crash.log")
        fixed_code = os.path.join(OUTPUT_DIR, "div_fixed.py")
        fixed_prog = os.path.join(OUTPUT_DIR, "run_div_fixed.py")

        clean_output(fixed_code)
        clean_output(fixed_prog)

        with open(crash_prompt, "w") as f: f.write("Function to divide numbers.")
        with open(crash_code, "w") as f: f.write("def div(a, b): return a / b")
        with open(crash_prog, "w") as f: f.write("print(div(1, 0))")
        with open(crash_err, "w") as f: f.write("ZeroDivisionError: division by zero")

        result = crash.callback(
            prompt_file=crash_prompt,
            code_file=crash_code,
            program_file=crash_prog,
            error_file=crash_err,
            output=fixed_code,
            output_program=fixed_prog,
            loop=False,
            max_attempts=3,
            budget=5.0
        )
        print(f"Crash Result: {result}")


        print("\n--- 5. Trace ---")
        # Traces execution flow back to the prompt.
        
        trace_prompt = os.path.join(OUTPUT_DIR, "logic.prompt")
        trace_code = os.path.join(OUTPUT_DIR, "logic.py")
        trace_out = os.path.join(OUTPUT_DIR, "trace.log")

        clean_output(trace_out)

        with open(trace_prompt, "w") as f: f.write("1. Set x to 10.\n2. Print x.")
        with open(trace_code, "w") as f: f.write("x = 10\nprint(x)")

        result = trace.callback(
            prompt_file=trace_prompt,
            code_file=trace_code,
            code_line=2,
            output=trace_out
        )
        print(f"Trace Result: {result}")

if __name__ == "__main__":
    main()