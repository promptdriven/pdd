import os
import click
from pdd.commands.analysis import detect_change, conflicts, bug, crash, trace

# Define the output directory relative to this script
OUTPUT_DIR = os.path.join(os.path.dirname(__file__), "output")
os.makedirs(OUTPUT_DIR, exist_ok=True)

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

    print("--- 1. Detect Change ---")
    # Detects if prompts need to be changed based on a description.
    # Inputs:
    #   files: Tuple of file paths. The last file is the change description.
    #   output: Path to save the CSV analysis results.
    
    prompt_1 = os.path.join(OUTPUT_DIR, "math_ops.prompt")
    prompt_2 = os.path.join(OUTPUT_DIR, "string_ops.prompt")
    change_desc = os.path.join(OUTPUT_DIR, "change_request.txt")
    detect_out = os.path.join(OUTPUT_DIR, "detect_results.csv")

    # Create dummy files
    with open(prompt_1, "w") as f: f.write("Create a function to add numbers.")
    with open(prompt_2, "w") as f: f.write("Create a function to concat strings.")
    with open(change_desc, "w") as f: f.write("Update all functions to include type hints.")

    # Invoke command callback
    # Returns: (result_list, total_cost, model_name) or None on error
    result = detect_change.callback(
        ctx=ctx,
        files=(prompt_1, prompt_2, change_desc),
        output=detect_out
    )
    print(f"Detect Result: {result}")


    print("\n--- 2. Conflicts ---")
    # Checks for conflicts between two prompt files.
    # Inputs:
    #   prompt1, prompt2: Paths to prompt files.
    #   output: Path to save CSV results.
    
    conflict_1 = os.path.join(OUTPUT_DIR, "theme_dark.prompt")
    conflict_2 = os.path.join(OUTPUT_DIR, "theme_light.prompt")
    conflicts_out = os.path.join(OUTPUT_DIR, "conflicts.csv")

    with open(conflict_1, "w") as f: f.write("Use dark theme default.")
    with open(conflict_2, "w") as f: f.write("Use light theme default.")

    result = conflicts.callback(
        ctx=ctx,
        prompt1=conflict_1,
        prompt2=conflict_2,
        output=conflicts_out
    )
    print(f"Conflicts Result: {result}")


    print("\n--- 3. Bug ---")
    # Generates a unit test reproducing a bug from inputs and outputs.
    # Inputs:
    #   prompt_file, code_file, program_file: Source files.
    #   current_output, desired_output: Files containing output text.
    #   output: Path to save the generated unit test.
    #   language: Programming language (e.g., "Python").
    
    bug_prompt = os.path.join(OUTPUT_DIR, "calc.prompt")
    bug_code = os.path.join(OUTPUT_DIR, "calc.py")
    bug_prog = os.path.join(OUTPUT_DIR, "run_calc.py")
    curr_out = os.path.join(OUTPUT_DIR, "actual.txt")
    des_out = os.path.join(OUTPUT_DIR, "expected.txt")
    test_out = os.path.join(OUTPUT_DIR, "test_calc_bug.py")

    with open(bug_prompt, "w") as f: f.write("Function to multiply numbers.")
    with open(bug_code, "w") as f: f.write("def mul(a, b): return a + b # Bug")
    with open(bug_prog, "w") as f: f.write("from calc import mul\nprint(mul(2, 3))")
    with open(curr_out, "w") as f: f.write("5")
    with open(des_out, "w") as f: f.write("6")

    result = bug.callback(
        ctx=ctx,
        prompt_file=bug_prompt,
        code_file=bug_code,
        program_file=bug_prog,
        current_output=curr_out,
        desired_output=des_out,
        output=test_out,
        language="Python"
    )
    print(f"Bug Result: {result}")


    print("\n--- 4. Crash ---")
    # Analyzes a crash and fixes the code and program.
    # Inputs:
    #   prompt_file, code_file, program_file: Source files.
    #   error_file: File containing the traceback/error log.
    #   output: Path to save fixed code.
    #   output_program: Path to save fixed program.
    #   loop: Enable iterative fixing.
    #   max_attempts: Max retries.
    #   budget: Max cost in USD.
    
    crash_prompt = os.path.join(OUTPUT_DIR, "div.prompt")
    crash_code = os.path.join(OUTPUT_DIR, "div.py")
    crash_prog = os.path.join(OUTPUT_DIR, "run_div.py")
    crash_err = os.path.join(OUTPUT_DIR, "crash.log")
    fixed_code = os.path.join(OUTPUT_DIR, "div_fixed.py")
    fixed_prog = os.path.join(OUTPUT_DIR, "run_div_fixed.py")

    with open(crash_prompt, "w") as f: f.write("Function to divide numbers.")
    with open(crash_code, "w") as f: f.write("def div(a, b): return a / b")
    with open(crash_prog, "w") as f: f.write("print(div(1, 0))")
    with open(crash_err, "w") as f: f.write("ZeroDivisionError: division by zero")

    result = crash.callback(
        ctx=ctx,
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
    # Inputs:
    #   prompt_file, code_file: Source files.
    #   code_line: The line number in the code file to trace.
    #   output: Path to save trace results.
    
    trace_prompt = os.path.join(OUTPUT_DIR, "logic.prompt")
    trace_code = os.path.join(OUTPUT_DIR, "logic.py")
    trace_out = os.path.join(OUTPUT_DIR, "trace.log")

    with open(trace_prompt, "w") as f: f.write("1. Set x to 10.\n2. Print x.")
    with open(trace_code, "w") as f: f.write("x = 10\nprint(x)")

    result = trace.callback(
        ctx=ctx,
        prompt_file=trace_prompt,
        code_file=trace_code,
        code_line=2,
        output=trace_out
    )
    print(f"Trace Result: {result}")

if __name__ == "__main__":
    main()
