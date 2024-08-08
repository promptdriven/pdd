import subprocess
import sys
import shutil
import os

def run_pytest(unit_test_file):
    """Run pytest on the given unit test file and capture output."""
    result = subprocess.run(['pytest', unit_test_file], capture_output=True, text=True)
    with open('error.log', 'a') as f:
        f.write(result.stdout)
        f.write(result.stderr)
    return result.returncode != 0  # Return True if there are errors

def extract_errors_from_log():
    """Extract the number of failed tests and errors from error.log."""
    with open('error.log', 'r') as f:
        log_content = f.read()
    print(log_content)  # Step 2a: Print out the error message
    # Extract number of failed and errors
    failed = log_content.count('FAILED')
    errors = log_content.count('ERROR')
    return failed, errors

def copy_files_with_suffix(unit_test_file, code_file, failed, errors):
    """Copy the unit test and code files with a suffix indicating the number of fails and errors."""
    unit_test_copy = f"{os.path.splitext(unit_test_file)[0]}_{failed}_{errors}.py"
    code_copy = f"{os.path.splitext(code_file)[0]}_{failed}_{errors}.py"
    shutil.copy(unit_test_file, unit_test_copy)
    shutil.copy(code_file, code_copy)
    return unit_test_copy, code_copy

def run_pdd_fix(unit_test_file, code_file):
    """Run the PDD fix command and append output to error.log."""
    result = subprocess.run([
        'python', 'staging/pdd/pdd.py', 
        '--strength', '0.9',
        'fix',
        '--output-test', unit_test_file,
        '--output-code', code_file,
        unit_test_file,
        code_file,
        'error.log'
    ], capture_output=True, text=True)
    with open('error.log', 'a') as f:
        f.write("\n--- PDD Output ---\n")
        f.write(result.stdout)
        f.write(result.stderr)

def run_verification_program(verification_program):
    """Run the verification program to ensure the code still runs."""
    result = subprocess.run(['python', verification_program], capture_output=True, text=True)
    return result.returncode == 0  # Return True if the program runs successfully

def main(unit_test_file, code_file, max_attempts, verification_program):
    attempts = 0
    old_failed, old_errors = 0, 0

    while attempts < max_attempts:
        if not run_pytest(unit_test_file):
            print("All tests passed!")
            break
        failed, errors = extract_errors_from_log()
        copy_files_with_suffix(unit_test_file, code_file, failed-old_failed, errors-old_errors)
        old_failed, old_errors = failed, errors
        run_pdd_fix(unit_test_file, code_file)
        if not run_verification_program(verification_program):
            print("Verification program failed. Attempting to fix again.")
            # Restore original files
            shutil.copy(unit_test_file, f"{os.path.splitext(unit_test_file)[0]}.py")
            shutil.copy(code_file, f"{os.path.splitext(code_file)[0]}.py")
    
        attempts += 1
    else:
        print("Reached maximum number of attempts without success.")

if __name__ == "__main__":
    if len(sys.argv) != 5:
        print("Usage: python fix_errors.py <unit_test_file> <code_file> <max_attempts> <verification_program>")
        sys.exit(1)

    unit_test_file = sys.argv[1]
    code_file = sys.argv[2]
    max_attempts = int(sys.argv[3])
    verification_program = sys.argv[4]

    main(unit_test_file, code_file, max_attempts, verification_program)