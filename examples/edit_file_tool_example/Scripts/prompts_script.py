import os
import json
import shutil
import subprocess
import sys

def get_pdd_command_prefix():
    """
    Build PDD command prefix from environment variables (set by Makefile) or use defaults.
    This ensures consistency between Makefile and Python scripts.
    """
    # Check if PDD_CMD is already set by Makefile
    if 'PDD_CMD' in os.environ:
        return os.environ['PDD_CMD'].strip()
    
    # Fallback: build from individual variables or defaults
    use_infisical = os.environ.get('USE_INFISICAL', 'yes').lower() == 'yes'
    use_local = os.environ.get('USE_LOCAL', 'yes').lower() == 'yes'
    
    # Use direct pdd command - path should be set up by environment
    pdd_base = "pdd"
    pdd_flags = "--local" if use_local else ""
    
    if use_infisical:
        return f"infisical run -- {pdd_base} {pdd_flags}".strip()
    else:
        return f"{pdd_base} {pdd_flags}".strip()

# --- Configuration ---
ARCHITECTURE_JSON = "pdd/architecture.json"
SOURCE_PROMPT_TEMPLATE = "prompts/script_prompts/modify_template_prompt.prompt"
TEMPLATE_PROMPTS_DIR = "prompts/template_prompts"
FINAL_PROMPTS_DIR = "prompts"
LOG_DIR = os.path.join("logs", "scripts_prompts")
COST_REPORT_DIR = "cost_reports"
COST_REPORT_FILE = os.path.join(COST_REPORT_DIR, "prompt_cost.csv")
PDD_COMMAND_PREFIX = get_pdd_command_prefix()

def run_shell_command(command: str):
    """
    Execute a single command-line string and return its exit code.
    Handles different platforms (Windows/Unix).
    """
    print(f"\n[INFO] Executing command:\n  {command}")
    try:
        if sys.platform == "win32":
            ps_exe = "pwsh" if shutil.which("pwsh") else "powershell"
            cmd_list = [ps_exe, "-NoLogo", "-NoProfile", "-Command", f"& {{ {command} }}"]
            result = subprocess.run(cmd_list, check=True, text=True, capture_output=True)
        else:
            result = subprocess.run(command, shell=True, executable="/bin/bash", check=True, text=True, capture_output=True)
        
        if result.stdout:
            print(f"[STDOUT]:\n{result.stdout}")
        if result.stderr:
            print(f"[STDERR]:\n{result.stderr}")
            
        print("[INFO] Command executed successfully.")
        return 0
    except subprocess.CalledProcessError as e:
        print(f"[ERROR] Command failed with exit code {e.returncode}.")
        if e.stdout:
            print(f"[STDOUT]:\n{e.stdout}")
        if e.stderr:
            print(f"[STDERR]:\n{e.stderr}")
        return e.returncode
    except Exception as e:
        print(f"[ERROR] An unexpected error occurred: {e}")
        return 1

def main():
    # 1. Check if architecture.json exists
    if not os.path.exists(ARCHITECTURE_JSON):
        print(f"[ERROR] Required file '{ARCHITECTURE_JSON}' not found. Please ensure it exists in the root directory.")
        sys.exit(1)
        
    if not os.path.exists(SOURCE_PROMPT_TEMPLATE):
        print(f"[ERROR] Source prompt template '{SOURCE_PROMPT_TEMPLATE}' not found.")
        sys.exit(1)

    # 2. Create directories
    os.makedirs(TEMPLATE_PROMPTS_DIR, exist_ok=True)
    os.makedirs(FINAL_PROMPTS_DIR, exist_ok=True)
    os.makedirs(LOG_DIR, exist_ok=True)
    os.makedirs(COST_REPORT_DIR, exist_ok=True)
    print(f"[INFO] Created directories: '{TEMPLATE_PROMPTS_DIR}', '{FINAL_PROMPTS_DIR}', '{LOG_DIR}', '{COST_REPORT_DIR}'")

    # Read the list of files from architecture.json
    try:
        with open(ARCHITECTURE_JSON, 'r', encoding='utf-8') as f:
            filenames = json.load(f)
    except json.JSONDecodeError:
        print(f"[ERROR] Could not parse '{ARCHITECTURE_JSON}'. Make sure it's a valid JSON file.")
        sys.exit(1)

    # Read the source prompt content
    try:
        with open(SOURCE_PROMPT_TEMPLATE, 'r', encoding='utf-8') as f:
            source_content = f.read()
    except IOError as e:
        print(f"[ERROR] Could not read source prompt template '{SOURCE_PROMPT_TEMPLATE}': {e}")
        sys.exit(1)

    all_commands = []
    
    # 3. Use existing template prompts or create them if they don't exist
    print("\n--- Phase 1: Preparing Template Prompts ---")
    for filename in filenames:
        base_name = filename['filename'].replace('.py', '')
        target_script_name = base_name + ".py"
        
        # Check if template prompt already exists
        template_prompt_name = f"{base_name}_python_prompt.prompt"
        template_prompt_path = os.path.join(TEMPLATE_PROMPTS_DIR, template_prompt_name).replace(os.sep, '/')
        
        if not os.path.exists(template_prompt_path):
            # Create the template prompt by replacing the placeholder
            modified_content = source_content.replace("placeholder.py", target_script_name)
            
            try:
                with open(template_prompt_path, 'w', encoding='utf-8') as f:
                    f.write(modified_content)
                print(f"[SUCCESS] Created template prompt: '{template_prompt_path}'")
            except IOError as e:
                print(f"[ERROR] Could not write template prompt to '{template_prompt_path}': {e}")
                continue # Skip to the next file
        else:
            print(f"[INFO] Using existing template prompt: '{template_prompt_path}'")

        # 4. Construct the generate command for this prompt
        final_prompt_name = f"{base_name}_python.prompt"
        final_prompt_path = os.path.join(FINAL_PROMPTS_DIR, final_prompt_name).replace(os.sep, '/')

        # Use forward slashes for cross-platform compatibility in the command
        cost_report_path_cmd = COST_REPORT_FILE.replace(os.sep, '/')

        # Define log file path
        log_filename = f"{base_name}_prompt.log"
        log_filepath = os.path.join(LOG_DIR, log_filename).replace(os.sep, '/')
        
        cmd = (
            f"{PDD_COMMAND_PREFIX} --output-cost \"{cost_report_path_cmd}\" "
            f"generate --output \"{final_prompt_path}\" \"{template_prompt_path}\" "
            f"> \"{log_filepath}\" 2>&1"
        )
        all_commands.append(cmd)

    # 5. Execute all generated commands
    print("\n--- Phase 2: Generating Final Prompts ---")
    for command in all_commands:
        return_code = run_shell_command(command)
        if return_code != 0:
            print(f"[WARN] The last command failed. Continuing with the rest of the script...")

    print("\n[INFO] Script finished.")

if __name__ == "__main__":
    main() 