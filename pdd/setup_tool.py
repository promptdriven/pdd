#!/usr/bin/env python3
"""
PDD Setup Script - Post-install configuration tool for PDD (Prompt Driven Development)
Helps new users bootstrap their PDD configuration with LLM API keys and basic settings.
"""

import os
import sys
import subprocess
import json
import requests
import csv
import importlib.resources
import shlex
from pathlib import Path
from typing import Dict, Optional, Tuple, List

# Global variables for non-ASCII characters and colors
HEAVY_HORIZONTAL = "━"
LIGHT_HORIZONTAL = "─" 
HEAVY_VERTICAL = "┃"
LIGHT_VERTICAL = "│"
TOP_LEFT_CORNER = "┏"
TOP_RIGHT_CORNER = "┓"
BOTTOM_LEFT_CORNER = "┗"
BOTTOM_RIGHT_CORNER = "┛"
CROSS = "┼"
TEE_DOWN = "┬"
TEE_UP = "┴"
TEE_RIGHT = "├"
TEE_LEFT = "┤"
BULLET = "•"
ARROW_RIGHT = "→"
CHECK_MARK = "✓"
CROSS_MARK = "✗"

# Color codes
RESET = "\033[0m"
WHITE = "\033[97m"
CYAN = "\033[96m"
YELLOW = "\033[93m"
BOLD = "\033[1m"

# Template content inline
SUCCESS_PYTHON_TEMPLATE = """
Write a python script to print "You did it, <Username>!!!" to the console.  
Do not write anything except that message.   
Capitalize the username."""

def _read_packaged_llm_model_csv() -> Tuple[List[str], List[Dict[str, str]]]:
    """Load the packaged CSV (pdd/data/llm_model.csv) and return header + rows.

    Returns:
        (header_fields, rows) where header_fields is the list of column names
        and rows is a list of dictionaries for each CSV row.
    """
    try:
        csv_text = importlib.resources.files('pdd').joinpath('data/llm_model.csv').read_text()
    except Exception as e:
        raise FileNotFoundError(f"Failed to load default LLM model CSV from package: {e}")

    reader = csv.DictReader(csv_text.splitlines())
    header = reader.fieldnames or []
    rows = [row for row in reader]
    return header, rows

def print_colored(text: str, color: str = WHITE, bold: bool = False) -> None:
    """Print colored text to console"""
    style = BOLD + color if bold else color
    print(f"{style}{text}{RESET}")

def create_divider(char: str = LIGHT_HORIZONTAL, width: int = 80) -> str:
    """Create a horizontal divider line"""
    return char * width

def create_fat_divider(width: int = 80) -> str:
    """Create a fat horizontal divider line"""
    return HEAVY_HORIZONTAL * width

def print_pdd_logo():
    """Print the PDD logo in ASCII art"""
    logo = "\n".join(
        [
            "  +xxxxxxxxxxxxxxx+",
            "xxxxxxxxxxxxxxxxxxxxx+",
            "xxx                 +xx+            PROMPT",
            "xxx      x+           xx+           DRIVEN",
            "xxx        x+         xxx           DEVELOPMENT©",
            "xxx         x+        xx+",
            "xxx        x+         xx+           COMMAND LINE INTERFACE",
            "xxx      x+          xxx",
            "xxx                +xx+ ",
            "xxx     +xxxxxxxxxxx+",
            "xxx   +xx+",
            "xxx  +xx+",
            "xxx+xx+                             WWW.PROMPTDRIVEN.AI",
            "xxxx+",
            "xx+",
        ]
    )
    print(f"{CYAN}{logo}{RESET}")
    print()
    print_colored("Let's get set up quickly with a solid basic configuration!", WHITE, bold=True)
    print()
    print_colored("Supported: OpenAI, Google Gemini, and Anthropic Claude", WHITE)
    print_colored("from their respective API endpoints (no third-parties, such as Azure)", WHITE)
    print()

def get_csv_variable_names() -> Dict[str, str]:
    """Inspect packaged CSV to determine API key variable names per provider.

    Focus on direct providers only: OpenAI GPT models (model startswith 'gpt-'),
    Google Gemini (model startswith 'gemini/'), and Anthropic (model startswith 'anthropic/').
    """
    header, rows = _read_packaged_llm_model_csv()
    variable_names: Dict[str, str] = {}

    for row in rows:
        model = (row.get('model') or '').strip()
        api_key = (row.get('api_key') or '').strip()
        provider = (row.get('provider') or '').strip().upper()

        if not api_key:
            continue

        if model.startswith('gpt-') and provider == 'OPENAI':
            variable_names['OPENAI'] = api_key
        elif model.startswith('gemini/') and provider == 'GOOGLE':
            # Prefer direct Gemini key, not Vertex
            variable_names['GOOGLE'] = api_key
        elif model.startswith('anthropic/') and provider == 'ANTHROPIC':
            variable_names['ANTHROPIC'] = api_key

    # Fallbacks if not detected (keep prior behavior)
    variable_names.setdefault('OPENAI', 'OPENAI_API_KEY')
    # Prefer GEMINI_API_KEY name for Google if present
    variable_names.setdefault('GOOGLE', 'GEMINI_API_KEY')
    variable_names.setdefault('ANTHROPIC', 'ANTHROPIC_API_KEY')
    return variable_names

def discover_api_keys() -> Dict[str, Optional[str]]:
    """Discover API keys from environment variables"""
    # Get the variable names actually used in CSV template
    csv_vars = get_csv_variable_names()
    
    keys = {
        'OPENAI_API_KEY': os.getenv('OPENAI_API_KEY'),
        'ANTHROPIC_API_KEY': os.getenv('ANTHROPIC_API_KEY'),
    }
    
    # For Google, check both possible environment variables but use CSV template's variable name
    google_var_name = csv_vars.get('GOOGLE', 'GEMINI_API_KEY')  # Default to GEMINI_API_KEY
    google_api_key = os.getenv('GEMINI_API_KEY') or os.getenv('GOOGLE_API_KEY')
    keys[google_var_name] = google_api_key
    
    return keys

def test_openai_key(api_key: str) -> bool:
    """Test OpenAI API key validity"""
    if not api_key or not api_key.strip():
        return False
    
    try:
        headers = {
            'Authorization': f'Bearer {api_key.strip()}',
            'Content-Type': 'application/json'
        }
        response = requests.get(
            'https://api.openai.com/v1/models',
            headers=headers,
            timeout=10
        )
        return response.status_code == 200
    except Exception:
        return False

def test_google_key(api_key: str) -> bool:
    """Test Google Gemini API key validity"""
    if not api_key or not api_key.strip():
        return False
    
    try:
        response = requests.get(
            f'https://generativelanguage.googleapis.com/v1beta/models?key={api_key.strip()}',
            timeout=10
        )
        return response.status_code == 200
    except Exception:
        return False

def test_anthropic_key(api_key: str) -> bool:
    """Test Anthropic API key validity"""
    if not api_key or not api_key.strip():
        return False
    
    try:
        headers = {
            'x-api-key': api_key.strip(),
            'Content-Type': 'application/json'
        }
        response = requests.get(
            'https://api.anthropic.com/v1/messages',
            headers=headers,
            timeout=10
        )
        # Anthropic returns 400 for invalid request structure but 401/403 for bad keys
        return response.status_code != 401 and response.status_code != 403
    except Exception:
        return False

def test_api_keys(keys: Dict[str, Optional[str]]) -> Dict[str, bool]:
    """Test all discovered API keys"""
    results = {}
    
    print_colored(f"\n{LIGHT_HORIZONTAL * 40}", CYAN)
    print_colored("Testing discovered API keys...", CYAN, bold=True)
    print_colored(f"{LIGHT_HORIZONTAL * 40}", CYAN)
    
    for key_name, key_value in keys.items():
        if key_value:
            print(f"Testing {key_name}...", end=" ", flush=True)
            if key_name == 'OPENAI_API_KEY':
                valid = test_openai_key(key_value)
            elif key_name in ['GEMINI_API_KEY', 'GOOGLE_API_KEY']:
                valid = test_google_key(key_value)
            elif key_name == 'ANTHROPIC_API_KEY':
                valid = test_anthropic_key(key_value)
            else:
                valid = False
            
            if valid:
                print_colored(f"{CHECK_MARK} Valid", CYAN)
                results[key_name] = True
            else:
                print_colored(f"{CROSS_MARK} Invalid", YELLOW)
                results[key_name] = False
        else:
            print_colored(f"{key_name}: Not found", YELLOW)
            results[key_name] = False
    
    return results

def get_user_keys(current_keys: Dict[str, Optional[str]]) -> Dict[str, Optional[str]]:
    """Interactive key entry/modification"""
    print_colored(f"\n{create_fat_divider()}", YELLOW)
    print_colored("API Key Configuration", YELLOW, bold=True)
    print_colored(f"{create_fat_divider()}", YELLOW)
    
    print_colored("You need only one API key to get started", WHITE)
    print()
    print_colored("Get API keys here:", WHITE)
    print_colored(f"  OpenAI {ARROW_RIGHT} https://platform.openai.com/api-keys", CYAN)
    print_colored(f"  Google Gemini {ARROW_RIGHT} https://aistudio.google.com/app/apikey", CYAN)
    print_colored(f"  Anthropic {ARROW_RIGHT} https://console.anthropic.com/settings/keys", CYAN)
    print()
    print_colored("A free instant starter key is available from Google Gemini (above)", CYAN)
    print()
    
    new_keys = current_keys.copy()
    
    # Get the actual key names from discovered keys
    key_names = list(current_keys.keys())
    for key_name in key_names:
        current_value = current_keys.get(key_name, "")
        status = "found" if current_value else "not found"
        
        print_colored(f"{LIGHT_HORIZONTAL * 60}", CYAN)
        print_colored(f"{key_name} (currently: {status})", WHITE, bold=True)
        
        if current_value:
            prompt = f"Enter new key or press ENTER to keep existing: "
        else:
            prompt = f"Enter API key (or press ENTER to skip): "
        
        try:
            user_input = input(f"{WHITE}{prompt}{RESET}").strip()
            if user_input:
                new_keys[key_name] = user_input
            elif not current_value:
                new_keys[key_name] = None
        except KeyboardInterrupt:
            print_colored("\n\nSetup cancelled.", YELLOW)
            sys.exit(0)
    
    return new_keys

def detect_shell() -> str:
    """Detect user's default shell"""
    try:
        shell_path = os.getenv('SHELL', '/bin/bash')
        shell_name = os.path.basename(shell_path)
        return shell_name
    except:
        return 'bash'

def get_shell_init_file(shell: str) -> str:
    """Get the appropriate shell initialization file"""
    home = Path.home()
    
    shell_files = {
        'bash': home / '.bashrc',
        'zsh': home / '.zshrc', 
        'fish': home / '.config/fish/config.fish',
        'csh': home / '.cshrc',
        'tcsh': home / '.tcshrc',
        'ksh': home / '.kshrc',
        'sh': home / '.profile'
    }
    
    return str(shell_files.get(shell, home / '.bashrc'))

def create_api_env_script(keys: Dict[str, str], shell: str) -> str:
    """Create shell-appropriate environment script with proper escaping"""
    valid_keys = {k: v for k, v in keys.items() if v}
    lines = []
    
    for key, value in valid_keys.items():
        # shlex.quote is designed for POSIX shells (sh, bash, zsh, ksh)
        # It also works reasonably well for fish and csh for simple assignments
        quoted_val = shlex.quote(value)
        
        if shell == 'fish':
            lines.append(f'set -gx {key} {quoted_val}')
        elif shell in ['csh', 'tcsh']:
            lines.append(f'setenv {key} {quoted_val}')
        else:  # bash, zsh, ksh, sh and others
            lines.append(f'export {key}={quoted_val}')
            
    return '\n'.join(lines) + '\n'

def save_configuration(valid_keys: Dict[str, str]) -> Tuple[List[str], bool, Optional[str]]:
    """Save configuration to ~/.pdd/ directory"""
    home = Path.home()
    pdd_dir = home / '.pdd'
    created_pdd_dir = False
    saved_files = []
    
    # Create .pdd directory if it doesn't exist
    if not pdd_dir.exists():
        pdd_dir.mkdir(mode=0o755)
        created_pdd_dir = True
    
    # Detect shell and create api-env script
    shell = detect_shell()
    api_env_content = create_api_env_script(valid_keys, shell)
    
    # Write shell-specific api-env file
    api_env_file = pdd_dir / f'api-env.{shell}'
    api_env_file.write_text(api_env_content)
    api_env_file.chmod(0o755)
    saved_files.append(str(api_env_file))
    
    # Create llm_model.csv with models from packaged CSV filtered by provider and available keys
    header_fields, rows = _read_packaged_llm_model_csv()

    # Keep only direct Google Gemini (model startswith 'gemini/'), OpenAI GPT (gpt-*) and Anthropic (anthropic/*)
    def _is_supported_model(row: Dict[str, str]) -> bool:
        model = (row.get('model') or '').strip()
        if model.startswith('gpt-'):
            return True
        if model.startswith('gemini/'):
            return True
        if model.startswith('anthropic/'):
            return True
        return False

    # Filter rows by supported models and by api_key presence in valid_keys
    filtered_rows: List[Dict[str, str]] = []
    for row in rows:
        if not _is_supported_model(row):
            continue
        api_key_name = (row.get('api_key') or '').strip()
        # Include only if we have a validated key for this row
        if api_key_name and api_key_name in valid_keys:
            filtered_rows.append(row)

    # Write out the filtered CSV to ~/.pdd/llm_model.csv preserving column order
    llm_model_file = pdd_dir / 'llm_model.csv'
    with llm_model_file.open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=header_fields)
        writer.writeheader()
        for row in filtered_rows:
            writer.writerow({k: row.get(k, '') for k in header_fields})
    saved_files.append(str(llm_model_file))
    
    # Update shell init file
    init_file_path = get_shell_init_file(shell)
    init_file = Path(init_file_path)
    init_file_updated = None
    
    source_line = f'[ -f "{api_env_file}" ] && source "{api_env_file}"'
    if shell == 'fish':
        source_line = f'test -f "{api_env_file}"; and source "{api_env_file}"'
    elif shell in ['csh', 'tcsh']:
        source_line = f'if ( -f "{api_env_file}" ) source "{api_env_file}"'
    elif shell == 'sh':
        source_line = f'[ -f "{api_env_file}" ] && . "{api_env_file}"'
    
    # Ensure parent directory exists (important for fish shell)
    init_file.parent.mkdir(parents=True, exist_ok=True)
    
    # Check if source line already exists
    if init_file.exists():
        content = init_file.read_text()
        if str(api_env_file) not in content:
            with init_file.open('a') as f:
                f.write(f'\n# PDD API environment\n{source_line}\n')
            init_file_updated = str(init_file)
    else:
        init_file.write_text(f'# PDD API environment\n{source_line}\n')
        init_file_updated = str(init_file)
    
    return saved_files, created_pdd_dir, init_file_updated

def create_sample_prompt():
    """Create the sample prompt file"""
    prompt_file = Path('success_python.prompt')
    prompt_file.write_text(SUCCESS_PYTHON_TEMPLATE)
    return str(prompt_file)

def show_menu(keys: Dict[str, Optional[str]], test_results: Dict[str, bool]) -> str:
    """Show main menu and get user choice"""
    print_colored(f"\n{create_divider()}", CYAN)
    print_colored("Main Menu", CYAN, bold=True)
    print_colored(f"{create_divider()}", CYAN)
    
    # Show current status
    print_colored("Current API Key Status:", WHITE, bold=True)
    # Get the actual key names from discovered keys
    key_names = list(keys.keys())
    for key_name in key_names:
        key_value = keys.get(key_name)
        if key_value:
            status = f"{CHECK_MARK} Valid" if test_results.get(key_name) else f"{CROSS_MARK} Invalid"
            status_color = CYAN if test_results.get(key_name) else YELLOW
        else:
            status = "Not configured"
            status_color = YELLOW
        
        print(f"  {key_name}: ", end="")
        print_colored(status, status_color)
    
    print()
    print_colored("Options:", WHITE, bold=True)
    print(f"  1. Re-enter API keys")
    print(f"  2. Re-test current keys")
    print(f"  3. Save configuration and exit")
    print(f"  4. Exit without saving")
    print()
    
    while True:
        try:
            choice = input(f"{WHITE}Choose an option (1-4): {RESET}").strip()
            if choice in ['1', '2', '3', '4']:
                return choice
            else:
                print_colored("Please enter 1, 2, 3, or 4", YELLOW)
        except KeyboardInterrupt:
            print_colored("\n\nSetup cancelled.", YELLOW)
            sys.exit(0)

def create_exit_summary(saved_files: List[str], created_pdd_dir: bool, sample_prompt_file: str, shell: str, valid_keys: Dict[str, str], init_file_updated: Optional[str] = None) -> str:
    """Create comprehensive exit summary"""
    summary_lines = [
        "\n\n\n\n\n",
        create_fat_divider(),
        "PDD Setup Complete!",
        create_fat_divider(),
        "",
        "API Keys Configured:",
        ""
    ]
    
    # Add configured API keys information
    if valid_keys:
        for key_name, key_value in valid_keys.items():
            # Show just the first and last few characters for security
            masked_key = f"{key_value[:8]}...{key_value[-4:]}" if len(key_value) > 12 else "***"
            summary_lines.append(f"  {key_name}: {masked_key}")
        summary_lines.extend(["", "Files created and configured:", ""])
    else:
        summary_lines.extend(["  None", "", "Files created and configured:", ""])
    
    # File descriptions with alignment
    file_descriptions = []
    if created_pdd_dir:
        file_descriptions.append(("~/.pdd/", "PDD configuration directory"))
    
    for file_path in saved_files:
        if 'api-env.' in file_path:
            file_descriptions.append((file_path, f"API environment variables ({shell} shell)"))
        elif 'llm_model.csv' in file_path:
            file_descriptions.append((file_path, "LLM model configuration"))
    
    file_descriptions.append((sample_prompt_file, "Sample prompt for testing"))
    
    # Add shell init file if it was updated
    if init_file_updated:
        file_descriptions.append((init_file_updated, f"Shell startup file (updated to source API environment)"))
    
    file_descriptions.append(("PDD-SETUP-SUMMARY.txt", "This summary"))
    
    # Find max file path length for alignment
    max_path_len = max(len(path) for path, _ in file_descriptions)
    
    for file_path, description in file_descriptions:
        summary_lines.append(f"{file_path:<{max_path_len + 2}}{description}")
    
    summary_lines.extend([
        "",
        create_divider(),
        "",
        "QUICK START:",
        "",
        f"1. Reload your shell environment:"
    ])
    
    # Shell-specific source command for manual reloading
    api_env_path = f"{Path.home()}/.pdd/api-env.{shell}"
    # Use dot command for sh shell, source for others
    if shell == 'sh':
        source_cmd = f". {api_env_path}"
    else:
        source_cmd = f"source {api_env_path}"
    
    summary_lines.extend([
        f"   {source_cmd}",
        "",
        f"2. Generate code from the sample prompt:",
        f"   pdd generate success_python.prompt",
        "",
        create_divider(),
        "",
        "LEARN MORE:",
        "",
        f"{BULLET} PDD documentation: pdd --help",
        f"{BULLET} PDD website: https://promptdriven.ai/",
        f"{BULLET} Discord community: https://discord.gg/Yp4RTh8bG7",
        "",
        "TIPS:",
        "",
        f"{BULLET} IMPORTANT: Reload your shell environment using the source command above",
        "",
        f"{BULLET} Start with simple prompts and gradually increase complexity",
        f"{BULLET} Try out 'pdd test' with your prompt+code to create test(s) pdd can use to automatically verify and fix your output code",
        f"{BULLET} Try out 'pdd example' with your prompt+code to create examples which help pdd do better",
        "",
        f"{BULLET} As you get comfortable, learn configuration settings, including the .pddrc file, PDD_GENERATE_OUTPUT_PATH, and PDD_TEST_OUTPUT_PATH",
        f"{BULLET} For larger projects, use Makefiles and/or 'pdd sync'",
        f"{BULLET} For ongoing substantial projects, learn about llm_model.csv and the --strength,",
        f"  --temperature, and --time options to optimize model cost, latency, and output quality",
        "",
        f"{BULLET} Use 'pdd --help' to explore all available commands",
        "",
        "Problems? Shout out on our Discord for help! https://discord.gg/Yp4RTh8bG7"
    ])
    
    return '\n'.join(summary_lines)

def main():
    """Main setup workflow"""
    # Initial greeting
    print_pdd_logo()
    
    # Discover environment
    print_colored(f"{create_divider()}", CYAN)
    print_colored("Discovering local configuration...", CYAN, bold=True)
    print_colored(f"{create_divider()}", CYAN)
    
    keys = discover_api_keys()
    
    # Test discovered keys
    test_results = test_api_keys(keys)
    
    # Main interaction loop
    while True:
        choice = show_menu(keys, test_results)
        
        if choice == '1':
            # Re-enter keys
            keys = get_user_keys(keys)
            test_results = test_api_keys(keys)
            
        elif choice == '2':
            # Re-test keys
            test_results = test_api_keys(keys)
            
        elif choice == '3':
            # Save and exit
            valid_keys = {k: v for k, v in keys.items() if v and test_results.get(k)}
            
            if not valid_keys:
                print_colored("\nNo valid API keys to save!", YELLOW)
                continue
            
            print_colored(f"\n{create_divider()}", CYAN)
            print_colored("Saving configuration...", CYAN, bold=True)
            print_colored(f"{create_divider()}", CYAN)
            
            try:
                saved_files, created_pdd_dir, init_file_updated = save_configuration(valid_keys)
                sample_prompt_file = create_sample_prompt()
                shell = detect_shell()
                
                # Create and display summary
                summary = create_exit_summary(saved_files, created_pdd_dir, sample_prompt_file, shell, valid_keys, init_file_updated)
                
                # Write summary to file
                summary_file = Path('PDD-SETUP-SUMMARY.txt')
                summary_file.write_text(summary)
                
                # Display summary with colors
                lines = summary.split('\n')
                for line in lines:
                    if line == create_fat_divider():
                        print_colored(line, YELLOW, bold=True)
                    elif line == "PDD Setup Complete!":
                        print_colored(line, YELLOW, bold=True)
                    elif line == create_divider():
                        print_colored(line, CYAN)
                    elif line.startswith("API Keys Configured:") or line.startswith("Files created and configured:"):
                        print_colored(line, CYAN, bold=True)
                    elif line.startswith("QUICK START:"):
                        print_colored(line, YELLOW, bold=True)
                    elif line.startswith("LEARN MORE:") or line.startswith("TIPS:"):
                        print_colored(line, CYAN, bold=True)
                    elif "IMPORTANT:" in line or "Problems?" in line:
                        print_colored(line, YELLOW, bold=True)
                    else:
                        print(line)
                
                break
                
            except Exception as e:
                print_colored(f"Error saving configuration: {e}", YELLOW)
                continue
                
        elif choice == '4':
            # Exit without saving
            print_colored("\nExiting without saving configuration.", YELLOW)
            break

if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print_colored("\n\nSetup cancelled.", YELLOW)
        sys.exit(0)