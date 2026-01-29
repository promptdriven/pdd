from __future__ import annotations

import os
import sys
import json
import shutil
import subprocess
import tempfile
import time
import uuid
import re
from pathlib import Path
from typing import List, Optional, Tuple, Dict, Any, Union
from dataclasses import dataclass

from rich.console import Console

try:
    from pdd.llm_invoke import _load_model_data
except ImportError:
    def _load_model_data(*args, **kwargs):
        return None

# Constants
AGENT_PROVIDER_PREFERENCE: List[str] = ["anthropic", "google", "openai"]

# CLI command mapping for each provider
CLI_COMMANDS: Dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
}

# Common installation paths for CLI tools (platform-specific)
# Used as fallback when shutil.which() fails to find the binary
_COMMON_CLI_PATHS: Dict[str, List[Path]] = {
    "claude": [
        Path.home() / ".npm-global" / "bin" / "claude",
        Path.home() / ".local" / "bin" / "claude",
        Path.home() / "bin" / "claude",
        Path("/usr/local/bin/claude"),
        Path("/opt/homebrew/bin/claude"),
        Path("/home/linuxbrew/.linuxbrew/bin/claude"),
        # nvm base path - glob-expanded in _find_cli_binary() to search
        # ~/.nvm/versions/node/*/bin/ for all installed node versions
        Path.home() / ".nvm" / "versions" / "node",
    ],
    "codex": [
        Path.home() / ".npm-global" / "bin" / "codex",
        Path.home() / ".local" / "bin" / "codex",
        Path("/usr/local/bin/codex"),
        Path("/opt/homebrew/bin/codex"),
    ],
    "gemini": [
        Path.home() / ".local" / "bin" / "gemini",
        Path("/usr/local/bin/gemini"),
        Path("/opt/homebrew/bin/gemini"),
    ],
}

# Maximum depth to search for .pddrc file
MAX_PDDRC_SEARCH_DEPTH: int = 10

DEFAULT_TIMEOUT_SECONDS: float = 600.0  # Increased from 240s; Claude needs time for complex verify tasks
MIN_VALID_OUTPUT_LENGTH: int = 50
DEFAULT_MAX_RETRIES: int = 3
DEFAULT_RETRY_DELAY: float = 5.0
MAX_PATH_DISPLAY_LENGTH: int = 200  # Truncation length for PATH in diagnostic messages

# GitHub State Markers
GITHUB_STATE_MARKER_START = "<!-- PDD_WORKFLOW_STATE:"
GITHUB_STATE_MARKER_END = "-->"

@dataclass
class Pricing:
    input_per_million: float
    output_per_million: float
    cached_input_multiplier: float = 1.0

# Pricing Configuration
# Gemini: Based on test expectations (Flash: $0.35/$1.05, Cached 50%)
GEMINI_PRICING_BY_FAMILY = {
    "flash": Pricing(0.35, 1.05, 0.5),
    "pro": Pricing(3.50, 10.50, 0.5), # Placeholder for Pro
}

# Codex: Based on test expectations ($1.50/$6.00, Cached 25%)
CODEX_PRICING = Pricing(1.50, 6.00, 0.25)

console = Console()


# ---------------------------------------------------------------------------
# CLI Discovery (addresses GitHub issue #234: Claude not found during agentic fallback)
# ---------------------------------------------------------------------------


def _load_agentic_config() -> Dict[str, Any]:
    """
    Load agentic CLI configuration from .pddrc.

    Looks for an 'agentic' section in .pddrc with CLI path overrides:

        agentic:
          claude_path: /path/to/claude
          codex_path: /path/to/codex
          gemini_path: /path/to/gemini

    Returns empty dict if no config found.
    """
    import yaml

    # Search for .pddrc in current dir and parent dirs
    search_path = Path.cwd()
    pddrc_path: Optional[Path] = None
    for _ in range(MAX_PDDRC_SEARCH_DEPTH):
        candidate = search_path / ".pddrc"
        if candidate.is_file():
            pddrc_path = candidate
            break
        parent = search_path.parent
        if parent == search_path:
            break
        search_path = parent

    # Also check home directory
    if not pddrc_path:
        home_pddrc = Path.home() / ".pddrc"
        if home_pddrc.is_file():
            pddrc_path = home_pddrc

    if not pddrc_path:
        return {}

    try:
        with open(pddrc_path, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)
        if isinstance(config, dict):
            return config.get("agentic", {}) or {}
    except Exception:
        pass

    return {}


def _find_cli_binary(name: str, config: Optional[Dict[str, Any]] = None) -> Optional[str]:
    """
    Find a CLI binary using multiple strategies.

    This function addresses a common issue where CLI tools like 'claude' are
    installed and runnable from the user's shell, but not found by shutil.which()
    when pdd runs. This happens because shell profiles (.bashrc, .zshrc) may add
    directories to PATH that aren't available in the pdd process environment.

    Strategies (in order):
        1. Check for explicit path override in .pddrc agentic config
        2. Try shutil.which() for standard PATH lookup
        3. Search common installation directories

    Args:
        name: CLI binary name (e.g., "claude", "codex", "gemini")
        config: Optional pre-loaded agentic config dict (avoids repeated file reads)

    Returns:
        Full path to the binary if found, None otherwise
    """
    # Strategy 1: Check .pddrc config override
    if config is None:
        config = _load_agentic_config()

    config_key = f"{name}_path"
    if config_key in config:
        custom_path = Path(config[config_key])
        if custom_path.exists() and os.access(custom_path, os.X_OK):
            return str(custom_path)

    # Strategy 2: Standard PATH lookup
    path_result = shutil.which(name)
    if path_result:
        return path_result

    # Strategy 3: Search common installation directories
    common_paths = _COMMON_CLI_PATHS.get(name, [])
    for path in common_paths:
        # Handle nvm-style paths that need glob expansion
        # nvm installs to ~/.nvm/versions/node/vX.Y.Z/bin/
        if "nvm" in str(path) and path.name == "node":
            # Glob for all node versions and check for the CLI in each
            try:
                for version_dir in path.glob("*/bin"):
                    cli_path = version_dir / name
                    if cli_path.exists() and os.access(cli_path, os.X_OK):
                        return str(cli_path)
            except Exception:
                pass
        elif path.exists() and os.access(path, os.X_OK):
            return str(path)

    return None


def _get_cli_diagnostic_info(name: str) -> str:
    """
    Generate diagnostic information for CLI discovery failures.

    Returns a helpful message for troubleshooting when a CLI binary cannot be found.
    """
    lines = [
        f"CLI '{name}' not found. Troubleshooting steps:",
        "",
        f"1. Check installation: which {name}",
        f"2. Common installation paths searched:",
    ]

    for path in _COMMON_CLI_PATHS.get(name, []):
        lines.append(f"   - {path}")

    lines.extend([
        "",
        "3. Configure custom path in .pddrc:",
        f"   agentic:",
        f"     {name}_path: /path/to/{name}",
        "",
        f"4. Current PATH: {os.environ.get('PATH', 'not set')[:MAX_PATH_DISPLAY_LENGTH]}...",
    ])

    return "\n".join(lines)


def get_available_agents() -> List[str]:
    """
    Returns list of available provider names based on CLI existence and API key configuration.

    Uses _find_cli_binary() for robust CLI discovery that searches:
    1. .pddrc config overrides
    2. Standard PATH (shutil.which)
    3. Common installation directories
    """
    available = []

    # 1. Anthropic (Claude)
    # Available if 'claude' CLI exists. API key not strictly required (subscription auth).
    if _find_cli_binary("claude"):
        available.append("anthropic")

    # 2. Google (Gemini)
    # Available if 'gemini' CLI exists AND (API key is set OR Vertex AI auth is configured)
    has_gemini_cli = _find_cli_binary("gemini") is not None
    has_google_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
    has_vertex_auth = (
        os.environ.get("GOOGLE_APPLICATION_CREDENTIALS") and
        os.environ.get("GOOGLE_GENAI_USE_VERTEXAI") == "true"
    )

    if has_gemini_cli and (has_google_key or has_vertex_auth):
        available.append("google")

    # 3. OpenAI (Codex)
    # Available if 'codex' CLI exists AND OPENAI_API_KEY is set
    if _find_cli_binary("codex") and os.environ.get("OPENAI_API_KEY"):
        available.append("openai")

    return available

def _calculate_gemini_cost(stats: Dict[str, Any]) -> float:
    """Calculates cost for Gemini based on token stats."""
    total_cost = 0.0
    models = stats.get("models", {})
    
    for model_name, data in models.items():
        tokens = data.get("tokens", {})
        prompt = tokens.get("prompt", 0)
        candidates = tokens.get("candidates", 0)
        cached = tokens.get("cached", 0)
        
        # Determine pricing family
        family = "flash" if "flash" in model_name.lower() else "pro"
        pricing = GEMINI_PRICING_BY_FAMILY.get(family, GEMINI_PRICING_BY_FAMILY["flash"])
        
        # Logic: new_input = max(0, prompt - cached)
        # Assuming 'prompt' is total input tokens
        new_input = max(0, prompt - cached)
        
        input_cost = (new_input / 1_000_000) * pricing.input_per_million
        cached_cost = (cached / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
        output_cost = (candidates / 1_000_000) * pricing.output_per_million
        
        total_cost += input_cost + cached_cost + output_cost
        
    return total_cost

def _calculate_codex_cost(usage: Dict[str, Any]) -> float:
    """Calculates cost for Codex based on usage stats."""
    input_tokens = usage.get("input_tokens", 0)
    output_tokens = usage.get("output_tokens", 0)
    cached_tokens = usage.get("cached_input_tokens", 0)
    
    pricing = CODEX_PRICING
    
    # Logic: new_input = max(0, input - cached)
    new_input = max(0, input_tokens - cached_tokens)
    
    input_cost = (new_input / 1_000_000) * pricing.input_per_million
    cached_cost = (cached_tokens / 1_000_000) * pricing.input_per_million * pricing.cached_input_multiplier
    output_cost = (output_tokens / 1_000_000) * pricing.output_per_million
    
    return input_cost + cached_cost + output_cost

def run_agentic_task(
    instruction: str,
    cwd: Path,
    *,
    verbose: bool = False,
    quiet: bool = False,
    label: str = "",
    timeout: Optional[float] = None,
    max_retries: int = 1,
    retry_delay: float = DEFAULT_RETRY_DELAY
) -> Tuple[bool, str, float, str]:
    """
    Runs an agentic task using available providers in preference order.

    Args:
        instruction: The task instruction
        cwd: Working directory
        verbose: Show detailed output
        quiet: Suppress all non-error output
        label: Task label for logging
        timeout: Optional timeout override
        max_retries: Number of attempts per provider before fallback (default: 1 = no retries)
        retry_delay: Base delay in seconds for exponential backoff (default: DEFAULT_RETRY_DELAY)

    Returns:
        (success, output_text, cost_usd, provider_used)
    """
    agents = get_available_agents()

    # Filter agents based on preference order
    candidates = [p for p in AGENT_PROVIDER_PREFERENCE if p in agents]

    if not candidates:
        msg = "No agent providers are available (check CLI installation and API keys)"
        if not quiet:
            console.print(f"[bold red]{msg}[/bold red]")
        return False, msg, 0.0, ""

    effective_timeout = timeout if timeout is not None else DEFAULT_TIMEOUT_SECONDS

    # Create a unique temp file for the prompt
    prompt_filename = f".agentic_prompt_{uuid.uuid4().hex[:8]}.txt"
    prompt_path = cwd / prompt_filename

    full_instruction = (
        f"{instruction}\n\n"
        f"Read the file {prompt_filename} for instructions. "
        "You have full file access to explore and modify files as needed."
    )

    try:
        # Write prompt to file
        with open(prompt_path, "w", encoding="utf-8") as f:
            f.write(full_instruction)

        for provider in candidates:
            if verbose:
                console.print(f"[dim]Attempting provider: {provider} for task '{label}'[/dim]")

            last_output = ""
            for attempt in range(1, max_retries + 1):
                if verbose and attempt > 1:
                    console.print(f"[dim]Retry {attempt}/{max_retries} for {provider} (task: {label})[/dim]")

                success, output, cost = _run_with_provider(
                    provider, prompt_path, cwd, effective_timeout, verbose, quiet
                )
                last_output = output

                # False Positive Detection
                # Issue #249: Empty output should ALWAYS be detected as false positive,
                # regardless of cost. Claude may consume tokens running tools but produce
                # no text response, which means the task wasn't actually completed.
                if success:
                    output_length = len(output.strip())
                    is_false_positive = (
                        output_length == 0 or  # Empty output is always a false positive
                        (cost == 0.0 and output_length < MIN_VALID_OUTPUT_LENGTH)  # Zero cost with short output
                    )

                    if is_false_positive:
                        if not quiet:
                            console.print(f"[yellow]Provider '{provider}' returned false positive (attempt {attempt})[/yellow]")
                        # Treat as failure, retry
                    else:
                        # Check for suspicious files (C, E, T)
                        suspicious = []
                        for name in ["C", "E", "T"]:
                            if (cwd / name).exists():
                                suspicious.append(name)

                        if suspicious:
                            console.print(f"[bold red]SUSPICIOUS FILES DETECTED: {', '.join(['- ' + s for s in suspicious])}[/bold red]")

                        # Real success
                        return True, output, cost, provider

                # Failed - retry with backoff if attempts remain
                if attempt < max_retries:
                    backoff = retry_delay * attempt
                    if verbose:
                        console.print(f"[dim]Waiting {backoff}s before retry...[/dim]")
                    time.sleep(backoff)

            # All retries exhausted for this provider
            if verbose:
                console.print(f"[yellow]Provider {provider} failed after {max_retries} attempts: {last_output}[/yellow]")

        return False, "All agent providers failed", 0.0, ""

    finally:
        # Cleanup prompt file
        if prompt_path.exists():
            try:
                os.remove(prompt_path)
            except OSError:
                pass

def _run_with_provider(
    provider: str,
    prompt_path: Path,
    cwd: Path,
    timeout: float = DEFAULT_TIMEOUT_SECONDS,
    verbose: bool = False,
    quiet: bool = False,
    cli_path: Optional[str] = None
) -> Tuple[bool, str, float]:
    """
    Internal helper to run a specific provider's CLI.
    Returns (success, output_or_error, cost).

    Args:
        provider: Provider name (anthropic, google, openai)
        prompt_path: Path to the prompt file
        cwd: Working directory
        timeout: Timeout in seconds
        verbose: Verbose output
        quiet: Suppress output
        cli_path: Optional explicit CLI path (if None, uses _find_cli_binary)
    """

    # Prepare Environment
    env = os.environ.copy()
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CI"] = "1"

    # Get CLI binary name for this provider
    cli_name = CLI_COMMANDS.get(provider)
    if not cli_name:
        return False, f"Unknown provider {provider}", 0.0

    # Find CLI binary path (use explicit path if provided)
    if cli_path is None:
        cli_path = _find_cli_binary(cli_name)
    if not cli_path:
        return False, f"CLI '{cli_name}' not found. {_get_cli_diagnostic_info(cli_name)}", 0.0

    cmd: List[str] = []

    # Read prompt content for providers that pipe via stdin
    prompt_content = prompt_path.read_text(encoding="utf-8") if prompt_path.exists() else ""

    # Construct Command using discovered cli_path (Issue #234 fix)
    if provider == "anthropic":
        # Remove API key to force subscription auth if configured that way
        env.pop("ANTHROPIC_API_KEY", None)
        # Use -p - to pipe prompt as direct user message via stdin.
        # This prevents Claude from interpreting file-discovered instructions
        # as "automated bot workflow" and refusing to execute.
        cmd = [
            cli_path,
            "-p", "-",
            "--dangerously-skip-permissions",
            "--output-format", "json",
        ]
    elif provider == "google":
        # Do NOT use -p flag for Gemini. The -p flag passes text literally,
        # so passing a file path gives Gemini the path string instead of content.
        # Instead, pass a short instruction as positional argument telling Gemini
        # to read the prompt file (matches old _run_google_variants pattern).
        cmd = [
            cli_path,
            f"Read the file {prompt_path.name} for your full instructions and execute them.",
            "--yolo",
            "--output-format", "json"
        ]
    elif provider == "openai":
        cmd = [
            cli_path,
            "exec",
            "--full-auto",
            "--json",
            str(prompt_path)
        ]
    else:
        return False, f"Unknown provider {provider}", 0.0

    # For anthropic, pipe prompt content via stdin; others use file path in cmd
    stdin_content = prompt_content if provider == "anthropic" else None

    try:
        result = subprocess.run(
            cmd,
            cwd=cwd,
            env=env,
            input=stdin_content,
            capture_output=True,
            text=True,
            timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return False, "Timeout expired", 0.0
    except Exception as e:
        return False, str(e), 0.0

    if result.returncode != 0:
        return False, f"Exit code {result.returncode}: {result.stderr}", 0.0

    # Parse JSON Output
    try:
        # Handle JSONL output (Codex sometimes streams)
        output_str = result.stdout.strip()
        data = {}
        
        if provider == "openai" and "\n" in output_str:
            # Parse JSONL, look for result type
            lines = output_str.splitlines()
            for line in lines:
                try:
                    item = json.loads(line)
                    if item.get("type") == "result":
                        data = item
                        break
                except json.JSONDecodeError:
                    continue
            # If no result block found, try parsing last line
            if not data and lines:
                try:
                    data = json.loads(lines[-1])
                except:
                    pass
        else:
            data = json.loads(output_str)
            
        return _parse_provider_json(provider, data)
    except json.JSONDecodeError:
        # Fallback if CLI didn't output valid JSON (sometimes happens on crash)
        return False, f"Invalid JSON output: {result.stdout[:200]}...", 0.0

def _parse_provider_json(provider: str, data: Dict[str, Any]) -> Tuple[bool, str, float]:
    """
    Extracts (success, text_response, cost_usd) from provider JSON.
    """
    cost = 0.0
    output_text = ""

    try:
        if provider == "anthropic":
            # Anthropic usually provides direct cost
            cost = float(data.get("total_cost_usd", 0.0))
            # Result might be in 'result' or 'response'
            output_text = data.get("result") or data.get("response") or ""
            
        elif provider == "google":
            stats = data.get("stats", {})
            cost = _calculate_gemini_cost(stats)
            output_text = data.get("result") or data.get("response") or data.get("output") or ""

        elif provider == "openai":
            usage = data.get("usage", {})
            cost = _calculate_codex_cost(usage)
            output_text = data.get("result") or data.get("output") or ""

        return True, str(output_text), cost

    except Exception as e:
        return False, f"Error parsing {provider} JSON: {e}", 0.0


# --- GitHub State Persistence ---

def _build_state_marker(workflow_type: str, issue_number: int) -> str:
    return f"{GITHUB_STATE_MARKER_START}{workflow_type}:issue-{issue_number}"

def _serialize_state_comment(workflow_type: str, issue_number: int, state: Dict) -> str:
    marker = _build_state_marker(workflow_type, issue_number)
    json_str = json.dumps(state, indent=2)
    return f"{marker}\n{json_str}\n{GITHUB_STATE_MARKER_END}"

def _parse_state_from_comment(body: str, workflow_type: str, issue_number: int) -> Optional[Dict]:
    marker = _build_state_marker(workflow_type, issue_number)
    if marker not in body:
        return None
    
    try:
        # Extract content between marker and end marker
        start_idx = body.find(marker) + len(marker)
        end_idx = body.find(GITHUB_STATE_MARKER_END, start_idx)
        
        if end_idx == -1:
            return None
            
        json_str = body[start_idx:end_idx].strip()
        return json.loads(json_str)
    except (json.JSONDecodeError, ValueError):
        return None

def _find_state_comment(
    repo_owner: str, 
    repo_name: str, 
    issue_number: int, 
    workflow_type: str, 
    cwd: Path
) -> Optional[Tuple[int, Dict]]:
    """
    Returns (comment_id, state_dict) if found, else None.
    """
    if not shutil.which("gh"):
        return None

    try:
        # List comments
        cmd = [
            "gh", "api", 
            f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
            "--method", "GET"
        ]
        result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
        if result.returncode != 0:
            return None
            
        comments = json.loads(result.stdout)
        marker = _build_state_marker(workflow_type, issue_number)
        
        for comment in comments:
            body = comment.get("body", "")
            if marker in body:
                state = _parse_state_from_comment(body, workflow_type, issue_number)
                if state:
                    return comment["id"], state
                    
        return None
    except Exception:
        return None

def github_save_state(
    repo_owner: str, 
    repo_name: str, 
    issue_number: int, 
    workflow_type: str, 
    state: Dict, 
    cwd: Path, 
    comment_id: Optional[int] = None
) -> Optional[int]:
    """
    Creates or updates a GitHub comment with the state. Returns new/existing comment_id.
    """
    if not shutil.which("gh"):
        return None

    body = _serialize_state_comment(workflow_type, issue_number, state)
    
    try:
        if comment_id:
            # PATCH existing
            cmd = [
                "gh", "api",
                f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}",
                "-X", "PATCH",
                "-f", f"body={body}"
            ]
            res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
            if res.returncode == 0:
                return comment_id
        else:
            # POST new
            cmd = [
                "gh", "api",
                f"repos/{repo_owner}/{repo_name}/issues/{issue_number}/comments",
                "-X", "POST",
                "-f", f"body={body}"
            ]
            res = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
            if res.returncode == 0:
                data = json.loads(res.stdout)
                return data.get("id")
                
        return None
    except Exception:
        return None

def github_load_state(
    repo_owner: str, 
    repo_name: str, 
    issue_number: int, 
    workflow_type: str, 
    cwd: Path
) -> Tuple[Optional[Dict], Optional[int]]:
    """
    Wrapper to find state. Returns (state, comment_id).
    """
    result = _find_state_comment(repo_owner, repo_name, issue_number, workflow_type, cwd)
    if result:
        return result[1], result[0]
    return None, None

def github_clear_state(
    repo_owner: str, 
    repo_name: str, 
    issue_number: int, 
    workflow_type: str, 
    cwd: Path
) -> bool:
    """
    Deletes the state comment if it exists.
    """
    result = _find_state_comment(repo_owner, repo_name, issue_number, workflow_type, cwd)
    if not result:
        return True # Already clear
        
    comment_id = result[0]
    try:
        cmd = [
            "gh", "api",
            f"repos/{repo_owner}/{repo_name}/issues/comments/{comment_id}",
            "-X", "DELETE"
        ]
        subprocess.run(cmd, cwd=cwd, capture_output=True)
        return True
    except Exception:
        return False

def _should_use_github_state(use_github_state: bool) -> bool:
    if not use_github_state:
        return False
    if os.environ.get("PDD_NO_GITHUB_STATE") == "1":
        return False
    return True

# --- High Level State Wrappers ---

def load_workflow_state(
    cwd: Path, 
    issue_number: int, 
    workflow_type: str, 
    state_dir: Path, 
    repo_owner: str, 
    repo_name: str, 
    use_github_state: bool = True
) -> Tuple[Optional[Dict], Optional[int]]:
    """
    Loads state from GitHub (priority) or local file.
    Returns (state_dict, github_comment_id).
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"
    
    # Try GitHub first
    if _should_use_github_state(use_github_state):
        gh_state, gh_id = github_load_state(repo_owner, repo_name, issue_number, workflow_type, cwd)
        if gh_state:
            # Cache locally
            try:
                state_dir.mkdir(parents=True, exist_ok=True)
                with open(local_file, "w") as f:
                    json.dump(gh_state, f, indent=2)
            except Exception:
                pass # Ignore local cache errors
            return gh_state, gh_id

    # Fallback to local
    if local_file.exists():
        try:
            with open(local_file, "r") as f:
                return json.load(f), None
        except Exception:
            pass
            
    return None, None

def save_workflow_state(
    cwd: Path, 
    issue_number: int, 
    workflow_type: str, 
    state: Dict, 
    state_dir: Path, 
    repo_owner: str, 
    repo_name: str, 
    use_github_state: bool = True, 
    github_comment_id: Optional[int] = None
) -> Optional[int]:
    """
    Saves state to local file and GitHub.
    Returns updated github_comment_id.
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"
    
    # 1. Save Local
    try:
        state_dir.mkdir(parents=True, exist_ok=True)
        with open(local_file, "w") as f:
            json.dump(state, f, indent=2)
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to save local state: {e}[/yellow]")

    # 2. Save GitHub
    if _should_use_github_state(use_github_state):
        new_id = github_save_state(
            repo_owner, repo_name, issue_number, workflow_type, state, cwd, github_comment_id
        )
        if new_id:
            return new_id
        else:
            console.print("[dim]Warning: Failed to sync state to GitHub[/dim]")
            
    return github_comment_id

def clear_workflow_state(
    cwd: Path, 
    issue_number: int, 
    workflow_type: str, 
    state_dir: Path, 
    repo_owner: str, 
    repo_name: str, 
    use_github_state: bool = True
) -> None:
    """
    Clears local and GitHub state.
    """
    local_file = state_dir / f"{workflow_type}_state_{issue_number}.json"
    
    # Clear Local
    if local_file.exists():
        try:
            os.remove(local_file)
        except Exception:
            pass

    # Clear GitHub
    if _should_use_github_state(use_github_state):
        github_clear_state(repo_owner, repo_name, issue_number, workflow_type, cwd)