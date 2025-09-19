from typing import Tuple, Optional, List
from rich import print
from rich.console import Console
from pydantic import BaseModel, Field
import difflib
import re
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .llm_invoke import llm_invoke
from . import DEFAULT_TIME, DEFAULT_STRENGTH
console = Console()


def _normalize_text(value: str) -> str:
    if value is None:
        return ""
    value = value.replace("\u201c", '"').replace("\u201d", '"')
    value = value.replace("\u2018", "'").replace("\u2019", "'")
    value = value.replace("\u00A0", " ")
    value = re.sub(r"\s+", " ", value.strip())
    return value


def _fallback_prompt_line(prompt_lines: List[str], code_str: str) -> int:
    """Best-effort deterministic fallback to select a prompt line."""
    normalized_code = _normalize_text(code_str).casefold()
    tokens = [tok for tok in re.split(r"\W+", normalized_code) if len(tok) >= 3]

    token_best_idx: Optional[int] = None
    token_best_hits = 0
    if tokens:
        for i, line in enumerate(prompt_lines, 1):
            normalized_line = _normalize_text(line).casefold()
            hits = sum(1 for tok in tokens if tok in normalized_line)
            if hits > token_best_hits:
                token_best_hits = hits
                token_best_idx = i
    if token_best_idx is not None and token_best_hits > 0:
        return token_best_idx

    for i, line in enumerate(prompt_lines, 1):
        if _normalize_text(line):
            return i
    return 1

class PromptLineOutput(BaseModel):
    prompt_line: str = Field(description="The line from the prompt file that matches the code")

def trace(
    code_file: str,
    code_line: int,
    prompt_file: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0,
    verbose: bool = False,
    time: float = DEFAULT_TIME
) -> Tuple[Optional[int], float, str]:
    """
    Trace a line of code back to its corresponding line in the prompt file.

    Args:
        code_file (str): Content of the code file
        code_line (int): Line number in the code file
        prompt_file (str): Content of the prompt file
        strength (float, optional): Model strength. Defaults to 0.5
        temperature (float, optional): Model temperature. Defaults to 0
        verbose (bool, optional): Whether to print detailed information. Defaults to False
        time (float, optional): Time parameter for LLM calls. Defaults to 0.25

    Returns:
        Tuple[Optional[int], float, str]: (prompt line number, total cost, model name)
    """
    try:
        # Input validation
        if not all([code_file, prompt_file]) or not isinstance(code_line, int):
            raise ValueError("Invalid input parameters")

        total_cost = 0
        model_name = ""

        # Step 1: Extract the code line string
        code_lines = code_file.splitlines()
        if code_line < 1 or code_line > len(code_lines):
            raise ValueError(f"Code line number {code_line} is out of range")
        code_str = code_lines[code_line - 1]

        # Step 2 & 3: Load and preprocess trace_LLM prompt
        trace_prompt = load_prompt_template("trace_LLM")
        if not trace_prompt:
            raise ValueError("Failed to load trace_LLM prompt template")
        trace_prompt = preprocess(trace_prompt, recursive=False, double_curly_brackets=False)

        # Step 4: First LLM invocation
        if verbose:
            console.print("[bold blue]Running trace analysis...[/bold blue]")

        trace_response = llm_invoke(
            prompt=trace_prompt,
            input_json={
                "CODE_FILE": code_file,
                "CODE_STR": code_str,
                "PROMPT_FILE": prompt_file
            },
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            time=time
        )

        total_cost += trace_response['cost']
        model_name = trace_response['model_name']

        # Step 5: Load and preprocess extract_promptline_LLM prompt
        extract_prompt = load_prompt_template("extract_promptline_LLM")
        if not extract_prompt:
            raise ValueError("Failed to load extract_promptline_LLM prompt template")
        extract_prompt = preprocess(extract_prompt, recursive=False, double_curly_brackets=False)

        # Step 6: Second LLM invocation
        if verbose:
            console.print("[bold blue]Extracting prompt line...[/bold blue]")

        extract_response = llm_invoke(
            prompt=extract_prompt,
            input_json={"llm_output": trace_response['result']},
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            output_pydantic=PromptLineOutput,
            time=time
        )

        total_cost += extract_response['cost']
        prompt_line_str = extract_response['result'].prompt_line

        # Step 7: Find matching line in prompt file using fuzzy matching
        prompt_lines = prompt_file.splitlines()
        best_match = None
        highest_ratio = 0.0

        if verbose:
            console.print(f"Searching for line: {prompt_line_str}")

        # Robust normalization for comparison
        # If the model echoed wrapper tags like <llm_output>...</llm_output>, extract inner text
        raw_search = prompt_line_str
        try:
            m = re.search(r"<\s*llm_output\s*>(.*?)<\s*/\s*llm_output\s*>", raw_search, flags=re.IGNORECASE | re.DOTALL)
            if m:
                raw_search = m.group(1)
        except Exception:
            pass

        normalized_search = _normalize_text(raw_search).casefold()
        best_candidate_idx = None
        best_candidate_len = 0

        for i, line in enumerate(prompt_lines, 1):
            normalized_line = _normalize_text(line).casefold()
            line_len = len(normalized_line)

            # Base similarity
            ratio = difflib.SequenceMatcher(None, normalized_search, normalized_line).ratio()

            # Boost if one contains the other, but avoid trivial/short lines
            if normalized_search and line_len >= 8:
                shorter = min(len(normalized_search), line_len)
                longer = max(len(normalized_search), line_len)
                length_ratio = shorter / longer if longer else 0.0
                if length_ratio >= 0.4 and (
                    normalized_search in normalized_line or normalized_line in normalized_search
                ):
                    ratio = max(ratio, 0.999)

            if verbose:
                console.print(f"Line {i}: '{line}' - Match ratio: {ratio}")

            # Track best candidate overall, skipping empty lines
            if line_len > 0:
                if ratio > highest_ratio:
                    highest_ratio = ratio
                    best_candidate_idx = i
                    best_candidate_len = line_len
                elif abs(ratio - highest_ratio) < 1e-6 and best_candidate_idx is not None:
                    # Tie-breaker: prefer longer normalized line
                    if line_len > best_candidate_len:
                        best_candidate_idx = i
                        best_candidate_len = line_len

            # Early exit on exact normalized equality
            if normalized_search == normalized_line:
                best_match = i
                highest_ratio = 1.0
                break

        # Decide on acceptance thresholds
        primary_threshold = 0.8  # lowered threshold for normal acceptance
        fallback_threshold = 0.6  # low-confidence fallback threshold

        if best_match is None and best_candidate_idx is not None:
            if highest_ratio >= primary_threshold:
                best_match = best_candidate_idx
            elif highest_ratio >= fallback_threshold:
                best_match = best_candidate_idx
                if verbose:
                    console.print(
                        f"[yellow]Low-confidence match selected (ratio={highest_ratio:.3f}).[/yellow]"
                    )

        # Step 7b: Multi-line window matching (sizes 2 and 3) if no strong single-line match
        if (best_match is None) or (highest_ratio < primary_threshold):
            if verbose:
                console.print("[blue]No strong single-line match; trying multi-line windows...[/blue]")

            win_best_ratio = 0.0
            win_best_idx: Optional[int] = None
            win_best_size = 0

            for window_size in (2, 3):
                if len(prompt_lines) < window_size:
                    continue
                for start_idx in range(1, len(prompt_lines) - window_size + 2):
                    window_lines = prompt_lines[start_idx - 1 : start_idx - 1 + window_size]
                    window_text = " ".join(window_lines)
                    normalized_window = normalize_text(window_text).casefold()
                    seg_len = len(normalized_window)
                    if seg_len == 0:
                        continue

                    ratio = difflib.SequenceMatcher(None, normalized_search, normalized_window).ratio()

                    # Containment boost under similar length condition
                    shorter = min(len(normalized_search), seg_len)
                    longer = max(len(normalized_search), seg_len)
                    length_ratio = (shorter / longer) if longer else 0.0
                    if (
                        normalized_search
                        and seg_len >= 8
                        and length_ratio >= 0.4
                        and (
                            normalized_search in normalized_window
                            or normalized_window in normalized_search
                        )
                    ):
                        ratio = max(ratio, 0.999)

                    if verbose:
                        console.print(
                            f"Window {start_idx}-{start_idx+window_size-1}: ratio={ratio}"
                        )

                    # Track best window, prefer higher ratio; tie-breaker: larger window, then longer segment
                    if ratio > win_best_ratio + 1e-6 or (
                        abs(ratio - win_best_ratio) < 1e-6
                        and (window_size > win_best_size or (window_size == win_best_size and seg_len > 0))
                    ):
                        win_best_ratio = ratio
                        win_best_idx = start_idx
                        win_best_size = window_size

            if win_best_idx is not None and win_best_ratio > highest_ratio:
                if win_best_ratio >= primary_threshold:
                    best_match = win_best_idx
                    highest_ratio = win_best_ratio
                elif win_best_ratio >= fallback_threshold and best_match is None:
                    best_match = win_best_idx
                    highest_ratio = win_best_ratio
                    if verbose:
                        console.print(
                            f"[yellow]Low-confidence multi-line match selected (ratio={win_best_ratio:.3f}).[/yellow]"
                        )

        # Step 7c: Deterministic fallback when LLM output cannot be matched reliably
        fallback_used = False
        if best_match is None:
            best_match = _fallback_prompt_line(prompt_lines, code_str)
            fallback_used = True

        # Step 8: Return results
        if verbose:
            console.print(f"[green]Found matching line: {best_match}[/green]")
            console.print(f"[green]Total cost: ${total_cost:.6f}[/green]")
            console.print(f"[green]Model used: {model_name}[/green]")
            if fallback_used:
                console.print("[yellow]Fallback matching heuristic was used.[/yellow]")

        return best_match, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error in trace function: {str(e)}[/bold red]")
        try:
            fallback_line = _fallback_prompt_line(prompt_file.splitlines(), code_file.splitlines()[code_line - 1] if 0 < code_line <= len(code_file.splitlines()) else "")
        except Exception:
            fallback_line = 1
        return fallback_line, 0.0, "fallback"
