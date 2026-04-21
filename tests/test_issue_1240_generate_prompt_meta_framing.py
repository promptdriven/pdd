"""Regression test for issue #1240.

The `generate_prompt` template previously embedded meta-prompt framing into
generated .prompt files ("Create a prompt for generating..." at the top,
"Please produce production-ready prompt content..." at the bottom), which
caused `pdd sync` to sometimes produce 0-byte code files because the
code-generating LLM interpreted the meta-framing literally and emitted
prompt text instead of code.
"""

from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
TEMPLATE_PATH = REPO_ROOT / "pdd" / "templates" / "generic" / "generate_prompt.prompt"
MCP_TEMPLATE_PATH = REPO_ROOT / "utils" / "mcp" / "prompts" / "generate_prompt.prompt"


def _content(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_generate_prompt_template_has_no_meta_prompt_closing_line():
    """The output template must not contain a closing instruction that tells
    the downstream code-generating LLM to 'produce prompt content'. That line
    was being embedded verbatim into every generated .prompt file."""
    content = _content(TEMPLATE_PATH)
    assert "Please produce production-ready prompt content" not in content
    assert "produce production-ready prompt content that will generate" not in content


def test_generate_prompt_template_instruction_list_is_not_meta_framed():
    """The '% Do the following' instruction list must not instruct the LLM
    to 'create a prompt for the ${MODULE}'. That phrasing caused the LLM to
    echo meta-commentary ('I will create a prompt for generating...') into
    the top of generated .prompt files."""
    content = _content(TEMPLATE_PATH)
    assert "create a prompt for the ${MODULE}" not in content
    assert "create a prompt for generating" not in content.lower()


def test_mcp_generate_prompt_template_is_not_meta_framed():
    """The MCP scaffolding template at utils/mcp/prompts/generate_prompt.prompt
    has the same shape as the main generate_prompt template — it is a template
    whose LLM output becomes a .prompt file that is later used by pdd generate
    to produce code. The same meta-framing bug applies: if the instruction list
    tells the LLM to 'Explain what you are going to do' or 'Create the prompt
    for {module}', the output echoes that meta-phrasing and the downstream
    code-generating LLM produces prompt text instead of code."""
    content = _content(MCP_TEMPLATE_PATH)
    # Exact literal instruction patterns that caused the bug
    assert "Explain what you are going to do" not in content
    assert "Create the prompt for {module}" not in content
    # Sanity: no general meta-framing leaked in either
    assert "create a prompt for generating" not in content.lower()


def test_mcp_checked_in_python_prompts_are_not_meta_framed():
    """The MCP path has two stages: utils/mcp/generate_prompt.sh creates
    `utils/mcp/prompts/*_python.prompt` artifacts from the scaffold template,
    and utils/mcp/generate_python.sh then runs `pdd generate` on those
    artifacts to produce actual Python code (e.g. pdd generate prompts/main_python.prompt
    → pdd_mcp_server/main.py). Fixing only the scaffold leaves stale meta-framing
    inside the already-checked-in artifacts — so `pdd generate` on those
    artifacts still hits the 0-byte bug. Guard all `utils/mcp/prompts/*_python.prompt`
    files against meta-framing so the supported MCP code-generation path stays clean."""
    mcp_prompts_dir = REPO_ROOT / "utils" / "mcp" / "prompts"
    python_prompts = sorted(mcp_prompts_dir.glob("*_python.prompt"))
    # Sanity: the MCP package ships at least one artifact prompt
    assert python_prompts, f"no *_python.prompt files found under {mcp_prompts_dir}"

    # Each of these patterns reflects a way a prompt can instruct the
    # downstream code-generating LLM to produce prompt text instead of code.
    forbidden = (
        "write a prompt for generating",
        "write a prompt for the",
        "Please produce production-ready prompt content",
        "create a prompt for generating",
        "Explain what you are going to do",
        "Create the prompt for {module}",
    )
    failures: list[str] = []
    for prompt_path in python_prompts:
        text = prompt_path.read_text(encoding="utf-8")
        for needle in forbidden:
            if needle.lower() in text.lower():
                failures.append(f"{prompt_path.relative_to(REPO_ROOT)} contains {needle!r}")
    assert not failures, "meta-framing leaked into MCP artifact prompts:\n  " + "\n  ".join(failures)
