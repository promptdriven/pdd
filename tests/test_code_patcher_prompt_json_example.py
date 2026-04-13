"""Regression test for issue #1145.

Validates the <output_json_example> block in code_patcher_LLM.prompt through
the same runtime preprocessing that incremental_code_generator applies:

    preprocess(prompt, double_curly_brackets=True, exclude_keys=...)

After preprocessing, double_curly() protects multiline {{...}} blocks with
__ALREADY_DOUBLED__...__END_ALREADY__ sentinels. This test restores those
sentinels to braces and then validates the resulting JSON structure — catching
both raw source typos (the original #1145 bug) and preprocessing regressions
that corrupt the example content.
"""
import json
import re
from pathlib import Path

from pdd.preprocess import preprocess

_PROMPT_PATH = (
    Path(__file__).resolve().parents[1]
    / "pdd"
    / "prompts"
    / "code_patcher_LLM.prompt"
)

# Same exclude_keys used in incremental_code_generator.py:122-126
_EXCLUDE_KEYS = ["ORIGINAL_PROMPT", "NEW_PROMPT", "EXISTING_CODE", "CHANGE_DESCRIPTION"]

_BLOCK_RE = re.compile(
    r"<output_json_example>(.*?)</output_json_example>", re.DOTALL
)

# Sentinels left by double_curly() for multiline doubled-brace blocks
_SENTINEL_RE = re.compile(
    r"__ALREADY_DOUBLED__(.*?)__END_ALREADY__", re.DOTALL
)


def test_code_patcher_output_json_example_parses_after_preprocessing() -> None:
    """The JSON example must be valid after runtime preprocessing.

    Reproduces the preprocessing from incremental_code_generator.py:
    1. Read code_patcher_LLM.prompt
    2. preprocess(..., double_curly_brackets=True, exclude_keys=_EXCLUDE_KEYS)
    3. Restore sentinels to braces, then unescape {{ -> { / }} -> }
    4. json.loads the result
    """
    raw = _PROMPT_PATH.read_text()
    preprocessed = preprocess(
        raw,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=_EXCLUDE_KEYS,
    )

    match = _BLOCK_RE.search(preprocessed)
    assert match, f"missing <output_json_example> block in {_PROMPT_PATH}"

    block = match.group(1).strip()

    # Restore multiline sentinels that double_curly() leaves behind
    restored = _SENTINEL_RE.sub(r'{\1}', block)

    # Unescape remaining double braces (what str.format() would do)
    formatted = restored.replace("{{", "{").replace("}}", "}")

    try:
        json.loads(formatted)
    except json.JSONDecodeError as exc:
        raise AssertionError(
            f"<output_json_example> is not valid JSON after preprocessing: {exc}\n"
            f"--- preprocessed block ---\n{block}\n"
            f"--- restored ---\n{restored}\n"
            f"--- formatted ---\n{formatted}"
        ) from exc
