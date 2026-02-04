"""
E2E Test for Issue #375 / #410: PDD tag handling in preprocessing pipeline

Issue #375 (original): architecture_sync.py sometimes saw doubled braces in
JSON from PDD metadata tags. The fix (commit ba62e379) added PDD tag protection
to double_curly() to keep braces single inside tags.

Issue #410 (regression): The PDD tag protection broke the format() pipeline.
llm_invoke.py calls prompt.format(**input_data) after preprocessing, and
single-braced JSON inside PDD tags was interpreted as format placeholders,
raising KeyError.

Root cause: architecture_sync.py reads RAW files (prompt_path.read_text()),
never preprocessed content. The PDD tag protection was unnecessary and harmful.

Fix: Remove PDD tag protection from double_curly(). All braces are doubled
uniformly. The fallback parser in parse_prompt_tags() (commit 6a1d77c4)
handles doubled braces as a safety net.

These E2E tests verify:
1. parse_prompt_tags() works on raw content (production path)
2. Preprocessed content survives .format() without KeyError (issue #410)
3. The fallback parser handles doubled braces (safety net)
"""

import pytest
from pathlib import Path
import json


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestProductionParsePath:
    """
    Tests for the production code path: architecture_sync reads raw files
    and parse_prompt_tags() extracts PDD metadata from unpreprocessed content.
    """

    def test_parse_prompt_tags_on_raw_content(self) -> None:
        """parse_prompt_tags() correctly parses raw prompt content."""
        from pdd.architecture_sync import parse_prompt_tags

        prompt_content = """<pdd-reason>Fixes validation errors in architecture.json</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "fix_architecture", "signature": "(arch: str, output: str)", "returns": "str"}
    ]
  }
}
</pdd-interface>
<pdd-dependency>agentic_arch_step7_validate_LLM.prompt</pdd-dependency>
% You are an expert software architect."""

        result = parse_prompt_tags(prompt_content)

        assert result['reason'] == 'Fixes validation errors in architecture.json'
        assert result['interface'] is not None
        assert result['interface']['type'] == 'module'
        assert result['interface']['module']['functions'][0]['name'] == 'fix_architecture'
        assert 'agentic_arch_step7_validate_LLM.prompt' in result['dependencies']

    def test_parse_prompt_tags_on_nested_json(self) -> None:
        """parse_prompt_tags() handles deeply nested JSON in raw content."""
        from pdd.architecture_sync import parse_prompt_tags

        prompt_content = """<pdd-reason>Complex module with nested interfaces</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "process_data",
        "signature": "(data: dict)",
        "returns": "dict",
        "parameters": {
          "data": {
            "type": "dict",
            "schema": {
              "items": {"type": "string"},
              "metadata": {"nested": {"deeply": "value"}}
            }
          }
        }
      }
    ]
  }
}
</pdd-interface>
% Complex module prompt."""

        result = parse_prompt_tags(prompt_content)

        assert result['interface'] is not None
        func = result['interface']['module']['functions'][0]
        assert func['parameters']['data']['schema']['metadata']['nested']['deeply'] == 'value'


class TestFormatPipelineSafety:
    """
    Tests for issue #410: preprocessed prompts must survive .format().

    The pipeline is: double_curly() → .format(**input_data)
    All braces must be doubled so .format() undoubles them safely.
    """

    def test_preprocessed_prompt_survives_format(self) -> None:
        """
        Issue #410 regression test: .format() on preprocessed prompt with
        PDD tags must not raise KeyError.
        """
        from pdd.preprocess import preprocess

        prompt = """<pdd-reason>Defines the User data model</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "User", "signature": "@dataclass class", "returns": "User"}
    ]
  }
}
</pdd-interface>
% Write the User data model."""

        processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

        try:
            formatted = processed.format()
        except KeyError as e:
            pytest.fail(
                f"Issue #410: .format() raised KeyError on preprocessed prompt: {e}\n"
                f"Preprocessed (first 300 chars): {processed[:300]}"
            )

        # JSON should be valid after undoubling
        import re
        match = re.search(r'<pdd-interface>(.*?)</pdd-interface>', formatted, re.DOTALL)
        assert match is not None
        parsed = json.loads(match.group(1).strip())
        assert parsed['type'] == 'module'

    def test_preprocessed_prompt_with_variables_survives_format(self) -> None:
        """
        Issue #410: Prompts with PDD tags AND template variables must work
        with .format(**input_data).
        """
        from pdd.preprocess import preprocess

        prompt = """<pdd-interface>
{"type": "module", "module": {"functions": [{"name": "format"}]}}
</pdd-interface>
% Format the {input_data} according to the {output_format} specification.

The output should be valid JSON like: {"result": "value"}
"""

        processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

        # .format(**{}) should succeed — the production call uses empty dict for pdd sync
        # double_curly() doubles all braces, .format() undoubles them back to original
        formatted = processed.format()

        # Template variables undoubled back to original single-brace form
        assert "{input_data}" in formatted
        assert "{output_format}" in formatted
        # Literal JSON outside tags gets undoubled back to single braces
        assert '{"result": "value"}' in formatted

    def test_real_world_prompt_end_to_end(self, tmp_path, monkeypatch) -> None:
        """
        Full E2E: raw parse → preprocess → format pipeline on a real-world prompt.
        """
        from pdd.preprocess import preprocess
        from pdd.architecture_sync import parse_prompt_tags

        prompt = """<pdd-reason>Fixes validation errors in architecture.json</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "fix_architecture", "signature": "(arch: str, output: str)", "returns": "str"}
    ]
  }
}
</pdd-interface>
<pdd-dependency>step7_validate.prompt</pdd-dependency>
% Fix validation errors.

% Inputs
- Issue URL: {issue_url}
- Repository: {repo_owner}/{repo_name}

% Current Architecture
<architecture_json>
{current_architecture}
</architecture_json>"""

        monkeypatch.chdir(tmp_path)

        # Step 1: Raw parse (production path for architecture_sync)
        raw_result = parse_prompt_tags(prompt)
        assert raw_result['interface'] is not None
        assert raw_result['interface']['type'] == 'module'

        # Step 2: Preprocess → format (production path for llm_invoke)
        # In production, llm_invoke calls prompt.format(**input_data) where
        # input_data={} for pdd sync. All {{...}} get undoubled to {...}.
        processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
        formatted = processed.format()

        # Template variables undoubled back to original single-brace form
        assert "{issue_url}" in formatted
        assert "{repo_owner}" in formatted

        # PDD tag JSON is valid after format undoubling
        import re
        match = re.search(r'<pdd-interface>(.*?)</pdd-interface>', formatted, re.DOTALL)
        assert match is not None
        parsed = json.loads(match.group(1).strip())
        assert parsed['module']['functions'][0]['name'] == 'fix_architecture'


class TestFallbackParserSafetyNet:
    """
    Tests that parse_prompt_tags() fallback parser handles doubled braces.

    This is a safety net (commit 6a1d77c4). In production, parse_prompt_tags()
    receives raw content. But if it ever receives preprocessed content, the
    fallback parser should handle it gracefully.
    """

    def test_parse_prompt_tags_handles_doubled_braces(self) -> None:
        """Fallback parser undoubles braces and parses JSON."""
        from pdd.architecture_sync import parse_prompt_tags

        # Simulate preprocessed content (all braces doubled)
        doubled_content = """<pdd-reason>Test module</pdd-reason>
<pdd-interface>
{{
  "type": "module",
  "module": {{
    "functions": [
      {{"name": "test", "signature": "(x: int)", "returns": "int"}}
    ]
  }}
}}
</pdd-interface>"""

        result = parse_prompt_tags(doubled_content)

        assert result['interface'] is not None, \
            f"Fallback parser should handle doubled braces: {result.get('interface_parse_error')}"
        assert result['interface']['type'] == 'module'

    def test_parse_prompt_tags_on_preprocessed_content(self) -> None:
        """parse_prompt_tags() works on content from preprocess()."""
        from pdd.preprocess import preprocess
        from pdd.architecture_sync import parse_prompt_tags

        prompt = """<pdd-interface>
{
  "type": "module",
  "module": {"functions": [{"name": "test"}]}
}
</pdd-interface>
% Template text."""

        processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
        result = parse_prompt_tags(processed)

        assert result['interface'] is not None, \
            f"parse_prompt_tags should handle preprocessed content: {result.get('interface_parse_error')}"
        assert result['interface']['type'] == 'module'
