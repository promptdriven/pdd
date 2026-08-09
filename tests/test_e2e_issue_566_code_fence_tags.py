"""
E2E regression test for Issue #566: parse_prompt_tags extracts example tags
inside code fences as real metadata.

When a prompt file contains example <pdd-*> tags inside markdown code fences
(```xml ... ```), parse_prompt_tags() incorrectly extracts them as real
metadata, overwriting actual declarations at the top of the file.

These tests exercise the full architecture sync pipeline:
  prompt file on disk → update_architecture_from_prompt() → architecture.json

No mocking of the buggy component — hits the real parse_prompt_tags() path.
"""

import json
from pathlib import Path

from pdd.architecture_sync import (
    parse_prompt_tags,
    update_architecture_from_prompt,
    sync_all_prompts_to_architecture,
)


# ---------------------------------------------------------------------------
# Helper: set up a realistic project directory with prompts/ + architecture.json
# ---------------------------------------------------------------------------

def _setup_project(tmp_path, prompt_filename, prompt_content, arch_entry):
    """
    Create a minimal project layout that update_architecture_from_prompt() expects:
      tmp_path/
        prompts/<prompt_filename>   ← the prompt file
        architecture.json           ← array with one module entry
    """
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / prompt_filename).write_text(prompt_content, encoding="utf-8")

    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps([arch_entry], indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    return prompts_dir, arch_path


# ---------------------------------------------------------------------------
# Test 1: Real tags + fenced example tags — only real tags extracted
# ---------------------------------------------------------------------------

class TestIssue566CodeFenceTagsE2E:
    """
    E2E: Full update_architecture_from_prompt with real filesystem to verify
    that example tags inside markdown code fences are ignored.
    """

    def test_fenced_example_tags_do_not_overwrite_real_tags(self, tmp_path):
        """
        BUG: When a prompt file has real <pdd-reason> at the top and an
        example <pdd-reason> inside a code fence, the parser should use the
        real tag, not the fenced example.

        The actual bug: lxml's .find() returns the *first* matching element,
        which may be the fenced example if it appears first in the document.
        """
        prompt_content = """\
<pdd-reason>Real reason for this module</pdd-reason>
<pdd-dependency>real_dep_python.prompt</pdd-dependency>

% Instructions

Here is an example of how to write tags:

```xml
<pdd-reason>Example reason shown in documentation</pdd-reason>
<pdd-dependency>example_dep_python.prompt</pdd-dependency>
```
"""
        prompts_dir, arch_path = _setup_project(
            tmp_path,
            "my_module_python.prompt",
            prompt_content,
            {
                "name": "my_module",
                "filename": "my_module_python.prompt",
                "reason": "Old reason",
                "dependencies": [],
            },
        )

        result = update_architecture_from_prompt(
            "my_module_python.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        assert result["success"], f"Sync failed: {result.get('error')}"

        # Reload architecture.json and verify
        arch = json.loads(arch_path.read_text(encoding="utf-8"))
        module = arch[0]

        # The reason must be the REAL tag, not the fenced example
        assert module["reason"] == "Real reason for this module", (
            f"Expected real reason, got '{module['reason']}'. "
            "parse_prompt_tags() extracted the fenced example tag."
        )

        # Dependencies must contain only the real dep, not the fenced example
        assert module["dependencies"] == ["real_dep_python.prompt"], (
            f"Expected only real dependency, got {module['dependencies']}. "
            "parse_prompt_tags() extracted dependencies from inside a code fence."
        )

    def test_real_header_tag_not_overwritten_by_fenced_example_in_body(self, tmp_path):
        """
        BUG: The buggy whole-file parser uses .find(), which returns the first
        match in document order.  When a fenced example exists in a body section
        the fenced tag is later in the file, so .find() still returns the correct
        header tag — but .findall() for dependencies collects BOTH.  More
        critically, prompts whose first % section contains the only pdd-* tags
        (the step10 pattern) will have those fenced tags extracted as real data.

        This test verifies the basic case: a prompt with a real header tag and a
        fenced example in a body section produces only the real header value.

        Fix: parse only the header (content before the first % line) so the body
        sections, including fenced examples, are never seen by the XML parser.
        """
        prompt_content = """\
<pdd-reason>Provides authentication utilities</pdd-reason>
<pdd-dependency>auth_helpers_python.prompt</pdd-dependency>

% Tag Format Examples

```xml
<pdd-reason>Example: Orchestrates the workflow</pdd-reason>
```
"""
        prompts_dir, arch_path = _setup_project(
            tmp_path,
            "auth_python.prompt",
            prompt_content,
            {
                "name": "auth",
                "filename": "auth_python.prompt",
                "reason": "Old auth reason",
                "dependencies": [],
            },
        )

        result = update_architecture_from_prompt(
            "auth_python.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        assert result["success"], f"Sync failed: {result.get('error')}"

        arch = json.loads(arch_path.read_text(encoding="utf-8"))
        module = arch[0]

        # Must be the real reason, not the fenced example
        assert module["reason"] == "Provides authentication utilities", (
            f"Expected real reason, got '{module['reason']}'. "
            "Fenced example tag was extracted because it appeared first."
        )

    def test_only_fenced_tags_produces_no_metadata(self, tmp_path):
        """
        BUG: A prompt file that has NO real tags — only examples inside code
        fences — should not produce any metadata. But the buggy parser
        extracts the fenced examples as real data.

        This mirrors the actual agentic_change_step10_architecture_update_LLM.prompt
        file which has zero real top-level tags.
        """
        prompt_content = """\
% Architecture Update Step

You are an expert software engineer. Update the architecture.

% Tag Format Examples

**Example `<pdd-reason>` tag:**
```xml
<pdd-reason>Orchestrates the 13-step agentic change workflow.</pdd-reason>
```

**Example `<pdd-dependency>` tags:**
```xml
<pdd-dependency>llm_invoke_python.prompt</pdd-dependency>
<pdd-dependency>path_resolution_python.prompt</pdd-dependency>
```
"""
        prompts_dir, arch_path = _setup_project(
            tmp_path,
            "step10_python.prompt",
            prompt_content,
            {
                "name": "step10",
                "filename": "step10_python.prompt",
                "reason": "Existing correct reason",
                "dependencies": ["existing_dep_python.prompt"],
            },
        )

        result = update_architecture_from_prompt(
            "step10_python.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        assert result["success"], f"Sync failed: {result.get('error')}"

        arch = json.loads(arch_path.read_text(encoding="utf-8"))
        module = arch[0]

        # With no real tags, the existing values should be preserved unchanged
        assert module["reason"] == "Existing correct reason", (
            f"Expected existing reason preserved, got '{module['reason']}'. "
            "Fenced example tags were extracted as real metadata."
        )
        assert module["dependencies"] == ["existing_dep_python.prompt"], (
            f"Expected existing deps preserved, got {module['dependencies']}. "
            "Fenced example dependency tags corrupted the architecture."
        )

    def test_sync_all_prompts_ignores_fenced_tags(self, tmp_path):
        """
        E2E: Exercise sync_all_prompts_to_architecture() — the highest-level
        entry point — with a multi-module architecture where one prompt has
        fenced example tags.
        """
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()

        # Module 1: clean prompt with real tags only
        (prompts_dir / "clean_python.prompt").write_text(
            "<pdd-reason>Clean module with real tags</pdd-reason>\n"
            "<pdd-dependency>utils_python.prompt</pdd-dependency>\n"
            "\n% Instructions\nDo clean things.\n",
            encoding="utf-8",
        )

        # Module 2: prompt with real tags AND fenced example tags
        (prompts_dir / "mixed_python.prompt").write_text(
            "<pdd-reason>Real mixed module reason</pdd-reason>\n"
            "<pdd-dependency>real_dep_python.prompt</pdd-dependency>\n"
            "\n% Examples\n\n"
            "```xml\n"
            "<pdd-reason>Example reason</pdd-reason>\n"
            "<pdd-dependency>example_dep_python.prompt</pdd-dependency>\n"
            "```\n",
            encoding="utf-8",
        )

        arch_path = tmp_path / "architecture.json"
        arch_data = [
            {
                "name": "clean",
                "filename": "clean_python.prompt",
                "reason": "Old clean reason",
                "dependencies": [],
            },
            {
                "name": "mixed",
                "filename": "mixed_python.prompt",
                "reason": "Old mixed reason",
                "dependencies": [],
            },
        ]
        arch_path.write_text(
            json.dumps(arch_data, indent=2) + "\n", encoding="utf-8"
        )

        result = sync_all_prompts_to_architecture(
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        assert result["success"], f"Sync failed: {result.get('errors')}"

        arch = json.loads(arch_path.read_text(encoding="utf-8"))

        # Clean module should work normally
        clean = arch[0]
        assert clean["reason"] == "Clean module with real tags"
        assert clean["dependencies"] == ["utils_python.prompt"]

        # Mixed module must use only real tags, not fenced examples
        mixed = arch[1]
        assert mixed["reason"] == "Real mixed module reason", (
            f"Expected real reason for mixed module, got '{mixed['reason']}'. "
            "sync_all_prompts extracted fenced example tags."
        )
        assert mixed["dependencies"] == ["real_dep_python.prompt"], (
            f"Expected only real dep, got {mixed['dependencies']}. "
            "Fenced example dependency was added by sync."
        )

    def test_real_prompt_file_step10_no_spurious_extraction(self, tmp_path):
        """
        Regression test using the actual content pattern from the file that
        triggered issue #566: agentic_change_step10_architecture_update_LLM.prompt.

        This prompt has NO real top-level tags — only instructional examples
        inside code fences. The parser must not extract anything.
        """
        # Simplified but faithful reproduction of the actual file structure
        prompt_content = """\
% Architecture Update Step

You are an expert software engineer. Your task is to update architecture.json
entries with the correct PDD metadata tags.

% Instructions

For each module, generate the following tags:

   b. Generate `<pdd-reason>` tag:
      - One-line summary of the module's purpose

   c. Generate `<pdd-interface>` tag:
      - JSON object describing the module's public interface

   d. Generate `<pdd-dependency>` tags:
      - One `<pdd-dependency>` tag per dependency

% Tag Format Examples

**Example `<pdd-reason>` tag:**
```xml
<pdd-reason>Orchestrates the 13-step agentic change workflow for implementing GitHub issues.</pdd-reason>
```

**Example `<pdd-interface>` tag (module type):**
```xml
<pdd-interface>
{{
  "type": "module",
  "module": {{
    "functions": [
      {{"name": "run_agentic_change_orchestrator", "signature": "(issue_url, issue_content, ...)", "returns": "Tuple[bool, str, float, str, List[str]]"}}
    ]
  }}
}}
</pdd-interface>
```

**Example `<pdd-dependency>` tags:**
```xml
<pdd-dependency>llm_invoke_python.prompt</pdd-dependency>
<pdd-dependency>path_resolution_python.prompt</pdd-dependency>
```
"""
        # Directly test parse_prompt_tags on this content
        tags = parse_prompt_tags(prompt_content)

        # No real tags exist, so nothing should be extracted
        assert tags["reason"] is None, (
            f"Expected no reason (no real tags), got '{tags['reason']}'. "
            "parse_prompt_tags() extracted a fenced example <pdd-reason>."
        )

        assert tags["dependencies"] == [], (
            f"Expected no dependencies (no real tags), got {tags['dependencies']}. "
            "parse_prompt_tags() extracted fenced example <pdd-dependency> tags."
        )
