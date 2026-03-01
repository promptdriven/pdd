"""
E2E tests for Issue #626: pdd generate mixes Next.js server and client component patterns.

These tests exercise the full code generation pipeline (CLI → template → front matter
→ schema extraction → LLM mock → validation/repair → output) to verify that:

1. The architecture template's output_schema defines a `renderingModel` enum field
   on the `page` interface, so the LLM can express server/client/hybrid intent.
2. The architecture template body contains rendering model guidance that teaches the
   LLM the rules for each rendering mode.
3. The generate_prompt template contains renderingModel enforcement instructions so
   that generated module prompts include the correct constraints.
4. The full pipeline correctly validates architecture JSON with renderingModel fields.
"""

import json
import os
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.code_generator_main import (
    _is_architecture_template,
    _parse_front_matter,
    _repair_architecture_interface_types,
)

# --- Helpers ---

PROJECT_ROOT = Path(__file__).resolve().parent.parent
TEMPLATES_DIR = PROJECT_ROOT / "pdd" / "templates"
ARCHITECTURE_TEMPLATE = TEMPLATES_DIR / "architecture" / "architecture_json.prompt"
GENERATE_PROMPT_TEMPLATE = TEMPLATES_DIR / "generic" / "generate_prompt.prompt"


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Ensure PDD_PATH is set so template loading works."""
    monkeypatch.setenv("PDD_PATH", str(PROJECT_ROOT))
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")


@pytest.fixture
def runner():
    """Provide a Click CLI test runner."""
    return CliRunner()


def _load_real_architecture_template():
    """Load the real architecture template and parse its front matter."""
    content = ARCHITECTURE_TEMPLATE.read_text(encoding="utf-8")
    meta, body = _parse_front_matter(content)
    assert meta is not None, "Architecture template must have YAML front matter"
    return meta, body


def _load_real_generate_prompt_template():
    """Load the real generate_prompt template and parse its front matter."""
    content = GENERATE_PROMPT_TEMPLATE.read_text(encoding="utf-8")
    meta, body = _parse_front_matter(content)
    assert meta is not None, "Generate prompt template must have YAML front matter"
    return meta, body


# =============================================================================
# E2E Test 1: Full pipeline — architecture template schema validates renderingModel
# =============================================================================

class TestArchitecturePipelineRenderingModel:
    """E2E tests exercising the architecture generation pipeline with renderingModel."""

    def test_architecture_schema_accepts_page_with_rendering_model(self):
        """
        E2E: Parse the REAL architecture template front matter, extract its
        output_schema, and validate that a page interface with renderingModel
        passes jsonschema validation.

        This exercises the full path: template file → _parse_front_matter() →
        output_schema extraction → jsonschema.validate().

        On buggy code: The page schema has no renderingModel property definition,
        so while JSON Schema won't reject unknown properties by default, this test
        verifies the schema DEFINES the field (not just tolerates it).
        """
        meta, body = _load_real_architecture_template()
        schema = meta.get("output_schema")
        assert schema is not None, "Architecture template must have output_schema"

        # Navigate to the page interface schema
        page_schema = (
            schema.get("items", {})
            .get("properties", {})
            .get("interface", {})
            .get("properties", {})
            .get("page", {})
        )
        page_props = page_schema.get("properties", {})

        # The page schema MUST define renderingModel as a property
        assert "renderingModel" in page_props, (
            "BUG DETECTED (Issue #626): The architecture template's page interface "
            "schema does not define a 'renderingModel' property. Without this field, "
            "pdd cannot express whether a Next.js page should be a server component, "
            "client component, or hybrid — leading to generated code that mixes "
            "'use client' with async functions and top-level await."
        )

        # Verify it's an enum with the correct values
        rm_schema = page_props["renderingModel"]
        assert rm_schema.get("type") == "string", (
            "renderingModel must be a string type"
        )
        assert set(rm_schema.get("enum", [])) == {"server", "client", "hybrid"}, (
            f"renderingModel enum must be exactly {{server, client, hybrid}}, "
            f"got {rm_schema.get('enum')}"
        )

    def test_full_pipeline_validates_architecture_with_rendering_model(self):
        """
        E2E: Simulate the full code_generator_main validation pipeline using
        the REAL architecture template's schema to validate a mock LLM output
        containing page entries with renderingModel fields.

        This exercises: template loading → front matter parsing → schema extraction
        → JSON parsing → _repair_architecture_interface_types() → jsonschema.validate()
        """
        import jsonschema

        meta, body = _load_real_architecture_template()
        output_schema = meta.get("output_schema")

        # Simulate LLM output: a Next.js architecture with page entries using renderingModel
        mock_architecture = [
            {
                "reason": "Admin dashboard needs server-side auth check and data fetching",
                "description": "Server component that fetches hackathon events and passes to client child",
                "dependencies": [],
                "priority": 1,
                "filename": "admin_hackathon_page_TypeScriptReact.prompt",
                "filepath": "app/admin/hackathon/page.tsx",
                "tags": ["frontend", "nextjs"],
                "interface": {
                    "type": "page",
                    "page": {
                        "route": "/admin/hackathon",
                        "renderingModel": "hybrid",
                        "dataSources": [
                            {
                                "kind": "api",
                                "source": "/api/hackathon/events",
                                "method": "GET",
                                "description": "Fetch hackathon events for admin dashboard"
                            }
                        ]
                    }
                }
            },
            {
                "reason": "Static marketing page with no interactivity",
                "description": "Server component rendering static content",
                "dependencies": [],
                "priority": 2,
                "filename": "landing_page_TypeScriptReact.prompt",
                "filepath": "app/page.tsx",
                "tags": ["frontend", "nextjs"],
                "interface": {
                    "type": "page",
                    "page": {
                        "route": "/",
                        "renderingModel": "server"
                    }
                }
            },
            {
                "reason": "Interactive settings form with client-side state",
                "description": "Client component with form state management",
                "dependencies": [],
                "priority": 3,
                "filename": "settings_page_TypeScriptReact.prompt",
                "filepath": "app/settings/page.tsx",
                "tags": ["frontend", "nextjs"],
                "interface": {
                    "type": "page",
                    "page": {
                        "route": "/settings",
                        "renderingModel": "client"
                    }
                }
            }
        ]

        # Run the repair function (same as code_generator_main does)
        assert _is_architecture_template(meta), "Template must be detected as architecture"
        repaired_payload, was_repaired = _repair_architecture_interface_types(mock_architecture)

        # Validate against the real schema
        jsonschema.validate(instance=repaired_payload, schema=output_schema)

        # Verify renderingModel values survived the pipeline
        for entry in repaired_payload:
            page_data = entry["interface"]["page"]
            assert "renderingModel" in page_data, (
                f"renderingModel was lost during pipeline processing for {entry['filename']}"
            )

    def test_pipeline_rejects_invalid_rendering_model_value(self):
        """
        E2E: Verify the full validation pipeline rejects a page with an invalid
        renderingModel value (e.g., "static" instead of server/client/hybrid).

        This exercises the same path as the LLM output validation in code_generator_main.
        """
        import jsonschema

        meta, body = _load_real_architecture_template()
        output_schema = meta.get("output_schema")

        page_schema = (
            output_schema.get("items", {})
            .get("properties", {})
            .get("interface", {})
            .get("properties", {})
            .get("page", {})
        )
        page_props = page_schema.get("properties", {})

        # Only test rejection if renderingModel is defined with enum
        if "renderingModel" not in page_props:
            pytest.fail(
                "BUG DETECTED (Issue #626): Cannot test invalid value rejection because "
                "renderingModel is not defined in the page interface schema. "
                "The schema must define renderingModel with enum: [server, client, hybrid]."
            )

        mock_architecture = [
            {
                "reason": "Page with invalid rendering model",
                "description": "This should fail validation",
                "dependencies": [],
                "priority": 1,
                "filename": "bad_page_TypeScriptReact.prompt",
                "filepath": "app/bad/page.tsx",
                "interface": {
                    "type": "page",
                    "page": {
                        "route": "/bad",
                        "renderingModel": "static"  # Invalid value
                    }
                }
            }
        ]

        repaired_payload, _ = _repair_architecture_interface_types(mock_architecture)

        with pytest.raises(jsonschema.ValidationError):
            jsonschema.validate(instance=repaired_payload, schema=output_schema)


# =============================================================================
# E2E Test 2: Architecture template body contains rendering model guidance
# =============================================================================

class TestArchitectureTemplateGuidance:
    """E2E tests verifying the architecture template provides rendering model guidance."""

    def test_architecture_template_body_has_rendering_model_section(self):
        """
        E2E: Read the REAL architecture template body and verify it contains
        a rendering model guidance section that teaches the LLM the rules for
        server/client/hybrid components.

        On buggy code: The template body has FRAMEWORK DETECTION and FILEPATH
        CONVENTIONS sections but NO rendering model guidance, so the LLM has
        no constraints preventing it from mixing 'use client' with async.
        """
        meta, body = _load_real_architecture_template()

        # The template must contain rendering model guidance
        assert "rendering model" in body.lower() or "renderingmodel" in body.lower(), (
            "BUG DETECTED (Issue #626): The architecture template body does not contain "
            "any rendering model guidance. Without this section, the LLM has no rules "
            "about Next.js server vs client components, leading to generated code that "
            "combines 'use client' with async functions and top-level await.\n\n"
            "Expected: A section explaining that server components can be async but "
            "cannot use hooks, client components can use hooks but cannot be async, "
            "and hybrid pages need a server wrapper passing data to a client child."
        )

        # Verify specific constraint keywords that must be present
        body_lower = body.lower()
        assert "'use client'" in body_lower or '"use client"' in body_lower, (
            "Architecture template must mention 'use client' directive rules"
        )
        assert "async" in body_lower, (
            "Architecture template must mention async component constraints"
        )
        assert "hook" in body_lower, (
            "Architecture template must mention hook usage constraints"
        )

    def test_interface_types_documentation_includes_rendering_model(self):
        """
        E2E: Verify the INTERFACE TYPES documentation section in the architecture
        template lists renderingModel as a property of the page interface.

        On buggy code: The INTERFACE TYPES section shows:
          page: route (string), params? (...), dataSources? (...), layout? (object)
        but does NOT mention renderingModel.
        """
        meta, body = _load_real_architecture_template()

        # Find the INTERFACE TYPES section
        assert "INTERFACE TYPES" in body, (
            "Architecture template must have an INTERFACE TYPES section"
        )

        # Extract the page line from INTERFACE TYPES
        lines = body.split("\n")
        page_doc_line = None
        for line in lines:
            stripped = line.strip()
            if stripped.startswith("- page:") and "route" in stripped:
                page_doc_line = stripped
                break

        assert page_doc_line is not None, (
            "Could not find page interface documentation line in INTERFACE TYPES section"
        )

        assert "renderingModel" in page_doc_line or "rendering_model" in page_doc_line, (
            f"BUG DETECTED (Issue #626): The INTERFACE TYPES documentation for 'page' "
            f"does not mention renderingModel.\n\n"
            f"Found: {page_doc_line}\n\n"
            f"Expected: renderingModel should be listed as a property of the page "
            f"interface so the LLM knows it exists and can use it."
        )


# =============================================================================
# E2E Test 3: Generate prompt template enforces rendering model constraints
# =============================================================================

class TestGeneratePromptRenderingModel:
    """E2E tests verifying the generate_prompt template enforces rendering model."""

    def test_generate_prompt_template_has_rendering_model_enforcement(self):
        """
        E2E: Read the REAL generate_prompt template and verify it contains
        instructions for enforcing renderingModel constraints when generating
        module prompts for Next.js pages.

        On buggy code: The generate_prompt template has an "Architecture awareness"
        section that says to describe "route/props/data sources" for pages but
        contains ZERO guidance about rendering model constraints.
        """
        meta, body = _load_real_generate_prompt_template()

        body_lower = body.lower()

        # The template must reference renderingModel
        assert "renderingmodel" in body_lower or "rendering model" in body_lower or "rendering_model" in body_lower, (
            "BUG DETECTED (Issue #626): The generate_prompt template does not reference "
            "renderingModel anywhere. Without this, generated module prompts for Next.js "
            "pages will have no constraints about server vs client component boundaries, "
            "leading to code that mixes 'use client' with async functions.\n\n"
            "Expected: The template should instruct the LLM to enforce renderingModel "
            "constraints (server → no 'use client'/hooks; client → no async; hybrid → "
            "server wrapper + client child) in the generated prompt's Requirements and "
            "Instructions sections."
        )

        # Verify it mentions the key constraint rules
        assert "'use client'" in body_lower or '"use client"' in body_lower, (
            "Generate prompt template must mention 'use client' directive constraints"
        )

    def test_generate_prompt_mentions_server_client_hybrid(self):
        """
        E2E: Verify the generate_prompt template mentions all three rendering
        model modes (server, client, hybrid) in its guidance.
        """
        meta, body = _load_real_generate_prompt_template()

        body_lower = body.lower()

        for mode in ["server", "client", "hybrid"]:
            assert mode in body_lower, (
                f"Generate prompt template must mention '{mode}' rendering mode. "
                f"Without guidance for all three modes, the LLM may not understand "
                f"the distinction between server, client, and hybrid components."
            )


# =============================================================================
# E2E Test 4: Full CLI pipeline with architecture template
# =============================================================================

class TestCLIPipelineE2E:
    """E2E tests exercising the full CLI → code_generator_main pipeline."""

    def test_cli_generate_architecture_schema_defines_rendering_model(self, runner, tmp_path):
        """
        E2E: Run `pdd generate --template architecture/architecture_json` with
        a mock LLM, then verify that the output_schema passed to the LLM
        defines the renderingModel field on the page interface.

        This exercises the full CLI path: command parsing → template resolution
        → template loading → front matter parsing → output_schema extraction →
        code_generator call. We capture the output_schema that reaches the LLM
        and verify it contains renderingModel.

        On buggy code: The output_schema extracted from the architecture template
        has no renderingModel in the page interface, so the LLM has no structured
        way to express server/client/hybrid rendering intent.
        """
        from pdd import cli

        # Create a minimal PRD file
        prd_file = tmp_path / "PRD.md"
        prd_file.write_text(
            "# Hackathon Platform\n"
            "Build a Next.js App Router application for managing hackathons.\n"
        )

        output_file = tmp_path / "architecture.json"

        # Capture the output_schema that reaches the code_generator
        captured_schema = {}

        mock_architecture_json = json.dumps([
            {
                "reason": "Admin dashboard",
                "description": "Page with data fetching",
                "dependencies": [],
                "priority": 1,
                "filename": "admin_page_TypeScriptReact.prompt",
                "filepath": "app/admin/page.tsx",
                "interface": {
                    "type": "page",
                    "page": {"route": "/admin", "renderingModel": "hybrid"}
                }
            }
        ], indent=2)

        def mock_code_generator(prompt, language, strength, temperature=0.0,
                                time=None, verbose=False, preprocess_prompt=True,
                                output_schema=None):
            """Capture output_schema and return mock architecture JSON."""
            captured_schema["schema"] = output_schema
            return (mock_architecture_json, 0.001, "mock-model")

        with patch("pdd.code_generator_main.local_code_generator_func", side_effect=mock_code_generator):
            result = runner.invoke(cli.cli, [
                "--local",
                "--force",
                "generate",
                "--template", "architecture/architecture_json",
                "-e", f"PRD_FILE={prd_file}",
                "--output", str(output_file),
            ], catch_exceptions=False)

        assert result.exit_code == 0, (
            f"CLI pipeline failed: {result.output}"
        )

        # Verify the output_schema was captured
        assert "schema" in captured_schema, (
            "output_schema was not passed to the code generator"
        )
        schema = captured_schema["schema"]
        assert schema is not None, "output_schema must not be None"

        # Navigate to the page interface schema
        page_schema = (
            schema.get("items", {})
            .get("properties", {})
            .get("interface", {})
            .get("properties", {})
            .get("page", {})
        )
        page_props = page_schema.get("properties", {})

        # The schema MUST define renderingModel
        assert "renderingModel" in page_props, (
            "BUG DETECTED (Issue #626): The output_schema passed to the LLM via "
            "the full CLI pipeline does not define 'renderingModel' on the page "
            "interface. This means the LLM has no structured field to express "
            "whether a Next.js page is a server, client, or hybrid component.\n\n"
            f"Page properties found: {list(page_props.keys())}\n"
            f"Missing: renderingModel (enum: server/client/hybrid)"
        )

        # Verify the enum values
        rm_schema = page_props["renderingModel"]
        assert set(rm_schema.get("enum", [])) == {"server", "client", "hybrid"}, (
            f"renderingModel enum must be {{server, client, hybrid}}, "
            f"got {rm_schema.get('enum')}"
        )

    def test_cli_pipeline_prompt_contains_rendering_model_guidance(self, runner, tmp_path):
        """
        E2E: Run `pdd generate --template architecture/architecture_json` and
        capture the prompt that reaches the LLM. Verify it contains rendering
        model guidance.

        On buggy code: The prompt reaching the LLM has FRAMEWORK DETECTION and
        FILEPATH CONVENTIONS but NO rendering model guidance sections.
        """
        from pdd import cli

        prd_file = tmp_path / "PRD.md"
        prd_file.write_text(
            "# Hackathon Platform\n"
            "Build a Next.js App Router app for hackathon management.\n"
        )

        output_file = tmp_path / "architecture.json"
        captured_prompt = {}

        mock_json = json.dumps([{
            "reason": "Page",
            "description": "A page",
            "dependencies": [],
            "priority": 1,
            "filename": "page_TypeScriptReact.prompt",
            "filepath": "app/page.tsx",
            "interface": {"type": "page", "page": {"route": "/"}}
        }], indent=2)

        def mock_code_generator(prompt, language, strength, temperature=0.0,
                                time=None, verbose=False, preprocess_prompt=True,
                                output_schema=None):
            """Capture the prompt and return mock JSON."""
            captured_prompt["prompt"] = prompt
            return (mock_json, 0.001, "mock-model")

        with patch("pdd.code_generator_main.local_code_generator_func", side_effect=mock_code_generator):
            result = runner.invoke(cli.cli, [
                "--local",
                "--force",
                "generate",
                "--template", "architecture/architecture_json",
                "-e", f"PRD_FILE={prd_file}",
                "--output", str(output_file),
            ], catch_exceptions=False)

        assert result.exit_code == 0, f"CLI failed: {result.output}"
        assert "prompt" in captured_prompt, "Prompt was not captured"

        prompt = captured_prompt["prompt"].lower()

        # The prompt reaching the LLM must contain rendering model guidance
        assert "rendering model" in prompt or "renderingmodel" in prompt, (
            "BUG DETECTED (Issue #626): The prompt reaching the LLM through the "
            "full CLI pipeline does not contain any rendering model guidance. "
            "Without this, the LLM has no instructions about Next.js server vs "
            "client component boundaries when generating architecture JSON.\n\n"
            "The prompt contains FRAMEWORK DETECTION and FILEPATH CONVENTIONS "
            "but NO rendering model rules."
        )
