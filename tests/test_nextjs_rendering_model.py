"""
Tests for Next.js App Router rendering model support (issue #626).

Verifies that pdd generates architecture entries with the correct rendering
model (server/client/hybrid) and that the templates enforce the Next.js
server/client component boundary constraints.
"""

import json
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

import pytest

from pdd.architecture_sync import (
    generate_tags_from_architecture,
    parse_prompt_tags,
)
from pdd.code_generator_main import (
    _parse_front_matter,
    _repair_architecture_interface_types,
)

# --- Helpers ---

TEMPLATES_DIR = Path(__file__).resolve().parent.parent / "pdd" / "templates"
ARCHITECTURE_TEMPLATE = TEMPLATES_DIR / "architecture" / "architecture_json.prompt"
GENERATE_PROMPT_TEMPLATE = TEMPLATES_DIR / "generic" / "generate_prompt.prompt"


def _load_architecture_schema() -> dict:
    """Parse the architecture template front matter and return the output_schema."""
    content = ARCHITECTURE_TEMPLATE.read_text(encoding="utf-8")
    meta, _ = _parse_front_matter(content)
    assert meta is not None, "Architecture template must have YAML front matter"
    schema = meta.get("output_schema")
    assert schema is not None, "Architecture template must have output_schema"
    return schema


def _get_page_schema(schema: dict) -> dict:
    """Navigate the output_schema to extract the page interface sub-schema."""
    items = schema.get("items", {})
    props = items.get("properties", {})
    interface = props.get("interface", {})
    interface_props = interface.get("properties", {})
    page = interface_props.get("page", {})
    return page


# =============================================================================
# Test 1: Schema defines renderingModel enum with server/client/hybrid
# =============================================================================

def test_schema_defines_rendering_model_enum():
    """
    Verify that the architecture template's output_schema defines a
    renderingModel property on the page interface with enum values
    server, client, and hybrid.

    On buggy code: The page interface schema has no renderingModel property,
    so pdd cannot structurally express whether a page is a server or client
    component.
    """
    schema = _load_architecture_schema()
    page_schema = _get_page_schema(schema)
    page_props = page_schema.get("properties", {})

    assert "renderingModel" in page_props, (
        "BUG DETECTED (Issue #626): page interface schema must include "
        "'renderingModel' field — without it, pdd cannot express whether a "
        "page is a server or client component"
    )

    rm_schema = page_props["renderingModel"]
    assert rm_schema.get("type") == "string", (
        "renderingModel must be a string type"
    )
    assert set(rm_schema.get("enum", [])) == {"server", "client", "hybrid"}, (
        f"renderingModel enum must be exactly {{server, client, hybrid}}, "
        f"got {rm_schema.get('enum')}"
    )


# =============================================================================
# Test 2: Schema rejects invalid renderingModel values
# =============================================================================

def test_schema_rendering_model_enum_rejects_invalid():
    """
    Verify that the architecture schema rejects an invalid renderingModel
    value like 'static' when validated with jsonschema.

    On buggy code: No renderingModel field exists, so there is nothing to
    reject — any value would pass or be silently ignored.
    """
    import jsonschema

    schema = _load_architecture_schema()
    page_schema = _get_page_schema(schema)
    page_props = page_schema.get("properties", {})

    # Skip gracefully if the field doesn't exist yet (test 1 already catches that)
    if "renderingModel" not in page_props:
        pytest.skip(
            "renderingModel not yet defined in schema — test 1 covers this gap"
        )

    # Build a minimal architecture entry with an invalid renderingModel
    invalid_entry = [
        {
            "reason": "Invalid rendering model test",
            "description": "Test page",
            "dependencies": [],
            "priority": 1,
            "filename": "test_page_TypeScriptReact.prompt",
            "filepath": "app/test/page.tsx",
            "interface": {
                "type": "page",
                "page": {
                    "route": "/test",
                    "renderingModel": "static"  # Invalid — not in enum
                }
            }
        }
    ]

    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(instance=invalid_entry, schema=schema)


# =============================================================================
# Test 3: Page interface without renderingModel still validates (backward compat)
# =============================================================================

def test_schema_rendering_model_is_optional():
    """
    Verify that a page interface entry without a renderingModel field still
    passes schema validation — the field should be optional for backward
    compatibility.
    """
    import jsonschema

    schema = _load_architecture_schema()

    entry_without_rm = [
        {
            "reason": "Backward compat test",
            "description": "Page without renderingModel",
            "dependencies": [],
            "priority": 1,
            "filename": "page_TypeScriptReact.prompt",
            "filepath": "app/page.tsx",
            "interface": {
                "type": "page",
                "page": {
                    "route": "/dashboard"
                }
            }
        }
    ]

    # Should NOT raise — renderingModel is optional
    jsonschema.validate(instance=entry_without_rm, schema=schema)


# =============================================================================
# Test 4: Architecture template contains rendering model guidance section
# =============================================================================

def test_architecture_template_contains_rendering_model_guidance():
    """
    Verify that the architecture template body contains a rendering model
    guidance section explaining the Next.js App Router server/client/hybrid
    component rules.

    On buggy code: The template has FRAMEWORK DETECTION and FILEPATH
    CONVENTIONS sections but no rendering model guidance, so the LLM has
    no constraints preventing it from mixing 'use client' with async.
    """
    content = ARCHITECTURE_TEMPLATE.read_text(encoding="utf-8")
    _, body = _parse_front_matter(content)

    body_lower = body.lower()
    assert "rendering model" in body_lower or "renderingmodel" in body_lower, (
        "BUG DETECTED (Issue #626): Architecture template must contain "
        "'NEXT.JS APP ROUTER RENDERING MODEL' section — without it, the LLM "
        "has no guidance on server/client component boundaries"
    )


# =============================================================================
# Test 5: Generate prompt template contains renderingModel enforcement
# =============================================================================

def test_generate_prompt_template_enforces_rendering_model():
    """
    Verify that the generate_prompt template references renderingModel and
    contains instructions for enforcing rendering model constraints in
    generated module prompts for Next.js pages.

    On buggy code: The template contains zero guidance about renderingModel,
    server/client boundaries, or 'use client' directive rules.
    """
    content = GENERATE_PROMPT_TEMPLATE.read_text(encoding="utf-8")
    _, body = _parse_front_matter(content)

    body_lower = body.lower()
    assert "renderingmodel" in body_lower or "rendering model" in body_lower or "rendering_model" in body_lower, (
        "BUG DETECTED (Issue #626): Generate prompt template must reference "
        "renderingModel — without it, generated module prompts won't enforce "
        "rendering boundaries"
    )


# =============================================================================
# Test 6: _repair_architecture_interface_types preserves page+renderingModel
# =============================================================================

def test_repair_preserves_page_rendering_model():
    """
    Verify that _repair_architecture_interface_types preserves the
    renderingModel field on a valid page interface without modifying it.
    """
    payload = [
        {
            "reason": "Admin page",
            "description": "Hybrid page",
            "dependencies": [],
            "priority": 1,
            "filename": "admin_page_TypeScriptReact.prompt",
            "filepath": "app/admin/page.tsx",
            "interface": {
                "type": "page",
                "page": {
                    "route": "/admin",
                    "renderingModel": "hybrid"
                }
            }
        }
    ]

    repaired, was_changed = _repair_architecture_interface_types(payload)

    # type is already valid ("page"), so it should NOT be changed
    assert not was_changed, (
        "Repair function should not change a valid page interface"
    )

    # renderingModel must be preserved
    page_data = repaired[0]["interface"]["page"]
    assert page_data.get("renderingModel") == "hybrid", (
        "Repair function must preserve the renderingModel field"
    )


# =============================================================================
# Test 7: Repair infers page type from nested key, preserving renderingModel
# =============================================================================

def test_repair_infers_page_type_preserves_rendering_model():
    """
    Verify that when _repair_architecture_interface_types encounters an
    invalid type (e.g., 'object') but finds a 'page' nested key, it
    repairs the type to 'page' while preserving renderingModel.
    """
    payload = [
        {
            "reason": "Admin page with wrong type",
            "description": "Should be repaired to page type",
            "dependencies": [],
            "priority": 1,
            "filename": "admin_page_TypeScriptReact.prompt",
            "filepath": "app/admin/page.tsx",
            "interface": {
                "type": "object",  # Wrong type — should be inferred as "page"
                "page": {
                    "route": "/admin",
                    "renderingModel": "server"
                }
            }
        }
    ]

    repaired, was_changed = _repair_architecture_interface_types(payload)

    # Type should be repaired from "object" to "page"
    assert was_changed, "Repair function should have fixed the type"
    assert repaired[0]["interface"]["type"] == "page", (
        "Repair should infer type='page' from the 'page' nested key"
    )

    # renderingModel must be preserved through the repair
    page_data = repaired[0]["interface"]["page"]
    assert page_data.get("renderingModel") == "server", (
        "Repair function must preserve renderingModel when fixing type"
    )


# =============================================================================
# Test 8: Architecture sync round-trip preserves renderingModel
# =============================================================================

def test_architecture_sync_round_trip_preserves_rendering_model():
    """
    Verify that renderingModel survives a full architecture sync round-trip:
    generate_tags_from_architecture → parse_prompt_tags.

    The architecture sync serializes interface data to XML tags and parses
    it back. renderingModel must be preserved through this cycle.
    """
    arch_entry = {
        "reason": "Admin dashboard page",
        "description": "Hybrid page with server data + client interactivity",
        "dependencies": ["auth_module.prompt"],
        "priority": 1,
        "filename": "admin_page_TypeScriptReact.prompt",
        "filepath": "app/admin/page.tsx",
        "interface": {
            "type": "page",
            "page": {
                "route": "/admin",
                "renderingModel": "hybrid",
                "dataSources": [
                    {
                        "kind": "api",
                        "source": "/api/hackathon/events",
                        "method": "GET",
                        "description": "Fetch events"
                    }
                ]
            }
        }
    }

    # Generate XML tags from architecture entry
    tags = generate_tags_from_architecture(arch_entry)

    # Parse the tags back
    parsed = parse_prompt_tags(tags)

    # Verify the round-trip preserved the interface
    assert parsed["interface"] is not None, (
        "parse_prompt_tags must return a non-None interface"
    )

    parsed_interface = parsed["interface"]
    assert parsed_interface.get("type") == "page", (
        "Round-trip must preserve interface type"
    )

    parsed_page = parsed_interface.get("page", {})
    assert parsed_page.get("renderingModel") == "hybrid", (
        "Round-trip must preserve renderingModel through "
        "generate_tags_from_architecture → parse_prompt_tags"
    )
    assert parsed_page.get("route") == "/admin", (
        "Round-trip must preserve route"
    )
