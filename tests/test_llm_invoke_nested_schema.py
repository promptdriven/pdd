"""
Test for nested additionalProperties: false requirement (OpenAI strict mode).

Issue: OpenAI's strict mode requires `additionalProperties: false` on ALL object
schemas in the hierarchy, not just the top level. The original fix (Issue #295)
only added it at the top level, causing errors like:

    "Invalid schema for response_format 'response': In context=('properties',
    'changes', 'items'), 'additionalProperties' is required to be supplied
    and to be false."

This test verifies that _add_additional_properties_false() recursively adds
the property to all nested objects.
"""

import pytest
from pdd.llm_invoke import _add_additional_properties_false


class TestNestedAdditionalPropertiesFalse:
    """Tests for recursive additionalProperties: false handling."""

    def test_adds_to_top_level_object(self):
        """Basic case: adds additionalProperties to top-level object."""
        schema = {
            "type": "object",
            "properties": {
                "name": {"type": "string"},
                "value": {"type": "integer"}
            },
            "required": ["name", "value"]
        }

        _add_additional_properties_false(schema)

        assert schema.get("additionalProperties") == False

    def test_adds_to_nested_object_in_properties(self):
        """Adds additionalProperties to nested objects within properties."""
        schema = {
            "type": "object",
            "properties": {
                "summary": {"type": "string"},
                "metadata": {
                    "type": "object",
                    "properties": {
                        "author": {"type": "string"},
                        "date": {"type": "string"}
                    },
                    "required": ["author", "date"]
                }
            },
            "required": ["summary", "metadata"]
        }

        _add_additional_properties_false(schema)

        # Top level
        assert schema.get("additionalProperties") == False
        # Nested object
        assert schema["properties"]["metadata"].get("additionalProperties") == False

    def test_adds_to_array_items_object(self):
        """Adds additionalProperties to objects inside array items.

        This is the exact case that was failing:
        In context=('properties', 'changes', 'items')
        """
        schema = {
            "type": "object",
            "properties": {
                "summary": {"type": "string"},
                "changes": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "properties": {
                            "change_type": {"type": "string"},
                            "description": {"type": "string"}
                        },
                        "required": ["change_type", "description"]
                    }
                }
            },
            "required": ["summary", "changes"]
        }

        _add_additional_properties_false(schema)

        # Top level
        assert schema.get("additionalProperties") == False
        # Array items object - THIS IS THE KEY ASSERTION
        assert schema["properties"]["changes"]["items"].get("additionalProperties") == False, \
            "BUG: additionalProperties: false missing from array items object. " \
            "OpenAI rejects with: In context=('properties', 'changes', 'items'), " \
            "'additionalProperties' is required to be supplied and to be false."

    def test_adds_to_deeply_nested_objects(self):
        """Adds additionalProperties to deeply nested structures."""
        schema = {
            "type": "object",
            "properties": {
                "sections": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "properties": {
                            "id": {"type": "string"},
                            "range": {
                                "type": "object",
                                "properties": {
                                    "startLine": {"type": "integer"},
                                    "endLine": {"type": "integer"}
                                },
                                "required": ["startLine", "endLine"]
                            },
                            "codeRanges": {
                                "type": "array",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "startLine": {"type": "integer"},
                                        "endLine": {"type": "integer"},
                                        "text": {"type": "string"}
                                    },
                                    "required": ["startLine", "endLine", "text"]
                                }
                            }
                        },
                        "required": ["id", "range"]
                    }
                }
            },
            "required": ["sections"]
        }

        _add_additional_properties_false(schema)

        # Check all levels
        assert schema.get("additionalProperties") == False, "Top level missing"

        section_item = schema["properties"]["sections"]["items"]
        assert section_item.get("additionalProperties") == False, "sections.items missing"

        range_obj = section_item["properties"]["range"]
        assert range_obj.get("additionalProperties") == False, "sections.items.range missing"

        code_range_item = section_item["properties"]["codeRanges"]["items"]
        assert code_range_item.get("additionalProperties") == False, "codeRanges.items missing"

    def test_handles_anyof_oneof_allof(self):
        """Adds additionalProperties to objects in anyOf/oneOf/allOf."""
        schema = {
            "type": "object",
            "properties": {
                "data": {
                    "anyOf": [
                        {
                            "type": "object",
                            "properties": {"name": {"type": "string"}},
                            "required": ["name"]
                        },
                        {
                            "type": "object",
                            "properties": {"id": {"type": "integer"}},
                            "required": ["id"]
                        }
                    ]
                }
            }
        }

        _add_additional_properties_false(schema)

        assert schema.get("additionalProperties") == False
        assert schema["properties"]["data"]["anyOf"][0].get("additionalProperties") == False
        assert schema["properties"]["data"]["anyOf"][1].get("additionalProperties") == False

    def test_handles_defs_references(self):
        """Adds additionalProperties to $defs (Pydantic reference definitions)."""
        schema = {
            "type": "object",
            "properties": {
                "item": {"$ref": "#/$defs/Item"}
            },
            "$defs": {
                "Item": {
                    "type": "object",
                    "properties": {
                        "name": {"type": "string"},
                        "nested": {
                            "type": "object",
                            "properties": {"value": {"type": "integer"}}
                        }
                    }
                }
            }
        }

        _add_additional_properties_false(schema)

        assert schema.get("additionalProperties") == False
        assert schema["$defs"]["Item"].get("additionalProperties") == False
        assert schema["$defs"]["Item"]["properties"]["nested"].get("additionalProperties") == False

    def test_does_not_modify_non_objects(self):
        """Doesn't add additionalProperties to non-object types."""
        schema = {
            "type": "object",
            "properties": {
                "name": {"type": "string"},
                "count": {"type": "integer"},
                "tags": {"type": "array", "items": {"type": "string"}}
            }
        }

        _add_additional_properties_false(schema)

        # Only the top-level object should have it
        assert schema.get("additionalProperties") == False
        # Primitives should NOT have it
        assert "additionalProperties" not in schema["properties"]["name"]
        assert "additionalProperties" not in schema["properties"]["count"]
        # Array of strings should NOT have it on items
        assert "additionalProperties" not in schema["properties"]["tags"].get("items", {})

    def test_idempotent(self):
        """Running multiple times doesn't cause issues."""
        schema = {
            "type": "object",
            "properties": {
                "nested": {
                    "type": "object",
                    "properties": {"x": {"type": "integer"}}
                }
            }
        }

        _add_additional_properties_false(schema)
        _add_additional_properties_false(schema)
        _add_additional_properties_false(schema)

        assert schema.get("additionalProperties") == False
        assert schema["properties"]["nested"].get("additionalProperties") == False
