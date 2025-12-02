# tests/test_commands_templates.py
"""Tests for commands/templates."""
import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock

import pytest
from click.testing import CliRunner
import click

from pdd import cli, __version__, DEFAULT_STRENGTH, DEFAULT_TIME

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


@patch('pdd.template_registry.list_templates')
def test_cli_templates_list_default(mock_list_templates, runner):
    """`pdd templates list` should pretty-print template metadata."""
    mock_list_templates.return_value = [
        {
            "name": "architecture/architecture_json",
            "description": "Architecture outline",
            "version": "1.0.0",
            "tags": ["architecture", "json"],
        }
    ]

    result = runner.invoke(cli.templates_group, ["list"])

    assert result.exit_code == 0
    mock_list_templates.assert_called_once_with(None)
    assert "Available Templates" in result.output
    assert "architecture/architecture_json" in result.output
    assert "Architecture outline" in result.output

@patch('pdd.template_registry.list_templates')
def test_cli_templates_list_json_filter(mock_list_templates, runner):
    """`pdd templates list --json --filter` should return JSON and pass the filter tag."""
    payload = [
        {
            "name": "frontend/nextjs",
            "description": "Next.js app",
            "version": "2.0.0",
            "tags": ["frontend"],
        }
    ]
    mock_list_templates.return_value = payload

    result = runner.invoke(cli.templates_group, ["list", "--json", "--filter", "tag=frontend"])

    assert result.exit_code == 0
    mock_list_templates.assert_called_once_with("tag=frontend")

    import json as _json

    parsed = _json.loads(result.output)
    assert parsed == payload

@patch('pdd.template_registry.show_template')
def test_cli_templates_show_outputs_sections(mock_show_template, runner):
    """`pdd templates show` should render template metadata sections."""
    mock_show_template.return_value = {
        "summary": {
            "name": "architecture/architecture_json",
            "description": "Architecture outline",
            "version": "1.0.0",
            "tags": ["architecture"],
            "language": "json",
            "output": "architecture.json",
            "path": "/tmp/arch.prompt",
        },
        "variables": {"PRD_FILE": {"required": True, "type": "path"}},
        "usage": {"generate": [{"command": "pdd generate ..."}]},
        "discover": {"enabled": True},
        "output_schema": {"type": "object"},
        "notes": "Provide a PRD file.",
    }

    result = runner.invoke(cli.templates_group, ["show", "architecture/architecture_json"])

    assert result.exit_code == 0
    mock_show_template.assert_called_once_with("architecture/architecture_json")
    assert "Template Summary:" in result.output
    assert "Architecture outline" in result.output
    assert "Version" in result.output
    assert "Variables:" in result.output
    assert "Output Schema" in result.output
    assert "Provide a PRD file." in result.output

@patch('pdd.template_registry.copy_template')
def test_cli_templates_copy_invokes_registry(mock_copy_template, runner, tmp_path):
    """`pdd templates copy` should copy via the registry and report the destination."""
    destination = tmp_path / "prompts" / "architecture" / "architecture_json.prompt"
    mock_copy_template.return_value = str(destination)

    result = runner.invoke(
        cli.templates_group,
        [
            "copy",
            "architecture/architecture_json",
            "--to",
            str(destination.parent),
        ],
    )

    assert result.exit_code == 0
    mock_copy_template.assert_called_once_with("architecture/architecture_json", str(destination.parent))
    assert "Copied to" in result.output
    assert "architecture_json.prompt" in result.output.replace("\n", "")

def test_cli_templates_group_registered():
    """Ensure the templates command group is reachable from the top-level CLI."""
    assert "templates" in cli.cli.commands
    assert cli.cli.commands["templates"] is cli.templates_group

# --- Global Options Tests ---

