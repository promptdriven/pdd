"""
Regression tests for issue #806: Fix and auto-deps commands creating
duplicate prompt files in wrong directory structure.

Background: When input_file_dirs is provided but context config also exists,
fix and auto-deps commands should prioritize input_file_dirs to preserve
the original directory structure and prevent path duplication.
"""
import os
import sys
import pytest
from pathlib import Path
from pdd.generate_output_paths import generate_output_paths


class TestFixAutoDepsDuplicationBugPrevention:
    """
    Test for the fix to issue #806: Fix and auto-deps commands creating
    duplicate prompt files in wrong directory structure.
    
    Background: When input_file_dirs is provided but context config also exists,
    fix and auto-deps commands should prioritize input_file_dirs to preserve
    the original directory structure and prevent path duplication.
    """
    
    def test_fix_command_prioritizes_input_file_dirs_over_context_config(self, tmp_path):
        """
        REGRESSION TEST for issue #806.
        
        When fix command is run with both input_file_dirs and context_config,
        it should prioritize input_file_dirs to prevent duplicate directory creation.
        
        Scenario:
        - .pddrc at project root with generate_output_path: "frontend/src"
        - Input file is in prompts/frontend/app/settings/billing/
        - Without fix: would create frontend/prompts/frontend/app/settings/billing/
        - With fix: correctly uses prompts/frontend/app/settings/billing/
        """
        project_root = tmp_path / "project"
        project_root.mkdir()
        
        # Create the directory structure
        prompt_dir = project_root / "prompts" / "frontend" / "app" / "settings" / "billing"
        prompt_dir.mkdir(parents=True)
        
        # Context config simulating .pddrc with frontend-specific path
        context_config = {
            "generate_output_path": "frontend/src",
            "test_output_path": "frontend/tests",
        }
        
        # Simulate construct_paths behavior for code and test outputs: it maps
        # fix outputs to the parent directories of the code_file and unit_test_file
        code_output_dir = project_root / context_config["generate_output_path"] / "app" / "settings" / "billing"
        test_output_dir = project_root / context_config["test_output_path"] / "app" / "settings" / "billing"
        code_output_dir.mkdir(parents=True, exist_ok=True)
        test_output_dir.mkdir(parents=True, exist_ok=True)
        
        # Input file dirs mapping - this is what construct_paths provides
        # when it detects input files are in specific directories
        input_file_dirs = {
            "output": str(prompt_dir),           # auto-deps uses 'output' key
            "output_code": str(code_output_dir), # fix uses 'output_code' key (parent of existing code file)
            "output_test": str(test_output_dir), # fix uses 'output_test' key (parent of existing test file)
        }
        
        # Test fix command path resolution
        fix_result = generate_output_paths(
            command="fix",
            output_locations={},
            basename="page",
            language="TypescriptReact", 
            file_extension=".tsx",
            context_config=context_config,
            input_file_dir=str(prompt_dir),
            input_file_dirs=input_file_dirs,
            config_base_dir=str(project_root),
        )
        
        # Test auto-deps command path resolution
        autodeps_result = generate_output_paths(
            command="auto-deps",
            output_locations={},
            basename="page", 
            language="TypescriptReact",
            file_extension=".prompt",
            context_config=context_config,
            input_file_dir=str(prompt_dir),
            input_file_dirs=input_file_dirs,
            config_base_dir=str(project_root),
        )
        
        # Verify fix command uses input_file_dirs, not context config
        fix_code_path = Path(fix_result.get("output_code", ""))
        fix_test_path = Path(fix_result.get("output_test", ""))
        
        # Should be located directly in the specified directories (no duplicated segments)
        assert fix_code_path.parent == code_output_dir
        assert fix_test_path.parent == test_output_dir
        
        # Verify auto-deps command uses input_file_dirs, not context config
        autodeps_output_path = Path(autodeps_result.get("output", ""))
        
        # Should be located directly in the prompt_dir (no duplicated segments)
        assert autodeps_output_path.parent == prompt_dir
        
    def test_auto_deps_with_only_input_file_dir_fallback(self, tmp_path):
        """
        Test that auto-deps correctly falls back to input_file_dir when
        input_file_dirs doesn't have the 'output' key.
        
        This addresses Copilot comment about auto-deps not always having
        the 'output' key in input_file_dirs.
        """
        project_root = tmp_path / "project"
        project_root.mkdir()
        
        prompt_dir = project_root / "prompts" / "module"
        prompt_dir.mkdir(parents=True)
        
        context_config = {
            "generate_output_path": "src",
        }
        
        # No 'output' key in input_file_dirs
        input_file_dirs = {}
        
        result = generate_output_paths(
            command="auto-deps",
            output_locations={},
            basename="module",
            language="Python",
            file_extension=".prompt",
            context_config=context_config,
            input_file_dir=str(prompt_dir),
            input_file_dirs=input_file_dirs,
            config_base_dir=str(project_root),
        )
        
        output_path = Path(result.get("output", ""))
        # Should fall back to input_file_dir
        assert output_path.parent == prompt_dir
        
    def test_fix_without_context_config_preserves_default_behavior(self, tmp_path):
        """
        Test that fix command without context config doesn't trigger the
        input_file_dirs override (preserving default/env behavior).
        
        This addresses Copilot comment about gating the override on context_path.
        """
        project_root = tmp_path / "project"
        project_root.mkdir()
        
        code_dir = project_root / "src" / "components"
        code_dir.mkdir(parents=True)
        
        # No context config
        context_config = {}
        
        input_file_dirs = {
            "output_code": str(code_dir),
        }
        
        result = generate_output_paths(
            command="fix",
            output_locations={},
            basename="button",
            language="TypeScript",
            file_extension=".ts",
            context_config=context_config,
            input_file_dir=str(code_dir),
            input_file_dirs=input_file_dirs,
            config_base_dir=str(project_root),
        )
        
        # Without context config, should still use input_file_dirs (existing behavior)
        output_code = Path(result.get("output_code", ""))
        assert output_code.parent == code_dir
        
    def test_generate_command_continues_using_context_config_normally(self, tmp_path):
        """
        Verify that other commands (generate) continue using context_config
        normally and are not affected by the fix/auto-deps special handling.
        """
        project_root = tmp_path / "project"
        project_root.mkdir()
        
        prompt_dir = project_root / "prompts" / "feature"
        prompt_dir.mkdir(parents=True)
        
        src_dir = project_root / "src"
        src_dir.mkdir()
        
        context_config = {
            "generate_output_path": str(src_dir),
        }
        
        input_file_dirs = {
            "output_code": str(prompt_dir),  # This should be ignored for generate command
        }
        
        result = generate_output_paths(
            command="generate",
            output_locations={},
            basename="feature",
            language="Python",
            file_extension=".py",
            context_config=context_config,
            input_file_dir=str(prompt_dir),
            input_file_dirs=input_file_dirs,
            config_base_dir=str(project_root),
        )
        
        # Generate command should use context config, not input_file_dirs
        # Note: generate command returns 'output' key, not 'output_code'
        output = result.get("output", "")
        # Use Path for cross-platform compatibility
        output_path = Path(output)
        expected_parent = src_dir
        
        # Compare using Path objects for Windows compatibility
        assert output_path.parent == expected_parent, \
            f"Generate command should use context config path {expected_parent}, got {output_path.parent}"
        
    def test_explicit_output_path_with_slash_handling(self, tmp_path):
        """
        Test handling of explicit output paths with '/' to ensure
        the fix doesn't break existing slash-based path handling.
        """
        project_root = tmp_path / "project"
        project_root.mkdir()
        
        nested_dir = project_root / "deeply" / "nested" / "components"
        nested_dir.mkdir(parents=True)
        
        context_config = {
            "generate_output_path": "src/",  # Ends with slash
        }
        
        input_file_dirs = {
            "output_code": str(nested_dir),
        }
        
        result = generate_output_paths(
            command="fix",
            output_locations={
                "output_code": "custom/path/",  # User-specified path with slash
            },
            basename="widget",
            language="JavaScript",
            file_extension=".js",
            context_config=context_config,
            input_file_dir=str(nested_dir),
            input_file_dirs=input_file_dirs,
            config_base_dir=str(project_root),
        )
        
        # User-specified paths should take precedence
        output_code = result.get("output_code", "")
        assert "custom/path" in output_code or "custom\\path" in output_code  # Windows compat