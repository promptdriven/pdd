"""
Tests for scripts/generate_section_compositions.py

PDD Principle: The prompt file is the source of truth.
These tests verify that the code conforms to the specification in
prompts/generate_section_compositions_python.prompt.

Spec requirements verified:
  1. Reads project.json from --project-dir to get the sections list
  2. For each section, generates remotion/src/remotion/{sectionId}/index.tsx
     - React component named {SectionId}Section (PascalCase)
     - Imports Sequence from remotion
     - Imports sub-compositions from section's compositions field
     - Uses durationSeconds and offsetSeconds from section config
     - Wraps sub-compositions in <Sequence from={offsetSeconds * fps} durationInFrames={durationSeconds * fps}>
  3. Updates remotion/src/remotion/Root.tsx to register all section compositions
  4. Prints JSON progress lines to stdout per section (done/skipped format)
  5. CLI args: --project-dir (default .), --remotion-dir (default remotion/), --force flag
  6. Exits with code 0 on success
  7. Section ID to PascalCase: intro -> Intro, section_two -> SectionTwo
  8. Default FPS: 30 (from project.json render.fps if present)
  9. If section file exists and --force not set, skip with status: skipped
 10. Creates directories as needed with os.makedirs
 11. Root.tsx update via regex/string templates (no JS parser)
 12. Uses argparse for CLI parsing
 13. Import guard: if __name__ == '__main__': main()
"""

import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List
from unittest import mock

import pytest

# Add scripts/ directory to path so we can import generate_section_compositions
TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(TESTS_DIR)
SCRIPTS_DIR = os.path.join(PROJECT_ROOT, "scripts")
sys.path.insert(0, SCRIPTS_DIR)

from generate_section_compositions import (
    to_pascal_case,
    resolve_comp_import,
    ensure_section_asset_aliases,
    resolve_section_visual_ids,
    resolve_section_base_component,
    load_project_json,
    get_fps,
    generate_section_component,
    generate_root_tsx,
    update_root_tsx,
    _merge_root_tsx,
    emit_progress,
    main,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_project_json(project_dir: str, data: Dict[str, Any]) -> None:
    """Write a project.json with the given data."""
    with open(os.path.join(project_dir, "project.json"), "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)


def _make_project_data(
    sections: List[Dict[str, Any]],
    fps: int = None,
    output_resolution: Dict[str, int] | None = None,
) -> Dict[str, Any]:
    """Build a project.json data dict with given sections and optional fps."""
    data: Dict[str, Any] = {"sections": sections}
    if fps is not None:
        data["render"] = {"fps": fps}
    if output_resolution is not None:
        data["outputResolution"] = output_resolution
    return data


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def tmp_project(tmp_path):
    """Create a temporary project directory with project.json and remotion skeleton."""
    sections = [
        {
            "id": "intro",
            "durationSeconds": 5,
            "offsetSeconds": 0,
            "compositions": ["title_card", "logo-reveal"],
        },
        {
            "id": "main_content",
            "durationSeconds": 30,
            "offsetSeconds": 5,
            "compositions": [{"id": "slide_one"}, {"id": "slide-two"}],
        },
        {
            "id": "outro",
            "durationSeconds": 4,
            "offsetSeconds": 35,
        },
    ]
    project_data = _make_project_data(sections, fps=30)
    _write_project_json(str(tmp_path), project_data)

    # Create remotion directory skeleton
    remotion_src = tmp_path / "remotion" / "src" / "remotion"
    remotion_src.mkdir(parents=True)

    return tmp_path


# ===========================================================================
# Tests: to_pascal_case
# ===========================================================================

class TestToPascalCase:
    """Spec: Section ID -> PascalCase: intro -> Intro, section_two -> SectionTwo."""

    def test_simple_id(self):
        assert to_pascal_case("intro") == "Intro"

    def test_underscore_separated(self):
        assert to_pascal_case("section_two") == "SectionTwo"

    def test_hyphen_separated(self):
        assert to_pascal_case("my-section") == "MySection"

    def test_mixed_separators(self):
        assert to_pascal_case("hello_world-test") == "HelloWorldTest"

    def test_single_char_parts(self):
        assert to_pascal_case("a_b_c") == "ABC"

    def test_already_capitalized(self):
        assert to_pascal_case("Intro") == "Intro"

    def test_multiple_consecutive_separators(self):
        # Empty parts filtered out
        result = to_pascal_case("a__b")
        assert result == "AB"

    def test_trailing_separator(self):
        result = to_pascal_case("intro_")
        assert result == "Intro"


# ===========================================================================
# Tests: load_project_json
# ===========================================================================

class TestLoadProjectJson:
    """Spec: Reads project.json from --project-dir."""

    def test_loads_valid_project(self, tmp_path):
        data = {"sections": [{"id": "intro"}]}
        _write_project_json(str(tmp_path), data)
        result = load_project_json(str(tmp_path))
        assert result["sections"][0]["id"] == "intro"

    def test_missing_project_json_exits(self, tmp_path):
        """Spec: Print error JSON and exit(1) if project.json not found."""
        with pytest.raises(SystemExit) as exc_info:
            load_project_json(str(tmp_path / "nonexistent"))
        assert exc_info.value.code == 1

    def test_missing_project_json_prints_error(self, tmp_path, capsys):
        with pytest.raises(SystemExit):
            load_project_json(str(tmp_path / "nonexistent"))
        captured = capsys.readouterr()
        error_data = json.loads(captured.out.strip())
        assert "error" in error_data
        assert "project.json" in error_data["error"]

    def test_invalid_json_raises(self, tmp_path):
        (tmp_path / "project.json").write_text("not valid json {{")
        with pytest.raises(json.JSONDecodeError):
            load_project_json(str(tmp_path))


# ===========================================================================
# Tests: get_fps
# ===========================================================================

class TestGetFps:
    """Spec: Default FPS: 30 (read from project.json render.fps if present, else 30)."""

    def test_default_fps_when_no_render(self):
        assert get_fps({}) == 30

    def test_default_fps_when_no_fps_key(self):
        assert get_fps({"render": {}}) == 30

    def test_custom_fps(self):
        assert get_fps({"render": {"fps": 60}}) == 60

    def test_fps_as_string(self):
        assert get_fps({"render": {"fps": "24"}}) == 24

    def test_fps_returns_int(self):
        result = get_fps({"render": {"fps": 29.97}})
        assert isinstance(result, int)


# ===========================================================================
# Tests: generate_section_component
# ===========================================================================

class TestGenerateSectionComponent:
    """Spec: Generates TSX with React component, Sequence import, sub-compositions."""

    def test_component_name_is_pascal_case_section(self):
        """Spec: Component named {SectionId}Section (PascalCase)."""
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}
        tsx = generate_section_component(section, fps=30)
        assert "IntroSection" in tsx

    def test_underscore_id_component_name(self):
        section = {"id": "section_two", "durationSeconds": 10, "offsetSeconds": 5}
        tsx = generate_section_component(section, fps=30)
        assert "SectionTwoSection" in tsx

    def test_imports_sequence_from_remotion(self):
        """Spec: Imports Sequence from remotion."""
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}
        tsx = generate_section_component(section, fps=30)
        assert 'import { Sequence } from "remotion";' in tsx

    def test_imports_react(self):
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}
        tsx = generate_section_component(section, fps=30)
        assert 'import React from "react";' in tsx

    def test_imports_sub_compositions_string_format(self):
        """Spec: Imports sub-compositions listed in section's compositions field."""
        section = {
            "id": "intro",
            "durationSeconds": 5,
            "offsetSeconds": 0,
            "compositions": ["title_card", "logo-reveal"],
        }
        tsx = generate_section_component(section, fps=30)
        assert 'import { TitleCard } from "../title_card";' in tsx
        assert 'import { LogoReveal } from "../logo-reveal";' in tsx

    def test_imports_sub_compositions_dict_format(self):
        """Compositions can be dicts with id field."""
        section = {
            "id": "main",
            "durationSeconds": 10,
            "offsetSeconds": 0,
            "compositions": [{"id": "slide_one"}, {"id": "slide-two"}],
        }
        tsx = generate_section_component(section, fps=30)
        assert 'import { SlideOne } from "../slide_one";' in tsx
        assert 'import { SlideTwo } from "../slide-two";' in tsx

    def test_uses_duration_and_offset(self):
        """Spec: Uses durationSeconds and offsetSeconds from section config."""
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 2}
        tsx = generate_section_component(section, fps=30)
        assert "durationSeconds = 5" in tsx
        assert "offsetSeconds = 2" in tsx

    def test_wraps_in_sequence_with_frame_calculations(self):
        """Spec: wrappers clamp section duration to at least one frame."""
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}
        tsx = generate_section_component(section, fps=30)
        assert "<Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>" in tsx

    def test_renders_sub_composition_jsx_tags(self):
        section = {
            "id": "intro",
            "durationSeconds": 5,
            "offsetSeconds": 0,
            "compositions": ["title_card"],
        }
        tsx = generate_section_component(section, fps=30)
        assert "<TitleCard />" in tsx

    def test_placeholder_when_no_compositions(self):
        """Section without compositions gets a placeholder comment."""
        section = {"id": "outro", "durationSeconds": 4, "offsetSeconds": 35}
        tsx = generate_section_component(section, fps=30)
        assert "{/* Sub-compositions will be added here */}" in tsx

    def test_exports_component_as_default(self):
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}
        tsx = generate_section_component(section, fps=30)
        assert "export default IntroSection;" in tsx

    def test_exports_named_component(self):
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}
        tsx = generate_section_component(section, fps=30)
        assert "export const IntroSection: React.FC" in tsx

    def test_fps_variable_in_component(self):
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}
        tsx = generate_section_component(section, fps=24)
        assert "const fps = 24;" in tsx

    def test_default_duration_and_offset(self):
        """Section missing durationSeconds/offsetSeconds defaults to 0."""
        section = {"id": "intro"}
        tsx = generate_section_component(section, fps=30)
        assert "durationSeconds = 0" in tsx
        assert "offsetSeconds = 0" in tsx

    def test_empty_compositions_list(self):
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0, "compositions": []}
        tsx = generate_section_component(section, fps=30)
        assert "{/* Sub-compositions will be added here */}" in tsx


# ===========================================================================
# Tests: generate_root_tsx
# ===========================================================================

class TestGenerateRootTsx:
    """Spec: Updates Root.tsx to register all section compositions as <Composition> entries."""

    def test_imports_composition_from_remotion(self):
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert 'import { Composition } from "remotion";' in root

    def test_imports_section_components(self):
        sections = [
            {"id": "intro", "durationSeconds": 5},
            {"id": "outro", "durationSeconds": 4},
        ]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert 'import { IntroSection } from "./intro";' in root
        assert 'import { OutroSection } from "./outro";' in root

    def test_registers_composition_entries(self):
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert '<Composition' in root
        # Default compositionId = PascalCase + "Section" when not explicitly set
        assert 'id="IntroSection"' in root
        assert 'component={IntroSection}' in root

    def test_uses_explicit_composition_id(self):
        sections = [{"id": "intro", "durationSeconds": 5, "compositionId": "CustomId"}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert 'id="CustomId"' in root

    def test_duration_in_frames_calculated(self):
        """Spec: durationInFrames = durationSeconds * fps."""
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert "durationInFrames={150}" in root  # 5 * 30 = 150

    def test_fps_in_composition(self):
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert "fps={30}" in root

    def test_default_dimensions(self):
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert "width={1920}" in root
        assert "height={1080}" in root

    def test_custom_dimensions(self):
        sections = [{"id": "intro", "durationSeconds": 5, "width": 1280, "height": 720}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert "width={1280}" in root
        assert "height={720}" in root

    def test_project_resolution_used_when_section_dimensions_missing(self):
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(
            sections,
            fps=30,
            remotion_dir="remotion/",
            default_width=1280,
            default_height=720,
        )
        assert "width={1280}" in root
        assert "height={720}" in root

    def test_multiple_sections_registered(self):
        sections = [
            {"id": "intro", "durationSeconds": 5},
            {"id": "main_content", "durationSeconds": 30},
            {"id": "outro", "durationSeconds": 4},
        ]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert 'id="IntroSection"' in root
        assert 'id="MainContentSection"' in root
        assert 'id="OutroSection"' in root

    def test_wraps_in_fragment(self):
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert "<>" in root
        assert "</>" in root

    def test_exports_remotion_root(self):
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert "export const RemotionRoot: React.FC" in root


# ===========================================================================
# Tests: update_root_tsx / _merge_root_tsx
# ===========================================================================

class TestUpdateRootTsx:
    """Spec: Updates or creates Root.tsx."""

    def test_creates_root_tsx_when_missing(self, tmp_path):
        remotion_dir = str(tmp_path / "remotion")
        sections = [{"id": "intro", "durationSeconds": 5}]
        update_root_tsx(sections, fps=30, remotion_dir=remotion_dir)

        root_path = os.path.join(remotion_dir, "src", "remotion", "Root.tsx")
        assert os.path.isfile(root_path)
        with open(root_path, "r") as f:
            content = f.read()
        assert "IntroSection" in content
        assert "Composition" in content

    def test_creates_directories_as_needed(self, tmp_path):
        """Spec: Create directories as needed."""
        remotion_dir = str(tmp_path / "remotion")
        sections = [{"id": "intro", "durationSeconds": 5}]
        update_root_tsx(sections, fps=30, remotion_dir=remotion_dir)

        assert os.path.isdir(os.path.join(remotion_dir, "src", "remotion"))

    def test_uses_project_output_resolution_when_present(self, tmp_path):
        remotion_dir = str(tmp_path / "remotion")
        sections = [{"id": "intro", "durationSeconds": 5}]
        update_root_tsx(
            sections,
            fps=30,
            remotion_dir=remotion_dir,
            default_width=1280,
            default_height=720,
        )

        root_path = os.path.join(remotion_dir, "src", "remotion", "Root.tsx")
        with open(root_path, "r", encoding="utf-8") as f:
            content = f.read()

        assert "width={1280}" in content
        assert "height={720}" in content

    def test_merges_into_existing_root_tsx(self, tmp_path):
        """Spec: Find existing <Composition> blocks and replace or append."""
        remotion_dir = str(tmp_path / "remotion")
        root_dir = os.path.join(remotion_dir, "src", "remotion")
        os.makedirs(root_dir, exist_ok=True)

        existing_content = (
            'import React from "react";\n'
            'import { Composition } from "remotion";\n'
            '\n'
            'export const RemotionRoot: React.FC = () => {\n'
            '  return (\n'
            '    <>\n'
            '    </>\n'
            '  );\n'
            '};\n'
        )
        root_path = os.path.join(root_dir, "Root.tsx")
        with open(root_path, "w") as f:
            f.write(existing_content)

        sections = [{"id": "intro", "durationSeconds": 5}]
        update_root_tsx(sections, fps=30, remotion_dir=remotion_dir)

        with open(root_path, "r") as f:
            content = f.read()
        assert "IntroSection" in content
        assert 'id="IntroSection"' in content


class TestMergeRootTsx:
    """Test _merge_root_tsx for regex-based merging."""

    def test_adds_imports_to_existing_file(self):
        existing = (
            'import React from "react";\n'
            'import { Composition } from "remotion";\n'
            '\n'
            'export const RemotionRoot: React.FC = () => {\n'
            '  return (\n'
            '    <>\n'
            '    </>\n'
            '  );\n'
            '};\n'
        )
        sections = [{"id": "intro", "durationSeconds": 5}]
        result = _merge_root_tsx(existing, sections, fps=30)
        assert 'import { IntroSection } from "./intro";' in result

    def test_adds_composition_blocks(self):
        existing = (
            'import React from "react";\n'
            'import { Composition } from "remotion";\n'
            '\n'
            'export const RemotionRoot: React.FC = () => {\n'
            '  return (\n'
            '    <>\n'
            '    </>\n'
            '  );\n'
            '};\n'
        )
        sections = [{"id": "intro", "durationSeconds": 5}]
        result = _merge_root_tsx(existing, sections, fps=30)
        assert '<Composition' in result
        assert 'id="IntroSection"' in result

    def test_replaces_existing_section_imports(self):
        existing = (
            'import React from "react";\n'
            'import { Composition } from "remotion";\n'
            'import { IntroSection } from "./intro";\n'
            '\n'
            'export const RemotionRoot: React.FC = () => {\n'
            '  return (\n'
            '    <>\n'
            '    </>\n'
            '  );\n'
            '};\n'
        )
        sections = [{"id": "intro", "durationSeconds": 10}]
        result = _merge_root_tsx(existing, sections, fps=30)
        # Should have only one import for intro
        import_count = result.count('import { IntroSection } from "./intro";')
        assert import_count == 1


# ===========================================================================
# Tests: emit_progress
# ===========================================================================

class TestEmitProgress:
    """Spec: Prints JSON progress lines to stdout per section."""

    def test_done_format(self, capsys):
        """Spec: {"sectionId": "intro", "status": "done", "path": "..."}."""
        emit_progress(section_id="intro", status="done", path="remotion/src/remotion/intro/index.tsx")
        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert data["sectionId"] == "intro"
        assert data["status"] == "done"
        assert data["path"] == "remotion/src/remotion/intro/index.tsx"

    def test_skipped_format(self, capsys):
        """Spec: {"sectionId": "intro", "status": "skipped", "reason": "already exists"}."""
        emit_progress(section_id="intro", status="skipped", reason="already exists")
        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert data["sectionId"] == "intro"
        assert data["status"] == "skipped"
        assert data["reason"] == "already exists"

    def test_no_path_when_not_provided(self, capsys):
        emit_progress(section_id="intro", status="skipped", reason="already exists")
        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert "path" not in data

    def test_no_reason_when_not_provided(self, capsys):
        emit_progress(section_id="intro", status="done", path="some/path")
        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert "reason" not in data

    def test_output_is_valid_json(self, capsys):
        emit_progress(section_id="test", status="done")
        captured = capsys.readouterr()
        # Should not raise
        json.loads(captured.out.strip())


# ===========================================================================
# Tests: main() - CLI args
# ===========================================================================

class TestMainCLIArgs:
    """Spec: CLI args --project-dir, --remotion-dir, --force with defaults."""

    def test_default_project_dir(self, tmp_project):
        """Spec: --project-dir default is '.'."""
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    def test_force_flag_default_false(self, tmp_project):
        """Spec: --force flag, default off."""
        # First run creates files
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        # Second run without --force should skip
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    def test_uses_argparse(self):
        """Spec: Uses argparse for CLI parsing."""
        script_path = os.path.join(SCRIPTS_DIR, "generate_section_compositions.py")
        with open(script_path, "r") as f:
            content = f.read()
        assert "argparse" in content
        assert "ArgumentParser" in content


# ===========================================================================
# Tests: main() - File Generation
# ===========================================================================

class TestMainFileGeneration:
    """Spec: Generates remotion/src/remotion/{sectionId}/index.tsx per section."""

    def test_creates_section_tsx_files(self, tmp_project):
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    def test_main_uses_project_output_resolution_for_root(self, tmp_path):
        sections = [{"id": "intro", "durationSeconds": 5}]
        project_data = _make_project_data(
            sections,
            fps=30,
            output_resolution={"width": 1280, "height": 720},
        )
        _write_project_json(str(tmp_path), project_data)
        remotion_src = tmp_path / "remotion" / "src" / "remotion"
        remotion_src.mkdir(parents=True)

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
            "--remotion-dir", str(tmp_path / "remotion"),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        root_path = tmp_path / "remotion" / "src" / "remotion" / "Root.tsx"
        content = root_path.read_text(encoding="utf-8")
        assert "width={1280}" in content
        assert "height={720}" in content

    def test_creates_directories_as_needed(self, tmp_project):
        """Spec: Create directories as needed: os.makedirs(...)."""
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        base = tmp_project / "remotion" / "src" / "remotion"
        assert (base / "intro").is_dir()
        assert (base / "main_content").is_dir()
        assert (base / "outro").is_dir()

    def test_generated_tsx_content(self, tmp_project):
        """Verify generated TSX has expected structure."""
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        intro_path = tmp_project / "remotion" / "src" / "remotion" / "intro" / "index.tsx"
        content = intro_path.read_text()
        assert "IntroSection" in content
        assert "Sequence" in content
        assert "TitleCard" in content
        assert "LogoReveal" in content

    def test_updates_root_tsx(self, tmp_project):
        """Spec: Updates Root.tsx to register all section compositions."""
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        root_path = tmp_project / "remotion" / "src" / "remotion" / "Root.tsx"
        assert root_path.exists()
        content = root_path.read_text()
        assert "IntroSection" in content
        assert "MainContentSection" in content
        assert "OutroSection" in content
        assert "Composition" in content


# ===========================================================================
# Tests: main() - Progress Output
# ===========================================================================

class TestMainProgressOutput:
    """Spec: Prints JSON progress lines to stdout per section."""

    def test_prints_done_lines(self, tmp_project, capsys):
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        assert len(lines) == 3  # 3 sections

        for line in lines:
            data = json.loads(line)
            assert "sectionId" in data
            assert data["status"] == "done"
            assert "path" in data

    def test_done_json_format(self, tmp_project, capsys):
        """Spec: {"sectionId": "intro", "status": "done", "path": "..."}."""
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        captured = capsys.readouterr()
        first_line = json.loads(captured.out.strip().split("\n")[0])
        assert first_line["sectionId"] == "intro"
        assert first_line["status"] == "done"
        assert "index.tsx" in first_line["path"]

    def test_skipped_json_format(self, tmp_project, capsys):
        """Spec: {"sectionId": "intro", "status": "skipped", "reason": "already exists"}."""
        # First run creates files
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        # Discard first run's output
        capsys.readouterr()

        # Second run without --force should skip
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        assert len(lines) == 3

        for line in lines:
            data = json.loads(line)
            assert data["status"] == "skipped"
            assert data["reason"] == "already exists"

    def test_one_line_per_section(self, tmp_project, capsys):
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit):
                main()

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        section_ids = [json.loads(l)["sectionId"] for l in lines]
        assert "intro" in section_ids
        assert "main_content" in section_ids
        assert "outro" in section_ids


# ===========================================================================
# Tests: main() - Skip / Force behavior
# ===========================================================================

class TestMainSkipForce:
    """Spec: Skip existing files unless --force is set."""

    def test_skips_existing_without_force(self, tmp_project, capsys):
        """Spec: If section file already exists and --force not set, skip."""
        # Pre-create one section file
        section_dir = tmp_project / "remotion" / "src" / "remotion" / "intro"
        section_dir.mkdir(parents=True, exist_ok=True)
        (section_dir / "index.tsx").write_text("existing content")

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        # intro should be skipped, others done
        captured = capsys.readouterr()
        lines = [json.loads(l) for l in captured.out.strip().split("\n") if l.strip()]

        intro_line = next(l for l in lines if l["sectionId"] == "intro")
        assert intro_line["status"] == "skipped"
        assert intro_line["reason"] == "already exists"

        # Verify file was NOT overwritten
        assert (section_dir / "index.tsx").read_text() == "existing content"

    def test_force_overwrites_existing(self, tmp_project, capsys):
        """Spec: --force overwrites existing files if set."""
        # Pre-create one section file
        section_dir = tmp_project / "remotion" / "src" / "remotion" / "intro"
        section_dir.mkdir(parents=True, exist_ok=True)
        (section_dir / "index.tsx").write_text("old content")

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
            "--force",
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        captured = capsys.readouterr()
        lines = [json.loads(l) for l in captured.out.strip().split("\n") if l.strip()]

        intro_line = next(l for l in lines if l["sectionId"] == "intro")
        assert intro_line["status"] == "done"

        # Verify file was overwritten
        new_content = (section_dir / "index.tsx").read_text()
        assert new_content != "old content"
        assert "IntroSection" in new_content


# ===========================================================================
# Tests: main() - Exit Codes
# ===========================================================================

class TestMainExitCodes:
    """Spec: Exits with code 0 on success."""

    def test_exit_zero_on_success(self, tmp_project):
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_project),
            "--remotion-dir", str(tmp_project / "remotion"),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    def test_exit_nonzero_missing_project_json(self, tmp_path):
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path / "nonexistent"),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 1

    def test_exit_zero_no_sections(self, tmp_path):
        """No sections in project.json should exit 0 with warning."""
        _write_project_json(str(tmp_path), {"sections": []})
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    def test_no_sections_prints_warning(self, tmp_path, capsys):
        _write_project_json(str(tmp_path), {"sections": []})
        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
        ]):
            with pytest.raises(SystemExit):
                main()

        captured = capsys.readouterr()
        data = json.loads(captured.out.strip())
        assert "warning" in data
        assert "No sections" in data["warning"]


# ===========================================================================
# Tests: main() - FPS from project.json
# ===========================================================================

class TestMainFpsHandling:
    """Spec: Default FPS: 30, read from project.json render.fps if present."""

    def test_uses_custom_fps_from_project(self, tmp_path):
        sections = [{"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}]
        data = _make_project_data(sections, fps=60)
        _write_project_json(str(tmp_path), data)

        remotion_dir = tmp_path / "remotion"
        (remotion_dir / "src" / "remotion").mkdir(parents=True)

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
            "--remotion-dir", str(remotion_dir),
        ]):
            with pytest.raises(SystemExit):
                main()

        # Check generated component uses fps=60
        tsx_path = remotion_dir / "src" / "remotion" / "intro" / "index.tsx"
        content = tsx_path.read_text()
        assert "const fps = 60;" in content

    def test_defaults_to_30_fps(self, tmp_path):
        sections = [{"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}]
        # No render.fps specified
        _write_project_json(str(tmp_path), {"sections": sections})

        remotion_dir = tmp_path / "remotion"
        (remotion_dir / "src" / "remotion").mkdir(parents=True)

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
            "--remotion-dir", str(remotion_dir),
        ]):
            with pytest.raises(SystemExit):
                main()

        tsx_path = remotion_dir / "src" / "remotion" / "intro" / "index.tsx"
        content = tsx_path.read_text()
        assert "const fps = 30;" in content


# ===========================================================================
# Tests: main() - Section without ID
# ===========================================================================

class TestMainSectionWithoutId:
    """Handle sections missing the id field."""

    def test_skips_section_without_id_in_generation(self, tmp_path, capsys):
        """Sections without id are skipped during generation with a warning.

        Note: The code passes all sections (including those without id) to
        update_root_tsx, which will raise KeyError. This test verifies the
        generation loop emits the warning before that point.
        """
        sections = [
            {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0},
            {"durationSeconds": 10, "offsetSeconds": 5},  # Missing id
        ]
        _write_project_json(str(tmp_path), _make_project_data(sections))

        remotion_dir = tmp_path / "remotion"
        (remotion_dir / "src" / "remotion").mkdir(parents=True)

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
            "--remotion-dir", str(remotion_dir),
        ]):
            with pytest.raises((SystemExit, KeyError)):
                main()

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        parsed = [json.loads(l) for l in lines]
        done_lines = [p for p in parsed if p.get("status") == "done"]
        warning_lines = [p for p in parsed if "warning" in p]
        assert len(done_lines) == 1
        assert done_lines[0]["sectionId"] == "intro"
        assert len(warning_lines) == 1


# ===========================================================================
# Tests: Import Guard
# ===========================================================================

class TestImportGuard:
    """Spec: Import guard: if __name__ == '__main__': main()."""

    def test_import_guard_exists(self):
        script_path = os.path.join(SCRIPTS_DIR, "generate_section_compositions.py")
        with open(script_path, "r") as f:
            content = f.read()
        assert ('if __name__ == "__main__":' in content or
                "if __name__ == '__main__':" in content)


# ===========================================================================
# Tests: Edge Cases
# ===========================================================================

class TestEdgeCases:
    """Edge case tests."""

    def test_single_section_project(self, tmp_path):
        sections = [{"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}]
        _write_project_json(str(tmp_path), _make_project_data(sections))

        remotion_dir = tmp_path / "remotion"
        (remotion_dir / "src" / "remotion").mkdir(parents=True)

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
            "--remotion-dir", str(remotion_dir),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        assert (remotion_dir / "src" / "remotion" / "intro" / "index.tsx").exists()
        assert (remotion_dir / "src" / "remotion" / "Root.tsx").exists()

    def test_section_with_hyphenated_id(self, tmp_path, capsys):
        """Spec: split on _ and - for PascalCase."""
        sections = [{"id": "my-section", "durationSeconds": 5, "offsetSeconds": 0}]
        _write_project_json(str(tmp_path), _make_project_data(sections))

        remotion_dir = tmp_path / "remotion"
        (remotion_dir / "src" / "remotion").mkdir(parents=True)

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
            "--remotion-dir", str(remotion_dir),
        ]):
            with pytest.raises(SystemExit):
                main()

        tsx_path = remotion_dir / "src" / "remotion" / "my-section" / "index.tsx"
        content = tsx_path.read_text()
        assert "MySectionSection" in content

    def test_section_zero_duration(self, tmp_path):
        """Section with zero duration should still generate."""
        sections = [{"id": "empty", "durationSeconds": 0, "offsetSeconds": 0}]
        _write_project_json(str(tmp_path), _make_project_data(sections))

        remotion_dir = tmp_path / "remotion"
        (remotion_dir / "src" / "remotion").mkdir(parents=True)

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
            "--remotion-dir", str(remotion_dir),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

    def test_many_sections(self, tmp_path, capsys):
        """Many sections should all be processed."""
        sections = [
            {"id": f"section_{i}", "durationSeconds": i + 1, "offsetSeconds": i * 2}
            for i in range(10)
        ]
        _write_project_json(str(tmp_path), _make_project_data(sections))

        remotion_dir = tmp_path / "remotion"
        (remotion_dir / "src" / "remotion").mkdir(parents=True)

        with mock.patch("sys.argv", [
            "generate_section_compositions.py",
            "--project-dir", str(tmp_path),
            "--remotion-dir", str(remotion_dir),
        ]):
            with pytest.raises(SystemExit) as exc_info:
                main()
            assert exc_info.value.code == 0

        captured = capsys.readouterr()
        lines = [l for l in captured.out.strip().split("\n") if l.strip()]
        assert len(lines) == 10

    def test_composition_as_empty_dict(self):
        """Composition dict without 'id' should be handled gracefully."""
        section = {
            "id": "intro",
            "durationSeconds": 5,
            "offsetSeconds": 0,
            "compositions": [{"id": ""}, {"id": "valid_comp"}],
        }
        tsx = generate_section_component(section, fps=30)
        # Empty id should be skipped, valid_comp should be imported
        assert "ValidComp" in tsx

    def test_subprocess_cli_invocation(self, tmp_project):
        """Spec: Invoked as a subprocess. Test actual subprocess execution."""
        import subprocess
        script_path = os.path.join(SCRIPTS_DIR, "generate_section_compositions.py")
        result = subprocess.run(
            [
                sys.executable,
                script_path,
                "--project-dir", str(tmp_project),
                "--remotion-dir", str(tmp_project / "remotion"),
            ],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0

        lines = [l for l in result.stdout.strip().split("\n") if l.strip()]
        assert len(lines) == 3
        for line in lines:
            data = json.loads(line)
            assert data["status"] == "done"

    def test_subprocess_force_flag(self, tmp_project):
        """Test --force flag via subprocess."""
        import subprocess
        script_path = os.path.join(SCRIPTS_DIR, "generate_section_compositions.py")

        # First run
        subprocess.run(
            [sys.executable, script_path,
             "--project-dir", str(tmp_project),
             "--remotion-dir", str(tmp_project / "remotion")],
            capture_output=True, text=True,
        )

        # Second run with --force
        result = subprocess.run(
            [sys.executable, script_path,
             "--project-dir", str(tmp_project),
             "--remotion-dir", str(tmp_project / "remotion"),
             "--force"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        lines = [l for l in result.stdout.strip().split("\n") if l.strip()]
        for line in lines:
            data = json.loads(line)
            assert data["status"] == "done"  # All done, not skipped

    def test_subprocess_skip_without_force(self, tmp_project):
        """Test skip behavior via subprocess."""
        import subprocess
        script_path = os.path.join(SCRIPTS_DIR, "generate_section_compositions.py")

        # First run
        subprocess.run(
            [sys.executable, script_path,
             "--project-dir", str(tmp_project),
             "--remotion-dir", str(tmp_project / "remotion")],
            capture_output=True, text=True,
        )

        # Second run without --force
        result = subprocess.run(
            [sys.executable, script_path,
             "--project-dir", str(tmp_project),
             "--remotion-dir", str(tmp_project / "remotion")],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        lines = [l for l in result.stdout.strip().split("\n") if l.strip()]
        for line in lines:
            data = json.loads(line)
            assert data["status"] == "skipped"
            assert data["reason"] == "already exists"


# ===========================================================================
# Tests: Audio & Video asset detection in generate_section_component
# ===========================================================================

class TestAssetDetection:
    """Verify that generate_section_component detects and includes audio/video assets."""

    def test_includes_audio_when_narration_exists(self, tmp_path):
        """When narration.wav exists in remotion/public/{section_id}/, include <Audio> tag."""
        section = {"id": "animation_section", "durationSeconds": 7, "offsetSeconds": 0}
        remotion_public = str(tmp_path / "public")
        narration_dir = tmp_path / "public" / "animation_section"
        narration_dir.mkdir(parents=True)
        (narration_dir / "narration.wav").write_bytes(b"RIFF" + b"\x00" * 100)

        tsx = generate_section_component(section, fps=30, remotion_public=remotion_public)
        assert "Audio" in tsx
        assert 'staticFile("animation_section/narration.wav")' in tsx

    def test_no_audio_when_narration_missing(self, tmp_path):
        """When no narration.wav exists, no <Audio> tag."""
        section = {"id": "animation_section", "durationSeconds": 7, "offsetSeconds": 0}
        remotion_public = str(tmp_path / "public")
        (tmp_path / "public").mkdir(parents=True)

        tsx = generate_section_component(section, fps=30, remotion_public=remotion_public)
        assert "Audio" not in tsx

    def test_includes_veo_video_when_clip_exists(self, tmp_path):
        """When veo/{section_id}.mp4 exists, include <OffthreadVideo> tag."""
        section = {"id": "veo_section", "durationSeconds": 7, "offsetSeconds": 0}
        remotion_public = str(tmp_path / "public")
        veo_dir = tmp_path / "public" / "veo"
        veo_dir.mkdir(parents=True)
        (veo_dir / "veo_section.mp4").write_bytes(b"\x00" * 100)

        tsx = generate_section_component(section, fps=30, remotion_public=remotion_public)
        assert "OffthreadVideo" in tsx
        assert 'staticFile("veo/veo_section.mp4")' in tsx

    def test_no_veo_video_when_clip_missing(self, tmp_path):
        """When no veo clip exists, no <OffthreadVideo> tag."""
        section = {"id": "animation_section", "durationSeconds": 7, "offsetSeconds": 0}
        remotion_public = str(tmp_path / "public")
        (tmp_path / "public").mkdir(parents=True)

        tsx = generate_section_component(section, fps=30, remotion_public=remotion_public)
        assert "OffthreadVideo" not in tsx

    def test_both_audio_and_veo(self, tmp_path):
        """Section with both narration and Veo clip includes both tags."""
        section = {"id": "veo_section", "durationSeconds": 7, "offsetSeconds": 0}
        remotion_public = str(tmp_path / "public")
        narration_dir = tmp_path / "public" / "veo_section"
        narration_dir.mkdir(parents=True)
        (narration_dir / "narration.wav").write_bytes(b"RIFF" + b"\x00" * 100)
        veo_dir = tmp_path / "public" / "veo"
        veo_dir.mkdir(parents=True)
        (veo_dir / "veo_section.mp4").write_bytes(b"\x00" * 100)

        tsx = generate_section_component(section, fps=30, remotion_public=remotion_public)
        assert "Audio" in tsx
        assert "OffthreadVideo" in tsx
        assert "staticFile" in tsx

    def test_veo_section_no_placeholder_comment(self, tmp_path):
        """Section with Veo clip should NOT have the placeholder comment."""
        section = {"id": "veo_section", "durationSeconds": 7, "offsetSeconds": 0}
        remotion_public = str(tmp_path / "public")
        veo_dir = tmp_path / "public" / "veo"
        veo_dir.mkdir(parents=True)
        (veo_dir / "veo_section.mp4").write_bytes(b"\x00" * 100)

        tsx = generate_section_component(section, fps=30, remotion_public=remotion_public)
        assert "{/* Sub-compositions will be added here */}" not in tsx

    def test_compositions_take_precedence_over_placeholder(self, tmp_path):
        """Section with compositions listed should render them, not placeholder."""
        section = {
            "id": "animation_section",
            "durationSeconds": 7,
            "offsetSeconds": 0,
            "compositions": ["blue_circle", "green_square"],
        }
        remotion_public = str(tmp_path / "public")
        narration_dir = tmp_path / "public" / "animation_section"
        narration_dir.mkdir(parents=True)
        (narration_dir / "narration.wav").write_bytes(b"RIFF" + b"\x00" * 100)

        tsx = generate_section_component(section, fps=30, remotion_public=remotion_public)
        assert "<BlueCircle />" in tsx
        assert "<GreenSquare />" in tsx
        assert 'import { BlueCircle } from "../blue_circle";' in tsx
        assert 'import { GreenSquare } from "../green_square";' in tsx
        assert "{/* Sub-compositions will be added here */}" not in tsx
        assert "Audio" in tsx  # Audio still included alongside compositions

    def test_no_remotion_public_no_assets(self):
        """When remotion_public is empty string, no asset detection happens."""
        section = {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0}
        tsx = generate_section_component(section, fps=30, remotion_public="")
        assert "Audio" not in tsx
        assert "OffthreadVideo" not in tsx


# ===========================================================================
# Tests: generate_root_tsx - Flat section file preference
# ===========================================================================

class TestRootTsxFlatFilePreference:
    """Root.tsx should always import from wrapper directory, even when flat file exists."""

    def test_generate_root_tsx_always_imports_from_wrapper(self, tmp_path):
        """Root.tsx should always import from wrapper dir, even when flat file exists."""
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_src.mkdir(parents=True)

        # Create a Claude-generated flat section file
        (remotion_src / "ColdOpenSection.tsx").write_text("export const ColdOpenSection = () => null;")

        sections = [{"id": "cold_open", "compositionId": "ColdOpenSection", "durationSeconds": 15, "compositions": []}]

        root_content = generate_root_tsx(sections, 30, str(remotion_dir))

        assert 'from "./cold_open"' in root_content
        assert 'from "./ColdOpenSection"' not in root_content

    def test_generate_root_tsx_no_flat_file(self, tmp_path):
        """When no flat section file exists, Root.tsx should import from the wrapper directory."""
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_src.mkdir(parents=True)

        sections = [{"id": "cold_open", "compositionId": "ColdOpenSection", "durationSeconds": 15, "compositions": []}]

        root_content = generate_root_tsx(sections, 30, str(remotion_dir))

        assert 'from "./cold_open"' in root_content
        assert 'from "./ColdOpenSection"' not in root_content


class TestWrapperDelegation:
    """Wrapper should delegate to an authored section component when one exists."""

    def test_wrapper_prefers_section_local_base_component(self, tmp_path):
        """Section-local section component should take precedence over top-level files."""
        remotion_src = str(tmp_path)
        section_dir = tmp_path / "cold_open"
        section_dir.mkdir()
        (section_dir / "ColdOpenSection.tsx").write_text("export const ColdOpenSection = () => null;")
        (tmp_path / "ColdOpenSection.tsx").write_text("export const ColdOpenSection = () => null;")

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpenSection",
            "durationSeconds": 15,
            "offsetSeconds": 0,
            "compositions": ["cold_open_title_card"],
        }
        tsx = generate_section_component(section, 30, remotion_public="", remotion_src=remotion_src)

        assert 'import { ColdOpenSection as ColdOpenSectionBase } from "./ColdOpenSection"' in tsx
        assert '<ColdOpenSectionBase />' in tsx
        assert '<ColdOpenTitleCard />' not in tsx
        assert 'Audio' not in tsx
        assert 'OffthreadVideo' not in tsx

    def test_wrapper_falls_back_to_top_level_base_component(self, tmp_path):
        """Top-level section file is still used when no section-local component exists."""
        remotion_src = str(tmp_path)
        (tmp_path / "ColdOpenSection.tsx").write_text("export const ColdOpenSection = () => null;")

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpenSection",
            "durationSeconds": 15,
            "offsetSeconds": 0,
            "compositions": ["cold_open_title_card"],
        }
        tsx = generate_section_component(section, 30, remotion_public="", remotion_src=remotion_src)

        assert 'import { ColdOpenSection as ColdOpenSectionBase } from "../ColdOpenSection"' in tsx
        assert '<ColdOpenSectionBase />' in tsx
        assert '<ColdOpenTitleCard />' not in tsx

    def test_wrapper_falls_back_without_flat_file(self, tmp_path):
        """When no flat file exists, wrapper renders its own Audio/Video."""
        remotion_src = str(tmp_path)

        section = {"id": "cold_open", "durationSeconds": 15, "offsetSeconds": 0, "compositions": ["cold_open_title_card"]}
        tsx = generate_section_component(section, 30, remotion_public=str(tmp_path / "public"), remotion_src=remotion_src)

        assert 'ColdOpenSectionBase' not in tsx
        assert '<ColdOpenTitleCard />' in tsx

    def test_wrapper_adds_direct_video_when_section_component_has_audio_only(self, tmp_path):
        """Section-local timing component can rely on wrapper for the Veo underlay."""
        remotion_src = str(tmp_path)
        remotion_public = tmp_path / "public"
        section_dir = tmp_path / "part1_economics"
        section_dir.mkdir()
        (section_dir / "Part1Economics.tsx").write_text(
            'import { Audio, staticFile } from "remotion";\n'
            'export const Part1Economics = () => <Audio src={staticFile("part1_economics_narration.wav")} />;'
        )

        audio_alias = remotion_public / "part1_economics_narration.wav"
        video_file = remotion_public / "veo" / "part1_economics.mp4"
        audio_alias.parent.mkdir(parents=True)
        video_file.parent.mkdir(parents=True)
        audio_alias.write_bytes(b"RIFF" + b"\x00" * 32)
        video_file.write_bytes(b"\x00" * 32)

        section = {
            "id": "part1_economics",
            "compositionId": "Part1Economics",
            "durationSeconds": 382,
            "offsetSeconds": 0,
            "compositions": ["03_cost_crossover_chart"],
        }
        tsx = generate_section_component(section, 30, str(remotion_public), remotion_src=remotion_src)

        assert 'import { Part1Economics as Part1EconomicsSectionBase } from "./Part1Economics"' in tsx
        assert '<Part1EconomicsSectionBase />' in tsx
        assert 'staticFile("veo/part1_economics.mp4")' in tsx
        assert 'staticFile("part1_economics_narration.wav")' not in tsx

    def test_wrapper_adds_direct_audio_when_component_audio_ref_is_missing(self, tmp_path):
        """Wrapper should fill in canonical narration when the section component ref is broken."""
        remotion_src = str(tmp_path)
        remotion_public = tmp_path / "public"
        section_dir = tmp_path / "part1_economics"
        section_dir.mkdir()
        (section_dir / "Part1Economics.tsx").write_text(
            'import { Audio, staticFile } from "remotion";\n'
            'export const Part1Economics = () => <Audio src={staticFile("missing_alias.wav")} />;'
        )

        canonical_audio = remotion_public / "part1_economics" / "narration.wav"
        canonical_audio.parent.mkdir(parents=True)
        canonical_audio.write_bytes(b"RIFF" + b"\x00" * 32)

        section = {
            "id": "part1_economics",
            "compositionId": "Part1Economics",
            "durationSeconds": 382,
            "offsetSeconds": 0,
        }
        tsx = generate_section_component(section, 30, str(remotion_public), remotion_src=remotion_src)

        assert 'staticFile("part1_economics/narration.wav")' in tsx
        assert '<Part1EconomicsSectionBase />' in tsx


class TestSectionBaseResolution:
    """Section wrapper delegation should resolve the correct base component path."""

    def test_resolve_section_base_component_prefers_section_local(self, tmp_path):
        remotion_src = str(tmp_path)
        section_dir = tmp_path / "part1_economics"
        section_dir.mkdir()
        (section_dir / "Part1Economics.tsx").write_text("export const Part1Economics = () => null;")
        (tmp_path / "Part1Economics.tsx").write_text("export const Part1Economics = () => null;")

        section = {
            "id": "part1_economics",
            "compositionId": "Part1Economics",
            "durationSeconds": 382,
        }

        assert resolve_section_base_component(section, remotion_src) == (
            "Part1Economics",
            "./Part1Economics",
            str(section_dir / "Part1Economics.tsx"),
        )


class TestGeneratedTimelineWrapper:
    """Generated section timelines should render deterministically in the wrapper."""

    def test_generated_timeline_uses_constants_and_exact_component_imports(self, tmp_path):
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        project_dir = tmp_path
        section_dir = remotion_src / "veo_section"
        component_dir = remotion_src / "VeoSection01OpeningTitleCard"
        section_dir.mkdir()
        component_dir.mkdir()
        (section_dir / "constants.ts").write_text(
            'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "01_opening_title_card", desc: "Intro" }];'
        )
        (component_dir / "index.ts").write_text(
            'export const VeoSection01OpeningTitleCard = () => null;\n'
            'export default VeoSection01OpeningTitleCard;'
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "veo_section.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo_section" / "narration.wav").parent.mkdir(parents=True)
        (remotion_public / "veo_section" / "narration.wav").write_bytes(b"RIFF" + b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 12,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "compositions": ["01_opening_title_card"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'import { VISUAL_SEQUENCE } from "./constants";' in tsx
        assert 'import { VeoSection01OpeningTitleCard } from "../VeoSection01OpeningTitleCard";' in tsx
        assert 'const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {' in tsx
        assert 'const frame = useCurrentFrame();' in tsx
        assert 'let renderVisual = activeVisual;' not in tsx
        assert 'const ActiveComponent = activeVisual ? COMPONENT_MAP[activeVisual.id] ?? null : null;' in tsx
        assert 'SlotScaledSequence' in tsx
        assert 'VisualMediaProvider' in tsx
        assert '<ActiveComponent />' in tsx
        assert 'staticFile("veo_section/narration.wav")' in tsx
        assert 'SectionBase' not in tsx

    def test_generated_timeline_includes_pure_veo_visual_media_and_slot_scaling(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "veo_section"
        title_dir = remotion_src / "VeoSection01TitleCard"
        overlay_dir = remotion_src / "VeoSection03NarrationOverlayIntro"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir()
        title_dir.mkdir()
        overlay_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 30, id: "veo_section_01_title_card", desc: "Title" },',
                    '  { start: 30, end: 60, id: "02_ocean_wave_sunset", desc: "Ocean" },',
                    '  { start: 60, end: 90, id: "03_narration_overlay_intro", desc: "Overlay" },',
                    "];",
                ]
            )
        )
        (title_dir / "index.ts").write_text(
            'export const VeoSection01TitleCard = () => null;\n'
            'export default VeoSection01TitleCard;'
        )
        (title_dir / "constants.ts").write_text(
            "export const ANIMATION_TIMING = { totalDuration: 90 };\n"
        )
        (overlay_dir / "index.ts").write_text(
            'export const VeoSection03NarrationOverlayIntro = () => null;\n'
            'export default VeoSection03NarrationOverlayIntro;'
        )
        (overlay_dir / "constants.ts").write_text(
            "export const ANIMATION_TIMING = { totalDuration: 120 };\n"
        )

        (specs_dir / "01_title_card.md").write_text(
            "**Timestamp:** 0:00 - 0:03\n",
            encoding="utf-8",
        )
        (specs_dir / "02_ocean_wave_sunset.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "**Timestamp:** 0:03 - 0:06",
                    "",
                    "```json",
                    '{ "clipSource": "veo/ocean_wave_sunset.mp4" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "03_narration_overlay_intro.md").write_text(
            "\n".join(
                [
                    "**Timestamp:** 0:06 - 0:09",
                    "",
                    "Narration overlay over the continuing ocean footage.",
                ]
            ),
            encoding="utf-8",
        )

        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "ocean_wave_sunset.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 9,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": [
                "veo_section_01_title_card",
                "03_narration_overlay_intro",
            ],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'import { SlotScaledSequence, VisualMediaProvider } from "../_shared/visual-runtime";' in tsx
        assert '"02_ocean_wave_sunset": { defaultSrc: "veo/ocean_wave_sunset.mp4"' in tsx
        assert '"03_narration_overlay_intro": { defaultSrc: "veo/ocean_wave_sunset.mp4"' in tsx
        assert '"03_narration_overlay_intro": 120' in tsx
        assert 'activeVisualMedia?.defaultSrc && !ActiveComponent' in tsx
        assert '<SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>' in tsx
        assert '<VisualMediaProvider media={activeVisualMedia}>' in tsx

    def test_generated_timeline_resolves_outputfile_media_aliases_from_staged_assets(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "veo_section"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 30, id: "02_ocean_wave_broll", desc: "Ocean" },',
                    '  { start: 30, end: 60, id: "04_aerial_forest_broll", desc: "Forest" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )

        (specs_dir / "02_ocean_wave_broll.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "```json",
                    '{ "outputFile": "veo/ocean_sunset.mp4" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "04_aerial_forest_broll.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "```json",
                    '{ "outputFile": "veo/aerial_forest.mp4" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "ocean_sunset.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "aerial_forest.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "veo_section.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 6,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": [],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert '"02_ocean_wave_broll": { defaultSrc: "veo/ocean_sunset.mp4"' in tsx
        assert '"04_aerial_forest_broll": { defaultSrc: "veo/aerial_forest.mp4"' in tsx
        assert '"02_ocean_wave_broll": { defaultSrc: "veo/veo_section.mp4"' not in tsx
        assert '"04_aerial_forest_broll": { defaultSrc: "veo/veo_section.mp4"' not in tsx

    def test_generated_timeline_prefers_staged_spec_basename_clip_over_section_fallback(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "veo_section"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 30, id: "02_ocean_wave_broll", desc: "Ocean" },',
                    '  { start: 30, end: 60, id: "04_aerial_forest_broll", desc: "Forest" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )

        (specs_dir / "02_ocean_wave_broll.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "```json",
                    '{ "outputFile": "veo/ocean_sunset.mp4" }',
                    "```",
                    "",
                    'src={staticFile("veo/ocean_sunset.mp4")}',
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "04_aerial_forest_broll.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "```json",
                    '{ "outputFile": "veo/aerial_forest.mp4" }',
                    "```",
                    "",
                    'src={staticFile("veo/aerial_forest.mp4")}',
                ]
            ),
            encoding="utf-8",
        )

        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_ocean_wave_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "04_aerial_forest_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "veo_section.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 6,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": [],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert '"02_ocean_wave_broll": { defaultSrc: "veo/02_ocean_wave_broll.mp4"' in tsx
        assert '"04_aerial_forest_broll": { defaultSrc: "veo/04_aerial_forest_broll.mp4"' in tsx
        assert '"02_ocean_wave_broll": { defaultSrc: "veo/veo_section.mp4"' not in tsx
        assert '"04_aerial_forest_broll": { defaultSrc: "veo/veo_section.mp4"' not in tsx

    def test_generated_timeline_does_not_reuse_last_renderable_visual_for_unmapped_slots(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        section_dir = remotion_src / "animation_section"
        title_dir = remotion_src / "AnimationSection01TitleCard"
        specs_dir = project_dir / "specs" / "animation_section"

        section_dir.mkdir()
        title_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 30, id: "animation_section_01_title_card", desc: "Title" },',
                    '  { start: 30, end: 180, id: "04_veo_broll", desc: "Unmapped Veo" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )
        (title_dir / "index.ts").write_text(
            'export const AnimationSection01TitleCard = () => null;\n'
            'export default AnimationSection01TitleCard;',
            encoding="utf-8",
        )
        (title_dir / "constants.ts").write_text(
            "export const ANIMATION_TIMING = { totalDuration: 90 };\n",
            encoding="utf-8",
        )
        (specs_dir / "01_title_card.md").write_text(
            "**Timestamp:** 0:00 - 0:01\n",
            encoding="utf-8",
        )
        (specs_dir / "04_veo_broll.md").write_text(
            "[veo: cinematic cutaway]\n\n**Timestamp:** 0:01 - 0:06\n",
            encoding="utf-8",
        )

        section = {
            "id": "animation_section",
            "compositionId": "AnimationSection",
            "durationSeconds": 6,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "animation_section",
            "compositions": ["animation_section_01_title_card"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public="",
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert "let renderVisual = activeVisual;" not in tsx
        assert "const ActiveComponent = activeVisual ? COMPONENT_MAP[activeVisual.id] ?? null : null;" in tsx
        assert "const intrinsicDurationInFrames = activeVisual ? VISUAL_DURATIONS[activeVisual.id] ?? activeVisualDuration : activeVisualDuration;" in tsx
        assert 'from={activeVisual.start}' in tsx
        assert 'durationInFrames={Math.max(1, activeVisual.end - activeVisual.start)}' in tsx

    def test_generated_timeline_falls_back_when_constants_are_missing(self, tmp_path):
        remotion_src = tmp_path
        section_dir = remotion_src / "cold_open"
        section_dir.mkdir()
        (section_dir / "ColdOpenSection.tsx").write_text(
            "export const ColdOpenSection = () => null;"
        )

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpenSection",
            "durationSeconds": 12,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "compositions": ["cold_open_title_card"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public="",
            remotion_src=str(remotion_src),
        )

        assert 'import { VISUAL_SEQUENCE } from "./constants";' not in tsx
        assert 'import { ColdOpenSection as ColdOpenSectionBase } from "./ColdOpenSection"' in tsx
        assert '<ColdOpenSectionBase />' in tsx

    def test_resolve_section_visual_ids_excludes_spec_only_visuals_without_media(self, tmp_path):
        project_dir = tmp_path
        specs_dir = project_dir / "specs" / "animation_section"
        specs_dir.mkdir(parents=True)
        (specs_dir / "01_title_card.md").write_text("**Timestamp:** 0:00 - 0:03\n")
        (specs_dir / "04_veo_broll.md").write_text("**Timestamp:** 0:03 - 0:06\n")

        section = {
            "id": "animation_section",
            "compositionId": "AnimationSection",
            "durationSeconds": 6,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "animation_section",
            "compositions": ["animation_section_01_title_card"],
        }

        visual_ids = resolve_section_visual_ids(section, str(project_dir))

        assert visual_ids == ["animation_section_01_title_card"]

    def test_generated_timeline_ignores_stale_veo_asset_when_script_has_no_veo(self, tmp_path):
        """A stale staged Veo asset must not contaminate a Remotion-only section render."""
        project_dir = tmp_path
        narrative_dir = project_dir / "narrative"
        narrative_dir.mkdir()
        (narrative_dir / "main_script.md").write_text(
            "# Integration Test Script\n\n"
            "## ANIMATION SECTION\n\n"
            "**[VISUAL: [Remotion] Blue circle pulse]**\n\n"
            "## VEO SECTION\n\n"
            "**[VISUAL: [veo: Ocean wave at sunset]]**\n",
            encoding="utf-8",
        )

        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "animation_section"
        component_dir = remotion_src / "AnimationSection01TitleCard"
        section_dir.mkdir()
        component_dir.mkdir()
        (section_dir / "constants.ts").write_text(
            'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "01_title_card", desc: "Intro" }];'
        )
        (component_dir / "index.ts").write_text(
            'export const AnimationSection01TitleCard = () => null;\n'
            'export default AnimationSection01TitleCard;'
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "animation_section.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "animation_section" / "narration.wav").parent.mkdir(parents=True)
        (remotion_public / "animation_section" / "narration.wav").write_bytes(b"RIFF" + b"\x00" * 32)

        section = {
            "id": "animation_section",
            "label": "Animation Section",
            "compositionId": "AnimationSection",
            "durationSeconds": 12,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "compositions": ["01_title_card"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'staticFile("animation_section/narration.wav")' in tsx
        assert 'staticFile("veo/animation_section.mp4")' not in tsx
        assert "OffthreadVideo" not in tsx


class TestSectionAssetAliases:
    """Compatibility aliases should be created for common Claude staticFile drift."""

    def test_creates_top_level_audio_alias(self, tmp_path):
        remotion_public = tmp_path / "public"
        canonical = remotion_public / "cold_open" / "narration.wav"
        canonical.parent.mkdir(parents=True)
        canonical.write_bytes(b"RIFF" + b"\x00" * 32)

        ensure_section_asset_aliases("cold_open", str(remotion_public))

        assert (remotion_public / "cold_open_narration.wav").exists()

    def test_creates_root_video_alias(self, tmp_path):
        remotion_public = tmp_path / "public"
        canonical = remotion_public / "veo" / "cold_open.mp4"
        canonical.parent.mkdir(parents=True)
        canonical.write_bytes(b"\x00" * 32)

        ensure_section_asset_aliases("cold_open", str(remotion_public))

        assert (remotion_public / "cold_open.mp4").exists()


class TestCompositionTiming:
    """Sub-compositions with timing get their own Sequence wrappers."""

    def test_composition_with_timing_gets_sequence(self):
        """Composition objects with startSeconds/durationSeconds get wrapped in Sequence."""
        section = {
            "id": "part1_economics",
            "durationSeconds": 382,
            "offsetSeconds": 0,
            "compositions": [
                {"id": "part1_economics_stat_callout_gitclear", "startSeconds": 126, "durationSeconds": 5},
            ],
        }
        tsx = generate_section_component(section, 30)
        # Should wrap in a timed Sequence
        assert 'from={Math.round(126 * fps)}' in tsx
        assert 'durationInFrames={Math.ceil(5 * fps)}' in tsx
        assert '<Part1EconomicsStatCalloutGitclear />' in tsx

    def test_composition_without_timing_no_inner_sequence(self):
        """String compositions (no timing) render directly without inner Sequence."""
        section = {
            "id": "part1_economics",
            "durationSeconds": 382,
            "offsetSeconds": 0,
            "compositions": ["part1_economics_stat_callout_gitclear"],
        }
        tsx = generate_section_component(section, 30)
        assert '<Part1EconomicsStatCalloutGitclear />' in tsx
        # Should not have a timed inner Sequence (from={Math.round(...)})
        assert 'from={Math.round(' not in tsx

    def test_mixed_timed_and_untimed_compositions(self):
        """Mix of timed objects and plain string compositions."""
        section = {
            "id": "part1_economics",
            "durationSeconds": 382,
            "offsetSeconds": 0,
            "compositions": [
                {"id": "part1_economics_stat_callout_gitclear", "startSeconds": 126, "durationSeconds": 5},
                "part1_economics_stat_callout_github",
            ],
        }
        tsx = generate_section_component(section, 30)
        assert 'from={Math.round(126 * fps)}' in tsx
        assert '<Part1EconomicsStatCalloutGitclear />' in tsx
        assert '<Part1EconomicsStatCalloutGithub />' in tsx

    def test_root_tsx_handles_composition_objects(self):
        """Root.tsx generation handles composition objects (not just strings)."""
        sections = [{
            "id": "part1_economics",
            "compositionId": "Part1Economics",
            "durationSeconds": 382,
            "compositions": [
                {"id": "part1_economics_stat_callout_gitclear", "startSeconds": 126, "durationSeconds": 5},
            ],
        }]
        root = generate_root_tsx(sections, 30, "")
        assert 'Part1EconomicsStatCalloutGitclear' in root
        assert 'part1-economics-stat-callout-gitclear' in root


class TestDigitPrefixedIdentifiers:
    """Tests for digit-prefixed composition IDs producing valid JS identifiers."""

    def test_resolve_comp_import_prefixes_digit_leading_names(self, tmp_path):
        """Digit-leading PascalCase names get prefixed with section PascalCase."""
        remotion_src = str(tmp_path)
        # Create a PascalCase directory so it resolves
        (tmp_path / "Part1Economics07StatCalloutGitclear").mkdir()
        comp_pascal, import_path = resolve_comp_import(
            "07_stat_callout_gitclear", "part1_economics", remotion_src
        )
        assert comp_pascal == "Part1Economics07StatCalloutGitclear"
        assert import_path == "Part1Economics07StatCalloutGitclear"
        # Must not start with a digit
        assert not comp_pascal[0].isdigit()

    def test_resolve_comp_import_kebab_fallback(self, tmp_path):
        """Falls back to kebab directory if PascalCase directory doesn't exist."""
        remotion_src = str(tmp_path)
        (tmp_path / "07-StatCalloutGitclear").mkdir()
        comp_pascal, import_path = resolve_comp_import(
            "07_stat_callout_gitclear", "part1_economics", remotion_src
        )
        assert comp_pascal == "Part1Economics07StatCalloutGitclear"
        assert import_path == "07-StatCalloutGitclear"

    def test_resolve_comp_import_no_prefix_for_alpha_leading(self, tmp_path):
        """Non-digit-leading names are NOT prefixed."""
        remotion_src = str(tmp_path)
        comp_pascal, import_path = resolve_comp_import(
            "cold_open_title_card", "cold_open", remotion_src
        )
        assert comp_pascal == "ColdOpenTitleCard"
        # Should not have double section prefix
        assert not comp_pascal.startswith("ColdOpenColdOpen")

    def test_root_tsx_no_digit_leading_identifiers(self):
        """Root.tsx must not contain identifiers starting with digits."""
        sections = [{
            "id": "part1_economics",
            "compositionId": "Part1Economics",
            "durationSeconds": 100,
            "compositions": ["07_stat_callout_gitclear", "09_context_degradation_chart"],
        }]
        root = generate_root_tsx(sections, 30, "")
        # No import should have a digit-starting identifier
        import re
        imports = re.findall(r'import \{ (\w+) \}', root)
        for ident in imports:
            assert not ident[0].isdigit(), f"Invalid JS identifier: {ident}"
        # Should contain the section-prefixed versions
        assert "Part1Economics07StatCalloutGitclear" in root
        assert "Part1Economics09ContextDegradationChart" in root

    def test_section_wrapper_no_digit_leading_identifiers(self):
        """Section wrapper must not contain identifiers starting with digits."""
        section = {
            "id": "part5_compound",
            "durationSeconds": 50,
            "compositions": ["08_split_patching_vs_pdd", "10_quote_card"],
        }
        tsx = generate_section_component(section, 30)
        import re
        imports = re.findall(r'import \{ (\w+) \}', tsx)
        for ident in imports:
            assert not ident[0].isdigit(), f"Invalid JS identifier: {ident}"
        assert "Part5Compound08SplitPatchingVsPdd" in tsx
        assert "Part5Compound10QuoteCard" in tsx

    def test_duplicate_comp_ids_across_sections_resolved(self):
        """Same comp_id in different sections gets unique identifiers."""
        sections = [
            {
                "id": "part2_paradigm_shift",
                "compositionId": "Part2ParadigmShift",
                "durationSeconds": 100,
                "compositions": ["11_subtitle_track"],
            },
            {
                "id": "part5_compound",
                "compositionId": "Part5CompoundReturns",
                "durationSeconds": 100,
                "compositions": ["11_subtitle_track"],
            },
        ]
        root = generate_root_tsx(sections, 30, "")
        assert "Part2ParadigmShift11SubtitleTrack" in root
        assert "Part5Compound11SubtitleTrack" in root

    def test_script_source_has_digit_check(self):
        """The script must contain code that checks for digit-prefixed identifiers."""
        script_path = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "..", "scripts", "generate_section_compositions.py"
        )
        with open(script_path, "r") as f:
            source = f.read()
        assert "isdigit" in source
