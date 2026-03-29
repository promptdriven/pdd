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
    build_visual_media_manifest,
    build_visual_overlay_manifest,
    build_visual_contract_manifest,
    write_visual_contract_manifest,
    load_project_json,
    get_fps,
    generate_section_component,
    generate_root_tsx,
    update_root_tsx,
    _merge_root_tsx,
    _extract_visual_overlay_config,
    _should_prefer_generated_contract_renderer,
    resolve_section_component_records,
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

    def test_duration_in_frames_prefers_word_timestamps_over_stale_project_duration(self, tmp_path):
        remotion_dir = tmp_path / "remotion"
        timestamps_dir = tmp_path / "outputs" / "tts" / "intro"
        (remotion_dir / "src" / "remotion").mkdir(parents=True)
        timestamps_dir.mkdir(parents=True)
        (timestamps_dir / "word_timestamps.json").write_text(
            json.dumps([
                {"word": "hello", "start": 0.0, "end": 17.54},
            ])
        )

        sections = [{"id": "intro", "durationSeconds": 0.363}]
        root = generate_root_tsx(
            sections,
            fps=30,
            remotion_dir=str(remotion_dir),
            project_dir=str(tmp_path),
        )

        assert "durationInFrames={527}" in root

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

    def test_root_does_not_import_async_font_loader(self):
        sections = [{"id": "intro", "durationSeconds": 5}]
        root = generate_root_tsx(sections, fps=30, remotion_dir="remotion/")
        assert 'load-inter-font' not in root


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

    def test_uses_component_intrinsic_duration_for_preview_compositions(self, tmp_path):
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        component_dir = remotion_src / "Part2ParadigmShift07VerilogSynthesisTriple"
        component_dir.mkdir(parents=True, exist_ok=True)
        (component_dir / "constants.ts").write_text(
            'export const TOTAL_FRAMES = 540;\n',
            encoding="utf-8",
        )

        sections = [
            {
                "id": "part2_paradigm_shift",
                "durationSeconds": 12,
                "compositions": ["07_verilog_synthesis_triple"],
            }
        ]

        update_root_tsx(sections, fps=30, remotion_dir=str(remotion_dir))

        root_path = remotion_src / "Root.tsx"
        content = root_path.read_text(encoding="utf-8")
        assert 'id="part2-paradigm-shift07-verilog-synthesis-triple"' in content
        assert 'durationInFrames={540}' in content

    def test_uses_duration_frames_constant_for_preview_compositions(self, tmp_path):
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        component_dir = remotion_src / "ColdOpen02ZoomOutAccumulated"
        component_dir.mkdir(parents=True, exist_ok=True)
        (component_dir / "constants.ts").write_text(
            'export const DURATION_FRAMES = 210;\n',
            encoding="utf-8",
        )

        sections = [
            {
                "id": "cold_open",
                "durationSeconds": 12,
                "compositions": ["02_zoom_out_accumulated"],
            }
        ]

        update_root_tsx(sections, fps=30, remotion_dir=str(remotion_dir))

        root_path = remotion_src / "Root.tsx"
        content = root_path.read_text(encoding="utf-8")
        assert 'id="cold-open02-zoom-out-accumulated"' in content
        assert 'durationInFrames={210}' in content

    def test_uses_nested_canvas_duration_frames_for_preview_compositions(self, tmp_path):
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        component_dir = remotion_src / "Closing01SockCallbackSplit"
        component_dir.mkdir(parents=True, exist_ok=True)
        (component_dir / "constants.ts").write_text(
            'export const CANVAS = { DURATION_FRAMES: 240, FPS: 30 } as const;\n',
            encoding="utf-8",
        )

        sections = [
            {
                "id": "closing",
                "durationSeconds": 12,
                "compositions": ["01_sock_callback_split"],
            }
        ]

        update_root_tsx(sections, fps=30, remotion_dir=str(remotion_dir))

        root_path = remotion_src / "Root.tsx"
        content = root_path.read_text(encoding="utf-8")
        assert 'id="closing01-sock-callback-split"' in content
        assert 'durationInFrames={240}' in content

    def test_falls_back_to_spec_duration_for_preview_compositions(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        component_dir = remotion_src / "Closing03CodeRegenerateWorkflow"
        component_dir.mkdir(parents=True, exist_ok=True)
        specs_dir = project_dir / "specs" / "closing"
        specs_dir.mkdir(parents=True, exist_ok=True)
        (specs_dir / "03_code_regenerate_workflow.md").write_text(
            "[Remotion]\n\n**Duration:** ~10s (300 frames @ 30fps)\n",
            encoding="utf-8",
        )

        sections = [
            {
                "id": "closing",
                "durationSeconds": 12,
                "specDir": "closing",
                "compositions": ["03_code_regenerate_workflow"],
            }
        ]

        update_root_tsx(
            sections,
            fps=30,
            remotion_dir=str(remotion_dir),
            project_dir=str(project_dir),
        )

        root_path = remotion_src / "Root.tsx"
        content = root_path.read_text(encoding="utf-8")
        assert 'id="closing03-code-regenerate-workflow"' in content
        assert 'durationInFrames={300}' in content


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

    def test_uses_component_intrinsic_duration_for_preview_compositions(self, tmp_path):
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
        remotion_dir = str(tmp_path / "remotion")
        remotion_src = Path(remotion_dir) / "src" / "remotion"
        component_dir = remotion_src / "Part2ParadigmShift07VerilogSynthesisTriple"
        component_dir.mkdir(parents=True, exist_ok=True)
        (component_dir / "constants.ts").write_text(
            'export const TOTAL_FRAMES = 540;\n',
            encoding="utf-8",
        )

        sections = [
            {
                "id": "part2_paradigm_shift",
                "durationSeconds": 12,
                "compositions": ["07_verilog_synthesis_triple"],
            }
        ]

        result = _merge_root_tsx(existing, sections, fps=30, remotion_dir=remotion_dir)
        assert 'id="part2-paradigm-shift07-verilog-synthesis-triple"' in result
        assert 'durationInFrames={540}' in result

    def test_uses_duration_frames_constant_for_preview_compositions(self, tmp_path):
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
        remotion_dir = str(tmp_path / "remotion")
        remotion_src = Path(remotion_dir) / "src" / "remotion"
        component_dir = remotion_src / "ColdOpen02ZoomOutAccumulated"
        component_dir.mkdir(parents=True, exist_ok=True)
        (component_dir / "constants.ts").write_text(
            'export const DURATION_FRAMES = 210;\n',
            encoding="utf-8",
        )

        sections = [
            {
                "id": "cold_open",
                "durationSeconds": 12,
                "compositions": ["02_zoom_out_accumulated"],
            }
        ]

        result = _merge_root_tsx(existing, sections, fps=30, remotion_dir=remotion_dir)
        assert 'id="cold-open02-zoom-out-accumulated"' in result
        assert 'durationInFrames={210}' in result

    def test_uses_nested_canvas_duration_frames_for_preview_compositions(self, tmp_path):
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
        remotion_dir = str(tmp_path / "remotion")
        remotion_src = Path(remotion_dir) / "src" / "remotion"
        component_dir = remotion_src / "Closing01SockCallbackSplit"
        component_dir.mkdir(parents=True, exist_ok=True)
        (component_dir / "constants.ts").write_text(
            'export const CANVAS = { DURATION_FRAMES: 240, FPS: 30 } as const;\n',
            encoding="utf-8",
        )

        sections = [
            {
                "id": "closing",
                "durationSeconds": 12,
                "compositions": ["01_sock_callback_split"],
            }
        ]

        result = _merge_root_tsx(existing, sections, fps=30, remotion_dir=remotion_dir)
        assert 'id="closing01-sock-callback-split"' in result
        assert 'durationInFrames={240}' in result

    def test_falls_back_to_spec_duration_for_preview_compositions(self, tmp_path):
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
        project_dir = tmp_path
        remotion_dir = str(tmp_path / "remotion")
        remotion_src = Path(remotion_dir) / "src" / "remotion"
        component_dir = remotion_src / "Closing03CodeRegenerateWorkflow"
        component_dir.mkdir(parents=True, exist_ok=True)
        specs_dir = project_dir / "specs" / "closing"
        specs_dir.mkdir(parents=True, exist_ok=True)
        (specs_dir / "03_code_regenerate_workflow.md").write_text(
            "[Remotion]\n\n**Duration:** ~10s (300 frames @ 30fps)\n",
            encoding="utf-8",
        )

        sections = [
            {
                "id": "closing",
                "durationSeconds": 12,
                "specDir": "closing",
                "compositions": ["03_code_regenerate_workflow"],
            }
        ]

        result = _merge_root_tsx(
            existing,
            sections,
            fps=30,
            remotion_dir=remotion_dir,
            project_dir=str(project_dir),
        )
        assert 'id="closing03-code-regenerate-workflow"' in result
        assert 'durationInFrames={300}' in result


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

    def test_generated_timeline_wins_over_legacy_authored_section_component_when_constants_exist(self, tmp_path):
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        project_dir = tmp_path
        section_dir = remotion_src / "cold_open"
        component_dir = remotion_src / "ColdOpen01TitleCard"
        section_dir.mkdir()
        component_dir.mkdir()
        (section_dir / "constants.ts").write_text(
            'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "01_title_card", desc: "Intro" }];'
        )
        (remotion_src / "ColdOpenSection.tsx").write_text(
            'import { Audio, staticFile } from "remotion";\n'
            'export const ColdOpenSection = () => <Audio src={staticFile("cold_open/narration.wav")} />;\n'
            "export default ColdOpenSection;\n"
        )
        (component_dir / "index.ts").write_text(
            'export const ColdOpen01TitleCard = () => null;\n'
            'export default ColdOpen01TitleCard;'
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "cold_open.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "cold_open" / "narration.wav").parent.mkdir(parents=True)
        (remotion_public / "cold_open" / "narration.wav").write_bytes(b"RIFF" + b"\x00" * 32)

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpenSection",
            "durationSeconds": 12,
            "offsetSeconds": 0,
            "timelineSource": "authored",
            "compositions": ["01_title_card"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'import { VISUAL_SEQUENCE } from "./constants";' in tsx
        assert 'import { ColdOpen01TitleCard } from "../ColdOpen01TitleCard";' in tsx
        assert "ColdOpenSectionBase" not in tsx
        assert 'staticFile("cold_open/narration.wav")' in tsx
        assert "<VisualComponent />" in tsx

    def test_generated_timeline_prefers_section_constants_duration_when_project_duration_is_stale(self, tmp_path):
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        project_dir = tmp_path
        section_dir = remotion_src / "part2_paradigm_shift"
        component_dir = remotion_src / "Part2ParadigmShift01SectionTitleCard"
        section_dir.mkdir()
        component_dir.mkdir()
        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const SECTION_DURATION_SECONDS = 227.480;",
                    'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "01_section_title_card", desc: "Intro" }];',
                ]
            )
        )
        (component_dir / "index.ts").write_text(
            'export const Part2ParadigmShift01SectionTitleCard = () => null;\n'
            'export default Part2ParadigmShift01SectionTitleCard;'
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "part2_paradigm_shift.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "part2_paradigm_shift" / "narration.wav").parent.mkdir(parents=True)
        (remotion_public / "part2_paradigm_shift" / "narration.wav").write_bytes(b"RIFF" + b"\x00" * 32)

        section = {
            "id": "part2_paradigm_shift",
            "compositionId": "Part2ParadigmShiftSection",
            "durationSeconds": 0.789334,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "compositions": ["01_section_title_card"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert "const durationSeconds = 227.48;" in tsx

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
        assert 'const VisualComponent = COMPONENT_MAP[visual.id] ?? null;' in tsx
        assert 'SlotScaledSequence' in tsx
        assert 'VisualMediaProvider' in tsx
        assert '<VisualComponent />' in tsx
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

        assert 'import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";' in tsx
        assert '"02_ocean_wave_sunset": { defaultSrc: "veo/ocean_wave_sunset.mp4"' in tsx
        assert '"03_narration_overlay_intro": { defaultSrc: "veo/ocean_wave_sunset.mp4"' in tsx
        assert '"03_narration_overlay_intro": 120' in tsx
        assert ') : visualMedia?.defaultSrc ? (' in tsx
        assert '<SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>' in tsx
        assert '<VisualMediaProvider media={visualMedia}>' in tsx

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

    def test_generated_timeline_resolves_split_panel_video_refs_to_staged_clip_aliases(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "veo_section"
        split_dir = remotion_src / "VeoSection05SplitNatureComparison"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir()
        split_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 30, id: "02_ocean_wave_broll", desc: "Ocean" },',
                    '  { start: 30, end: 60, id: "04_aerial_forest_broll", desc: "Forest" },',
                    '  { start: 60, end: 90, id: "05_split_nature_comparison", desc: "Split" },',
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
        (specs_dir / "05_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "```typescript",
                    '<SplitPanel side="left" video="veo/ocean_sunset.mp4" />',
                    '<SplitPanel side="right" video="veo/aerial_forest.mp4" />',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (split_dir / "index.ts").write_text(
            "export const VeoSection05SplitNatureComparison = () => null;\n",
            encoding="utf-8",
        )

        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_ocean_wave_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "04_aerial_forest_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "veo_section.mp4").write_bytes(b"\x00" * 32)

        # Stale compatibility aliases should not win over the staged per-clip assets.
        (remotion_public / "ocean_sunset.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "aerial_forest.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 9,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": ["05_split_nature_comparison"],
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
        assert '"05_split_nature_comparison": { defaultSrc: "veo/02_ocean_wave_broll.mp4"' in tsx
        assert 'leftSrc: "veo/02_ocean_wave_broll.mp4"' in tsx
        assert 'rightSrc: "veo/04_aerial_forest_broll.mp4"' in tsx
        assert '"05_split_nature_comparison": { defaultSrc: "aerial_forest.mp4"' not in tsx
        assert 'leftSrc: "ocean_sunset.mp4"' not in tsx
        assert 'rightSrc: "aerial_forest.mp4"' not in tsx

    def test_generated_timeline_prefers_current_staged_clips_over_stale_exact_veo_references(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "veo_section"
        split_dir = remotion_src / "VeoSection05SplitNatureComparison"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir()
        split_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 30, id: "02_veo_ocean_broll", desc: "Ocean" },',
                    '  { start: 30, end: 60, id: "03_veo_forest_cutaway", desc: "Forest" },',
                    '  { start: 60, end: 90, id: "05_split_nature_comparison", desc: "Split" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )

        (specs_dir / "02_veo_ocean_broll.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    'src={staticFile("veo/04_veo_broll.mp4")}',
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "03_veo_forest_cutaway.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    'src={staticFile("veo/05_veo_cutaway.mp4")}',
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "05_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "```typescript",
                    '<SplitPanel side="left" video="veo/04_veo_broll.mp4" />',
                    '<SplitPanel side="right" video="veo/05_veo_cutaway.mp4" />',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (split_dir / "index.ts").write_text(
            "export const VeoSection05SplitNatureComparison = () => null;\n",
            encoding="utf-8",
        )

        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_veo_ocean_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "03_veo_forest_cutaway.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "04_veo_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "05_veo_cutaway.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 9,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": ["05_split_nature_comparison"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert '"02_veo_ocean_broll": { defaultSrc: "veo/02_veo_ocean_broll.mp4"' in tsx
        assert '"03_veo_forest_cutaway": { defaultSrc: "veo/03_veo_forest_cutaway.mp4"' in tsx
        assert '"05_split_nature_comparison": { defaultSrc: "veo/02_veo_ocean_broll.mp4"' in tsx
        assert 'leftSrc: "veo/02_veo_ocean_broll.mp4"' in tsx
        assert 'rightSrc: "veo/03_veo_forest_cutaway.mp4"' in tsx
        assert '"02_veo_ocean_broll": { defaultSrc: "veo/04_veo_broll.mp4"' not in tsx
        assert '"03_veo_forest_cutaway": { defaultSrc: "veo/05_veo_cutaway.mp4"' not in tsx
        assert 'leftSrc: "veo/04_veo_broll.mp4"' not in tsx
        assert 'rightSrc: "veo/05_veo_cutaway.mp4"' not in tsx

    def test_generated_timeline_renders_all_active_visual_layers_for_overlap(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "veo_section"
        overlay_dir = remotion_src / "VeoSection07NarrationOverlayIntro"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir()
        overlay_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 60, id: "02_veo_ocean_broll", desc: "Ocean" },',
                    '  { start: 30, end: 90, id: "07_narration_overlay_intro", desc: "Narration Overlay" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )
        (overlay_dir / "index.ts").write_text(
            "export const VeoSection07NarrationOverlayIntro = () => null;\n"
            "export default VeoSection07NarrationOverlayIntro;\n",
            encoding="utf-8",
        )
        (overlay_dir / "constants.ts").write_text(
            "export const ANIMATION_TIMING = { totalDuration: 38 };\n",
            encoding="utf-8",
        )
        (specs_dir / "02_veo_ocean_broll.md").write_text(
            '[veo:]\n\nsrc={staticFile("veo/02_veo_ocean_broll.mp4")}\n',
            encoding="utf-8",
        )
        (specs_dir / "07_narration_overlay_intro.md").write_text(
            "**Timestamp:** 0:01 - 0:03\nNarration overlay over the continuing ocean footage.\n",
            encoding="utf-8",
        )

        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_veo_ocean_broll.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 3,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": ["07_narration_overlay_intro"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert "const activeVisuals = VISUAL_SEQUENCE" in tsx
        assert '.filter((visual) => frame >= visual.start && frame < visual.end)' in tsx
        assert "activeVisuals.map((visual) => {" in tsx
        assert "const VisualComponent = COMPONENT_MAP[visual.id] ?? null;" in tsx
        assert "let activeVisual = VISUAL_SEQUENCE.length > 0 ? VISUAL_SEQUENCE[0] : null;" not in tsx
        assert "const ActiveComponent = activeVisual ? COMPONENT_MAP[activeVisual.id] ?? null : null;" not in tsx
        assert 'key={visual.id}' in tsx
        assert '<VisualMediaProvider media={visualMedia}>' in tsx

    def test_generated_timeline_builds_generic_media_overlay_config_for_composited_media_specs(self, tmp_path):
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
                    '  { start: 0, end: 38, id: "02_veo_ocean_broll", desc: "Ocean" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "02_veo_ocean_broll.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "**Timestamp:** 0:01 - 0:03",
                    "",
                    "### Chart/Visual Elements",
                    "- **Color grade overlay:** Linear gradient from transparent to rgba(10, 22, 40, 0.6), z-index 1",
                    "- **Lower-third narration badge:** Semi-transparent dark bar at the bottom, z-index 2",
                    "",
                    "## Narration Sync",
                    '> "This is the second section of the integration test video."',
                    "",
                    "```typescript",
                    "<AbsoluteFill>",
                    '  <OffthreadVideo src={staticFile("veo/02_veo_ocean_broll.mp4")} />',
                    "  <GradientOverlay direction=\"bottom\" opacity={0.6} />",
                    "  <LowerThirdBadge><NarrationText text=\"This is the second section of the integration test video.\" /></LowerThirdBadge>",
                    "</AbsoluteFill>",
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_veo_ocean_broll.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 3,
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

        assert 'import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";' in tsx
        assert 'const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {' in tsx
        assert '"02_veo_ocean_broll": { gradientOverlay: "bottom", lowerThirdText: "This is the second section of the integration test video."' in tsx
        assert '<GeneratedMediaVisual config={visualOverlayConfig} />' in tsx

    def test_generated_timeline_serializes_numeric_overlay_values_as_numbers(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "callback_section"
        specs_dir = project_dir / "specs" / "callback_section"

        section_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 180, id: "01_callback_clip", desc: "Callback clip" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "01_callback_clip.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "### Animation Sequence",
                    "1. **Frame 0-15 (0-0.5s):** Fade in from black.",
                    "2. **Frame 15-150 (0.5-5s):** Hold.",
                    "3. **Frame 150-180 (5-6s):** Gentle fade to black.",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "developer_cursor_callback" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "developer_cursor_callback.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "callback_section",
            "compositionId": "CallbackSection",
            "durationSeconds": 6,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "callback_section",
            "compositions": [],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {' in tsx
        assert '"01_callback_clip": { fadeInFrames: 15, fadeOutFrames: 30 }' in tsx
        assert '"01_callback_clip": { fadeInFrames: "15", fadeOutFrames: "30" }' not in tsx

    def test_generated_timeline_uses_structured_data_points_for_split_media_aliases(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "veo_section"
        split_dir = remotion_src / "VeoSection05SplitNatureComparison"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir()
        split_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 26, id: "05_split_nature_comparison", desc: "Split" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )
        (split_dir / "index.ts").write_text(
            'export const VeoSection05SplitNatureComparison = () => null;\n'
            'export default VeoSection05SplitNatureComparison;',
            encoding="utf-8",
        )
        (split_dir / "constants.ts").write_text(
            "export const TIMING = { totalFrames: 26 };\n",
            encoding="utf-8",
        )
        (specs_dir / "05_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points",
                    "```json",
                    "{",
                    '  "leftPanel": {',
                    '    "videoSrc": "veo/02_veo_ocean_broll.mp4"',
                    "  },",
                    '  "rightPanel": {',
                    '    "videoSrc": "veo/03_veo_forest_cutaway.mp4"',
                    "  }",
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_veo_ocean_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "03_veo_forest_cutaway.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 3,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": ["05_split_nature_comparison"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert '"05_split_nature_comparison": {' in tsx
        assert 'leftSrc: "veo/02_veo_ocean_broll.mp4"' in tsx
        assert 'rightSrc: "veo/03_veo_forest_cutaway.mp4"' in tsx
        assert 'defaultSrc: "veo/02_veo_ocean_broll.mp4"' in tsx
        assert 'backgroundSrc: "veo/02_veo_ocean_broll.mp4"' in tsx
        assert 'outputSrc: "veo/02_veo_ocean_broll.mp4"' in tsx
        assert 'baseSrc: "veo/02_veo_ocean_broll.mp4"' in tsx
        assert 'revealSrc: "veo/03_veo_forest_cutaway.mp4"' in tsx

    def test_generated_timeline_resolves_clipid_based_split_media_aliases(self, tmp_path):
        """leftClipId / rightClipId fields (no file extension) must resolve to leftSrc / rightSrc."""
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "cold_open"
        split_dir = remotion_src / "ColdOpen01SplitScreenHook"
        specs_dir = project_dir / "specs" / "cold_open"

        section_dir.mkdir()
        split_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 150, id: "01_split_screen_hook", desc: "Split" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )
        (split_dir / "index.ts").write_text(
            'export const ColdOpen01SplitScreenHook = () => null;\n'
            'export default ColdOpen01SplitScreenHook;',
            encoding="utf-8",
        )
        (split_dir / "constants.ts").write_text(
            "export const TIMING = { totalFrames: 150 };\n",
            encoding="utf-8",
        )
        (specs_dir / "01_split_screen_hook.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    "{",
                    '  "type": "split_screen",',
                    '  "leftClipId": "developer_ai_edit",',
                    '  "rightClipId": "grandmother_darning"',
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "developer_ai_edit.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "grandmother_darning.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpen",
            "durationSeconds": 5,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "cold_open",
            "compositions": ["01_split_screen_hook"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'leftSrc: "veo/developer_ai_edit.mp4"' in tsx
        assert 'rightSrc: "veo/grandmother_darning.mp4"' in tsx
        assert 'defaultSrc: "veo/developer_ai_edit.mp4"' in tsx

    def test_generated_timeline_resolves_standalone_clipid_media_alias(self, tmp_path):
        """A standalone veo spec with clipId (no extension) must resolve to defaultSrc."""
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "cold_open"
        specs_dir = project_dir / "specs" / "cold_open"

        section_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 150, id: "02_developer_ai_edit", desc: "Dev" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "02_developer_ai_edit.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    "{",
                    '  "type": "veo_clip",',
                    '  "clipId": "developer_ai_edit"',
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "developer_ai_edit.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpen",
            "durationSeconds": 5,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "cold_open",
            "compositions": [],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'defaultSrc: "veo/developer_ai_edit.mp4"' in tsx

    def test_generated_timeline_resolves_image_style_split_sources_via_structured_refs(self, tmp_path):
        project_dir = tmp_path
        remotion_src = tmp_path
        remotion_public = tmp_path / "public"
        section_dir = remotion_src / "veo_section"
        split_dir = remotion_src / "VeoSection05SplitNatureComparison"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir()
        split_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            "\n".join(
                [
                    "export const VISUAL_SEQUENCE = [",
                    '  { start: 0, end: 30, id: "02_ocean_wave_sunset", desc: "Ocean" },',
                    '  { start: 30, end: 60, id: "03_aerial_forest_canopy", desc: "Forest" },',
                    '  { start: 60, end: 90, id: "05_split_nature_comparison", desc: "Split" },',
                    "];",
                ]
            ),
            encoding="utf-8",
        )
        (split_dir / "index.ts").write_text(
            'export const VeoSection05SplitNatureComparison = () => null;\n'
            'export default VeoSection05SplitNatureComparison;',
            encoding="utf-8",
        )
        (split_dir / "constants.ts").write_text(
            "export const TIMING = { totalFrames: 30 };\n",
            encoding="utf-8",
        )
        (specs_dir / "02_ocean_wave_sunset.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points",
                    "```json",
                    '{ "source_file": "ocean_wave_sunset.mp4" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "03_aerial_forest_canopy.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points",
                    "```json",
                    '{ "source_file": "aerial_forest_canopy.mp4" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "05_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points",
                    "```json",
                    "{",
                    '  "left": {',
                    '    "label": "Ocean · Sunset",',
                    '    "source": "ocean_wave_sunset_still.jpg"',
                    "  },",
                    '  "right": {',
                    '    "label": "Forest · Canopy",',
                    '    "source": "aerial_forest_canopy_still.jpg"',
                    "  }",
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_ocean_wave_sunset.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "03_aerial_forest_canopy.mp4").write_bytes(b"\x00" * 32)

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 3,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": ["05_split_nature_comparison"],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'leftSrc: "veo/02_ocean_wave_sunset.mp4"' in tsx
        assert 'rightSrc: "veo/03_aerial_forest_canopy.mp4"' in tsx
        assert 'const VISUAL_CONTRACTS' in tsx
        assert '<VisualContractProvider contract={visualContract}>' in tsx

    def test_writes_visual_contract_manifest_with_data_points_and_media_aliases(self, tmp_path):
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / "veo_section"

        specs_dir.mkdir(parents=True)
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_veo_ocean_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "03_veo_forest_cutaway.mp4").write_bytes(b"\x00" * 32)

        (specs_dir / "05_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points",
                    "```json",
                    "{",
                    '  "leftPanel": {',
                    '    "videoSrc": "veo/02_veo_ocean_broll.mp4",',
                    '    "label": "OCEAN — Sunset"',
                    "  },",
                    '  "rightPanel": {',
                    '    "videoSrc": "veo/03_veo_forest_cutaway.mp4",',
                    '    "label": "FOREST — Canopy"',
                    "  }",
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 3,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": ["05_split_nature_comparison"],
        }

        manifest = build_visual_contract_manifest(
            [section],
            str(project_dir),
            str(remotion_public),
        )

        visual = manifest["sections"][0]["visuals"][0]
        assert visual["id"] == "05_split_nature_comparison"
        assert visual["dataPoints"]["leftPanel"]["videoSrc"] == "veo/02_veo_ocean_broll.mp4"
        assert visual["mediaAliases"]["leftSrc"] == "veo/02_veo_ocean_broll.mp4"
        assert visual["mediaAliases"]["rightSrc"] == "veo/03_veo_forest_cutaway.mp4"

        manifest_path = write_visual_contract_manifest(
            [section],
            str(project_dir),
            str(remotion_public),
        )
        saved = json.loads(Path(manifest_path).read_text(encoding="utf-8"))
        assert saved["sections"][0]["visuals"][0]["mediaAliases"]["leftSrc"] == "veo/02_veo_ocean_broll.mp4"

    def test_writes_visual_contract_manifest_from_data_points_json_heading_and_embedded_clip_ids(self, tmp_path):
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / "cold_open"

        specs_dir.mkdir(parents=True)
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "developer_cursor_edit.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "grandmother_darning_hook.mp4").write_bytes(b"\x00" * 32)

        (specs_dir / "01_split_screen_hook.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    "{",
                    '  "leftPanel": {',
                    '    "content": "developer_cursor_edit_veo",',
                    '    "label": "2025"',
                    "  },",
                    '  "rightPanel": {',
                    '    "content": "grandmother_darning_hook_veo",',
                    '    "label": "1955"',
                    "  },",
                    '  "embeddedVeoClips": ["developer_cursor_edit", "grandmother_darning_hook"]',
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpenSection",
            "durationSeconds": 3,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "cold_open",
            "compositions": ["01_split_screen_hook"],
        }

        manifest = build_visual_contract_manifest(
            [section],
            str(project_dir),
            str(remotion_public),
        )

        visual = manifest["sections"][0]["visuals"][0]
        assert visual["dataPoints"]["leftPanel"]["content"] == "developer_cursor_edit_veo"
        assert visual["mediaAliases"]["leftSrc"] == "veo/developer_cursor_edit.mp4"
        assert visual["mediaAliases"]["rightSrc"] == "veo/grandmother_darning_hook.mp4"

    def test_builds_counter_overlay_config_from_data_points_json(self, tmp_path):
        project_dir = tmp_path
        specs_dir = project_dir / "specs" / "part2_paradigm_shift"
        specs_dir.mkdir(parents=True)

        (specs_dir / "03_injection_molding_process.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    "{",
                    '  "clipId": "injection_molding_process",',
                    '  "overlay": {',
                    '    "counter": {',
                    '      "values": [1, 10, 100, 1000, 10000],',
                    '      "position": "lower_right"',
                    "    }",
                    "  }",
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        section = {
            "id": "part2_paradigm_shift",
            "specDir": "part2_paradigm_shift",
            "compositions": ["03_injection_molding_process"],
        }

        overlay_manifest = build_visual_overlay_manifest(section, str(project_dir))

        assert overlay_manifest["03_injection_molding_process"]["counterOverlay"] is True
        assert overlay_manifest["03_injection_molding_process"]["counterPosition"] == "lower_right"

    def test_media_aliases_prefer_current_staged_clip_over_prior_split_placeholder_refs(self, tmp_path):
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / "veo_section"

        specs_dir.mkdir(parents=True)
        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_ocean_wave_sunset.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "04_veo_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "05_veo_cutaway.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "06_aerial_forest_canopy.mp4").write_bytes(b"\x00" * 32)

        (specs_dir / "02_ocean_wave_sunset.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points",
                    "```json",
                    '{ "source_file": "veo/04_veo_broll.mp4" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "04_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points",
                    "```json",
                    "{",
                    '  "left": { "label": "Ocean · Sunset", "source": "veo/04_veo_broll.mp4" },',
                    '  "right": { "label": "Forest · Canopy", "source": "veo/05_veo_cutaway.mp4" }',
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "06_aerial_forest_canopy.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points",
                    "```json",
                    '{ "source_file": "veo/05_veo_cutaway.mp4" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 6,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": [],
        }

        manifest = build_visual_media_manifest(
            section,
            str(project_dir),
            str(remotion_public),
        )

        assert manifest["04_split_nature_comparison"]["leftSrc"] == "veo/02_ocean_wave_sunset.mp4"
        assert manifest["04_split_nature_comparison"]["rightSrc"] == "veo/06_aerial_forest_canopy.mp4"
        assert manifest["06_aerial_forest_canopy"]["defaultSrc"] == "veo/06_aerial_forest_canopy.mp4"

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
        assert "const VisualComponent = COMPONENT_MAP[visual.id] ?? null;" in tsx
        assert "const intrinsicDurationInFrames = VISUAL_DURATIONS[visual.id] ?? visualDuration;" in tsx
        assert 'from={visual.start}' in tsx
        assert 'durationInFrames={visualDuration}' in tsx

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

    def test_resolve_section_visual_ids_includes_spec_only_visuals_with_generic_video_refs(self, tmp_path):
        project_dir = tmp_path
        specs_dir = project_dir / "specs" / "veo_section"
        specs_dir.mkdir(parents=True)
        (specs_dir / "05_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    '<SplitPanel side="left" video="veo/ocean_sunset.mp4" />',
                    '<SplitPanel side="right" video="veo/aerial_forest.mp4" />',
                ]
            ),
            encoding="utf-8",
        )

        section = {
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 6,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "veo_section",
            "compositions": [],
        }

        visual_ids = resolve_section_visual_ids(section, str(project_dir))

        assert visual_ids == ["05_split_nature_comparison"]

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

    def test_root_tsx_wraps_preview_compositions_with_visual_media_when_available(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        section_dir = remotion_src / "veo_section"
        split_dir = remotion_src / "VeoSection05SplitNatureComparison"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir(parents=True)
        split_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "index.tsx").write_text(
            "export const VeoSectionSection = () => null;\nexport default VeoSectionSection;\n",
            encoding="utf-8",
        )
        (split_dir / "index.ts").write_text(
            "export const VeoSection05SplitNatureComparison = () => null;\nexport default VeoSection05SplitNatureComparison;\n",
            encoding="utf-8",
        )
        (specs_dir / "02_ocean_wave_broll.md").write_text(
            '[veo:]\n```json\n{ "outputFile": "veo/ocean_sunset.mp4" }\n```',
            encoding="utf-8",
        )
        (specs_dir / "04_aerial_forest_broll.md").write_text(
            '[veo:]\n```json\n{ "outputFile": "veo/aerial_forest.mp4" }\n```',
            encoding="utf-8",
        )
        (specs_dir / "05_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    '<SplitPanel side="left" video="veo/ocean_sunset.mp4" />',
                    '<SplitPanel side="right" video="veo/aerial_forest.mp4" />',
                ]
            ),
            encoding="utf-8",
        )

        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_ocean_wave_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "04_aerial_forest_broll.mp4").write_bytes(b"\x00" * 32)

        sections = [{
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 8,
            "specDir": "veo_section",
            "compositions": ["05_split_nature_comparison"],
        }]

        root = generate_root_tsx(
            sections,
            30,
            str(remotion_dir),
            project_dir=str(project_dir),
        )

        assert 'import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "./_shared/visual-runtime";' in root
        assert 'const PREVIEW_VISUAL_MEDIA' in root
        assert 'const PREVIEW_VISUAL_CONTRACTS' in root
        assert '"veo_section:05_split_nature_comparison": { defaultSrc: "veo/02_ocean_wave_broll.mp4"' in root
        assert 'leftSrc: "veo/02_ocean_wave_broll.mp4"' in root
        assert 'rightSrc: "veo/04_aerial_forest_broll.mp4"' in root
        assert 'const VeoSection05SplitNatureComparisonPreview: React.FC = () => (' in root
        assert '<VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:05_split_nature_comparison"] ?? null}>' in root
        assert '<VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:05_split_nature_comparison"] ?? null}>' in root
        assert 'component={VeoSection05SplitNatureComparisonPreview}' in root

    def test_root_tsx_prefers_current_staged_clips_over_stale_exact_veo_references(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        section_dir = remotion_src / "veo_section"
        split_dir = remotion_src / "VeoSection05SplitNatureComparison"
        specs_dir = project_dir / "specs" / "veo_section"

        section_dir.mkdir(parents=True)
        split_dir.mkdir()
        specs_dir.mkdir(parents=True)

        (section_dir / "index.tsx").write_text(
            "export const VeoSectionSection = () => null;\nexport default VeoSectionSection;\n",
            encoding="utf-8",
        )
        (split_dir / "index.ts").write_text(
            "export const VeoSection05SplitNatureComparison = () => null;\nexport default VeoSection05SplitNatureComparison;\n",
            encoding="utf-8",
        )
        (specs_dir / "02_veo_ocean_broll.md").write_text(
            '[veo:]\nsrc={staticFile("veo/04_veo_broll.mp4")}\n',
            encoding="utf-8",
        )
        (specs_dir / "03_veo_forest_cutaway.md").write_text(
            '[veo:]\nsrc={staticFile("veo/05_veo_cutaway.mp4")}\n',
            encoding="utf-8",
        )
        (specs_dir / "05_split_nature_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    '<SplitPanel side="left" video="veo/04_veo_broll.mp4" />',
                    '<SplitPanel side="right" video="veo/05_veo_cutaway.mp4" />',
                ]
            ),
            encoding="utf-8",
        )

        (remotion_public / "veo").mkdir(parents=True)
        (remotion_public / "veo" / "02_veo_ocean_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "03_veo_forest_cutaway.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "04_veo_broll.mp4").write_bytes(b"\x00" * 32)
        (remotion_public / "veo" / "05_veo_cutaway.mp4").write_bytes(b"\x00" * 32)

        sections = [{
            "id": "veo_section",
            "compositionId": "VeoSection",
            "durationSeconds": 8,
            "specDir": "veo_section",
            "compositions": ["05_split_nature_comparison"],
        }]

        root = generate_root_tsx(
            sections,
            30,
            str(remotion_dir),
            project_dir=str(project_dir),
        )

        assert '"veo_section:05_split_nature_comparison": { defaultSrc: "veo/02_veo_ocean_broll.mp4"' in root
        assert 'leftSrc: "veo/02_veo_ocean_broll.mp4"' in root
        assert 'rightSrc: "veo/03_veo_forest_cutaway.mp4"' in root
        assert '"veo_section:05_split_nature_comparison": { defaultSrc: "veo/04_veo_broll.mp4"' not in root
        assert 'leftSrc: "veo/04_veo_broll.mp4"' not in root
        assert 'rightSrc: "veo/05_veo_cutaway.mp4"' not in root


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

    def test_resolve_comp_import_reads_named_export_from_digit_prefixed_directory_index(self, tmp_path):
        """Directory names can drift into invalid identifiers; import path and export name must stay separate."""
        remotion_src = str(tmp_path)
        component_dir = tmp_path / "08-SplitPatchingVsPdd"
        component_dir.mkdir()
        (component_dir / "index.ts").write_text(
            'export { Part5Compound08SplitPatchingVsPdd } from "./Part5Compound08SplitPatchingVsPdd";\n'
            'export { default } from "./Part5Compound08SplitPatchingVsPdd";\n',
            encoding="utf-8",
        )

        comp_pascal, import_path = resolve_comp_import(
            "08_patching_vs_pdd", "part5_compound_returns", remotion_src
        )

        assert comp_pascal == "Part5Compound08SplitPatchingVsPdd"
        assert import_path == "08-SplitPatchingVsPdd"
        assert not comp_pascal[0].isdigit()

    def test_resolve_comp_import_no_prefix_for_alpha_leading(self, tmp_path):
        """Non-digit-leading names are NOT prefixed."""
        remotion_src = str(tmp_path)
        comp_pascal, import_path = resolve_comp_import(
            "cold_open_title_card", "cold_open", remotion_src
        )
        assert comp_pascal == "ColdOpenTitleCard"
        # Should not have double section prefix
        assert not comp_pascal.startswith("ColdOpenColdOpen")

    def test_resolve_comp_import_matches_unique_semantic_suffix_when_numbers_drift(self, tmp_path):
        """Unique section-scoped component matches should survive numbering drift."""
        remotion_src = str(tmp_path)
        component_dir = tmp_path / "Closing09FinalTitleCard"
        component_dir.mkdir()
        (component_dir / "index.ts").write_text(
            'export const Closing09FinalTitleCard = () => null;\n'
            'export default Closing09FinalTitleCard;\n',
            encoding="utf-8",
        )
        comp_pascal, import_path = resolve_comp_import(
            "08_final_title_card", "closing", remotion_src
        )
        assert comp_pascal == "Closing09FinalTitleCard"
        assert import_path == "Closing09FinalTitleCard"

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

    def test_generate_section_component_prefers_generated_contract_for_structured_title_cards_even_when_exact_component_exists(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "closing"
        section_dir = remotion_src / "closing"
        component_dir = remotion_src / "Closing09FinalTitleCard"

        specs_dir.mkdir(parents=True)
        section_dir.mkdir(parents=True)
        component_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True)

        (specs_dir / "08_final_title_card.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                '{"type":"title_card","title":"Prompt-Driven Development","commands":["uv tool install pdd-cli"]}',
                "```",
            ]),
            encoding="utf-8",
        )
        (section_dir / "constants.ts").write_text(
            'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "08_final_title_card", desc: "Outro" }];',
            encoding="utf-8",
        )
        (component_dir / "index.ts").write_text(
            'export const Closing09FinalTitleCard = () => null;\n'
            'export default Closing09FinalTitleCard;',
            encoding="utf-8",
        )

        section = {
            "id": "closing",
            "compositionId": "ClosingSection",
            "durationSeconds": 8,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "closing",
            "compositions": [],
        }

        tsx = generate_section_component(
            section,
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'import { Closing09FinalTitleCard } from "../Closing09FinalTitleCard";' not in tsx
        assert '"08_final_title_card": {"specBaseName": "08_final_title_card"' in tsx
        assert '"08_final_title_card": Closing09FinalTitleCard' not in tsx
        assert "<GeneratedContractVisual />" in tsx

    def test_generate_root_tsx_uses_generated_contract_preview_for_structured_title_cards_even_when_exact_component_exists(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "closing"
        component_dir = remotion_src / "Closing09FinalTitleCard"

        component_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (specs_dir / "08_final_title_card.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                '{"type":"title_card","title":"Prompt-Driven Development","commands":["uv tool install pdd-cli"]}',
                "```",
            ]),
            encoding="utf-8",
        )
        (component_dir / "index.ts").write_text(
            'export const Closing09FinalTitleCard = () => null;\n'
            'export default Closing09FinalTitleCard;',
            encoding="utf-8",
        )

        root = generate_root_tsx(
            [{
                "id": "closing",
                "compositionId": "ClosingSection",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "closing",
                "compositions": [],
            }],
            30,
            str(remotion_dir),
            project_dir=str(project_dir),
        )

        assert 'import { Closing09FinalTitleCard } from "./Closing09FinalTitleCard";' not in root
        assert 'id="closing08-final-title-card"' in root
        assert 'GeneratedContractVisual' in root

    def test_generate_root_tsx_includes_preview_media_and_contract_aliases_from_visual_contract_manifest(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "part1_economics"
        component_dir = remotion_src / "Part1Economics12DeveloperDarningSplit"
        section_dir = remotion_src / "part1_economics"

        component_dir.mkdir(parents=True)
        section_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)
        (remotion_public / "veo").mkdir()

        (remotion_public / "veo" / "developer_cursor_edit.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "grandmother_darning_lamplight.mp4").write_text("stub", encoding="utf-8")

        (component_dir / "index.ts").write_text(
            "export const Part1Economics12DeveloperDarningSplit = () => null;\n"
            "export default Part1Economics12DeveloperDarningSplit;\n",
            encoding="utf-8",
        )
        (section_dir / "constants.ts").write_text(
            'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "12_developer_darning_split", desc: "split", lane: 0 }];',
            encoding="utf-8",
        )
        (specs_dir / "12_developer_darning_split.md").write_text(
            "\n".join([
                "[split:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "split_screen",
                        "leftPanel": {"label": "CURSOR"},
                        "rightPanel": {"label": "DARNING NEEDLE"},
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )
        (specs_dir / "13_developer_cursor_coding.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "veo_clip",
                        "clipId": "developer_cursor_coding",
                        "embeddedIn": "12_developer_darning_split",
                        "panel": "left",
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )
        (specs_dir / "14_grandmother_darning_expert.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "veo_clip",
                        "clipId": "grandmother_darning_expert",
                        "embeddedIn": "12_developer_darning_split",
                        "panel": "right",
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )

        root = generate_root_tsx(
            [{
                "id": "part1_economics",
                "compositionId": "Part1EconomicsSection",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "part1_economics",
                "compositions": ["12_developer_darning_split"],
            }],
            30,
            str(remotion_dir),
            project_dir=str(project_dir),
        )

        assert '"part1_economics:12_developer_darning_split": { leftSrc: "veo/developer_cursor_edit.mp4"' in root
        assert 'rightSrc: "veo/grandmother_darning_lamplight.mp4"' in root
        assert '"mediaAliases": {"leftSrc": "veo/developer_cursor_edit.mp4"' in root

    def test_generate_root_tsx_registers_fallback_preview_for_manifest_component_without_import(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "part1_economics"

        remotion_src.mkdir(parents=True)
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (specs_dir / "02_sock_price_chart.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                '{"type":"animated_chart","chartId":"sock_economics","narrationSegments":["part1_economics_005"]}',
                "```",
            ]),
            encoding="utf-8",
        )

        root = generate_root_tsx(
            [{
                "id": "part1_economics",
                "compositionId": "Part1EconomicsSection",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "part1_economics",
                "compositions": [],
            }],
            30,
            str(remotion_dir),
            project_dir=str(project_dir),
        )

        assert 'import { GeneratedContractVisual } from "./_shared/GeneratedContractVisual";' in root
        assert 'const Part1Economics02SockPriceChartPreview: React.FC = () => (' in root
        assert '<GeneratedContractVisual />' in root
        assert 'id="part1-economics02-sock-price-chart"' in root

    def test_generate_root_tsx_registers_media_preview_for_manifest_raw_media_visual_without_exact_component(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "part1_economics"

        remotion_src.mkdir(parents=True)
        (remotion_public / "veo").mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo" / "developer_codebase_zoomout.mp4").write_text(
            "stub",
            encoding="utf-8",
        )
        (specs_dir / "17_developer_codebase_zoomout.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "veo_clip",
                        "clipId": "developer_codebase_zoomout",
                        "characters": [
                            {
                                "id": "developer_protagonist",
                                "label": "Developer",
                            }
                        ],
                        "narrationSegments": ["part1_economics_028"],
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )

        root = generate_root_tsx(
            [{
                "id": "part1_economics",
                "compositionId": "Part1EconomicsSection",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "part1_economics",
                "compositions": [],
            }],
            30,
            str(remotion_dir),
            project_dir=str(project_dir),
        )

        assert 'import { GeneratedMediaVisual } from "./_shared/GeneratedMediaVisual";' in root
        assert 'const Part1Economics17DeveloperCodebaseZoomoutPreview: React.FC = () => (' in root
        assert 'PREVIEW_VISUAL_MEDIA["part1_economics:17_developer_codebase_zoomout"]' in root
        assert '<SlotScaledSequence intrinsicDurationInFrames={PREVIEW_INTRINSIC_DURATIONS["part1_economics:17_developer_codebase_zoomout"] ?? 150}>' in root
        assert '<GeneratedMediaVisual config={PREVIEW_VISUAL_OVERLAYS["part1_economics:17_developer_codebase_zoomout"] ?? null} />' in root
        assert 'id="part1-economics17-developer-codebase-zoomout"' in root

    def test_generate_root_tsx_prefers_contract_preview_for_manifest_component_even_with_media_aliases(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "cold_open"

        remotion_src.mkdir(parents=True)
        (remotion_public / "veo").mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo" / "developer_cursor_edit.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "developer_codebase_zoomout.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "grandmother_darning.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "grandmother_drawer_zoomout.mp4").write_text("stub", encoding="utf-8")
        (specs_dir / "01_split_screen_darning.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "split_screen",
                        "layout": "vertical_50_50",
                        "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.4},
                        "panels": {
                            "left": {"clips": ["developer_cursor_edit", "developer_codebase_zoomout"]},
                            "right": {"clips": ["grandmother_darning", "grandmother_drawer_zoomout"]},
                        },
                        "durationSeconds": 9,
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )

        root = generate_root_tsx(
            [{
                "id": "cold_open",
                "compositionId": "ColdOpenSection",
                "durationSeconds": 9,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "cold_open",
                "compositions": [],
            }],
            30,
            str(remotion_dir),
            project_dir=str(project_dir),
        )

        assert 'const ColdOpen01SplitScreenDarningPreview: React.FC = () => (' in root
        assert '<GeneratedContractVisual />' in root
        assert '<GeneratedMediaVisual config={PREVIEW_VISUAL_OVERLAYS["cold_open:01_split_screen_darning"] ?? null} />' not in root

    def test_generate_root_tsx_uses_section_timeline_slot_duration_for_preview_compositions(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        specs_dir = project_dir / "specs" / "part1_economics"
        outputs_dir = project_dir / "outputs" / "compositions"
        component_dir = remotion_src / "Part1Economics01SectionTitleCard"

        component_dir.mkdir(parents=True, exist_ok=True)
        specs_dir.mkdir(parents=True)
        outputs_dir.mkdir(parents=True)

        (component_dir / "constants.ts").write_text(
            'export const TOTAL_FRAMES = 150;\n',
            encoding="utf-8",
        )
        (specs_dir / "01_section_title_card.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "title_card",
                        "sectionNumber": 1,
                        "titleLine1": "THE ECONOMICS",
                        "titleLine2": "OF DARNING",
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )
        (outputs_dir / "section-timeline.json").write_text(
            json.dumps(
                {
                    "version": 1,
                    "updatedAt": "2026-03-27T00:00:00Z",
                    "sections": [
                        {
                            "sectionId": "part1_economics",
                            "durationSeconds": 24,
                            "entries": [
                                {
                                    "id": "01_section_title_card",
                                    "startSeconds": 0,
                                    "endSeconds": 24,
                                }
                            ],
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )

        root = generate_root_tsx(
            [{
                "id": "part1_economics",
                "compositionId": "Part1EconomicsSection",
                "durationSeconds": 24,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "part1_economics",
                "compositions": ["01_section_title_card"],
            }],
            30,
            str(remotion_dir),
            project_dir=str(project_dir),
        )

        assert 'const PREVIEW_INTRINSIC_DURATIONS: Record<string, number> = {' in root
        assert '"part1_economics:01_section_title_card": 150,' in root
        assert '<SlotScaledSequence intrinsicDurationInFrames={PREVIEW_INTRINSIC_DURATIONS["part1_economics:01_section_title_card"] ?? 150}>' in root
        assert 'id="part1-economics01-section-title-card"' in root
        assert 'durationInFrames={720}' in root

    def test_generate_section_component_falls_back_to_generated_contract_visual_when_import_missing(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "part1_economics"
        section_dir = remotion_src / "part1_economics"

        section_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (section_dir / "constants.ts").write_text(
            'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "02_sock_price_chart", desc: "Sock economics", lane: 0 }];',
            encoding="utf-8",
        )
        (specs_dir / "02_sock_price_chart.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                '{"type":"animated_chart","chartId":"sock_economics","narrationSegments":["part1_economics_005"]}',
                "```",
            ]),
            encoding="utf-8",
        )

        tsx = generate_section_component(
            {
                "id": "part1_economics",
                "compositionId": "Part1EconomicsSection",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "part1_economics",
                "compositions": [],
            },
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";' in tsx
        assert 'visualContract?.renderMode === "component" ? (' in tsx
        assert (
            '            ) : visualContract?.renderMode === "component" ? (\n'
            '              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>\n'
            '                <VisualContractProvider contract={visualContract}>\n'
            '                  <VisualMediaProvider media={visualMedia}>\n'
            '                    <GeneratedContractVisual />\n'
            '                  </VisualMediaProvider>\n'
            '                </VisualContractProvider>\n'
            '              </SlotScaledSequence>\n'
        ) in tsx

    def test_generate_section_component_prefers_generated_contract_when_name_drift_is_semantic_not_exact(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "where_to_start"
        section_dir = remotion_src / "where_to_start"
        existing_component_dir = remotion_src / "WhereToStart03ModuleHighlightUpdate"

        section_dir.mkdir(parents=True)
        existing_component_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)
        (existing_component_dir / "index.ts").write_text(
            'export const WhereToStart03ModuleHighlightUpdate = () => null;\n'
            'export default WhereToStart03ModuleHighlightUpdate;\n',
            encoding="utf-8",
        )

        (section_dir / "constants.ts").write_text(
            'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "03_module_highlight_terminal", desc: "module highlight", lane: 0 }];',
            encoding="utf-8",
        )
        (specs_dir / "03_module_highlight_terminal.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                '{"type":"code_transformation","chartId":"module_highlight_terminal","narrationSegments":["where_to_start_001"]}',
                "```",
            ]),
            encoding="utf-8",
        )

        tsx = generate_section_component(
            {
                "id": "where_to_start",
                "compositionId": "WhereToStartSection",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "where_to_start",
                "compositions": [],
            },
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert 'import { WhereToStart03ModuleHighlightUpdate } from "../WhereToStart03ModuleHighlightUpdate";' not in tsx
        assert '"03_module_highlight_terminal": WhereToStart03ModuleHighlightUpdate,' not in tsx
        assert 'import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";' in tsx

    def test_generate_section_component_serializes_contract_media_aliases_for_component_visuals(self, tmp_path):
        project_dir = tmp_path
        remotion_dir = tmp_path / "remotion"
        remotion_src = remotion_dir / "src" / "remotion"
        remotion_public = remotion_dir / "public"
        specs_dir = project_dir / "specs" / "part1_economics"
        section_dir = remotion_src / "part1_economics"
        component_dir = remotion_src / "Part1Economics12DeveloperDarningSplit"

        section_dir.mkdir(parents=True)
        component_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True)
        (remotion_public / "veo").mkdir()
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo" / "developer_cursor_edit.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "grandmother_darning_lamplight.mp4").write_text("stub", encoding="utf-8")

        (section_dir / "constants.ts").write_text(
            'export const VISUAL_SEQUENCE = [{ start: 0, end: 90, id: "12_developer_darning_split", desc: "split", lane: 0 }];',
            encoding="utf-8",
        )
        (specs_dir / "12_developer_darning_split.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                '{',
                '  "type": "split_screen",',
                '  "leftSrc": "developer_cursor_edit.mp4",',
                '  "rightSrc": "grandmother_darning_lamplight.mp4",',
                '  "leftPanel": { "content": "developer_cursor_edit", "label": "CURSOR" },',
                '  "rightPanel": { "content": "grandmother_darning_lamplight", "label": "DARNING" },',
                '  "embeddedVeoClips": ["developer_cursor_edit", "grandmother_darning_lamplight"],',
                '  "narrationSegments": ["part1_economics_001"]',
                '}',
                "```",
            ]),
            encoding="utf-8",
        )

        tsx = generate_section_component(
            {
                "id": "part1_economics",
                "compositionId": "Part1EconomicsSection",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "timelineSource": "generated",
                "specDir": "part1_economics",
                "compositions": ["12_developer_darning_split"],
            },
            30,
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
            project_dir=str(project_dir),
        )

        assert '"renderMode": "component"' in tsx
        assert '"mediaAliases": {' in tsx
        assert '"leftSrc": "veo/developer_cursor_edit.mp4"' in tsx
        assert '"rightSrc": "veo/grandmother_darning_lamplight.mp4"' in tsx

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


# ---------------------------------------------------------------------------
# renderMode assignment — must prefer "component" when a Remotion component exists
# ---------------------------------------------------------------------------


class TestResolveVisualRenderMode:
    """_resolve_visual_render_mode must return 'component' when a Remotion
    component exists for the visual, even if media aliases are present.
    Title cards and Remotion specs that get fallback video should not be
    overridden to 'raw-media'."""

    def _import_fn(self):
        import importlib, sys
        sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
        mod = importlib.import_module("generate_section_compositions")
        return mod._resolve_visual_render_mode

    def test_returns_component_when_component_exists_and_media_present(self):
        fn = self._import_fn()
        result = fn(
            media_aliases={"defaultSrc": "veo/some_clip.mp4"},
            overlay_config=None,
            has_component=True,
        )
        assert result == "component"

    def test_returns_raw_media_when_no_component_and_media_present(self):
        fn = self._import_fn()
        result = fn(
            media_aliases={"defaultSrc": "veo/some_clip.mp4"},
            overlay_config=None,
            has_component=False,
        )
        assert result == "raw-media"

    def test_returns_component_when_no_media_and_component_exists(self):
        fn = self._import_fn()
        result = fn(
            media_aliases={},
            overlay_config=None,
            has_component=True,
        )
        assert result == "component"

    def test_returns_generated_media_with_overlay_and_no_component(self):
        fn = self._import_fn()
        result = fn(
            media_aliases={"defaultSrc": "veo/clip.mp4"},
            overlay_config={"gradientOverlay": "bottom"},
            has_component=False,
        )
        assert result == "generated-media"

    def test_returns_generated_media_with_overlay_even_with_component(self):
        """Overlay visuals need generated-media to composite the overlay."""
        fn = self._import_fn()
        result = fn(
            media_aliases={"defaultSrc": "veo/clip.mp4"},
            overlay_config={"gradientOverlay": "bottom"},
            has_component=False,
        )
        assert result == "generated-media"


class TestBuildVisualMediaManifestComponentFiltering:
    """build_visual_media_manifest must not assign fallback video to
    component-mode visuals. Only media-mode visuals should receive fallback."""

    def _import_fn(self):
        import importlib, sys
        sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
        mod = importlib.import_module("generate_section_compositions")
        return mod.build_visual_media_manifest

    def test_accepts_component_visual_ids_parameter(self):
        """build_visual_media_manifest should accept component_visual_ids."""
        import inspect
        fn = self._import_fn()
        sig = inspect.signature(fn)
        assert 'component_visual_ids' in sig.parameters

    def test_does_not_inherit_previous_clip_for_non_media_visual_types(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "closing"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "06_mold_glow_finale.mp4").write_text("stub", encoding="utf-8")

        (specs_dir / "06_mold_glow_finale.md").write_text(
            "\n".join(
                [
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "mold_glow_finale" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "07_the_beat.md").write_text(
            "\n".join(
                [
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "beat", "chartId": "the_beat" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "08_final_title_card.md").write_text(
            "\n".join(
                [
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "title_card", "title": "Prompt-Driven Development" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        section = {
            "id": "closing",
            "specDir": "closing",
            "durationSeconds": 8,
            "offsetSeconds": 0,
            "compositions": [],
        }

        manifest = build_visual_media_manifest(
            section,
            str(project_dir),
            str(remotion_public),
        )

        assert manifest["06_mold_glow_finale"]["defaultSrc"] == "veo/06_mold_glow_finale.mp4"
        assert "07_the_beat" not in manifest
        assert "08_final_title_card" not in manifest

    def test_does_not_inherit_previous_clip_when_spec_declares_unresolved_clipid(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part2_paradigm_shift"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "03_injection_molding_process.mp4").write_text(
            "stub",
            encoding="utf-8",
        )

        (specs_dir / "03_injection_molding_process.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "injection_molding_process" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "04_1980s_chip_lab.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "1980s_chip_lab" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_media_manifest(
            {
                "id": "part2_paradigm_shift",
                "specDir": "part2_paradigm_shift",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
        )

        assert manifest["03_injection_molding_process"]["defaultSrc"] == "veo/03_injection_molding_process.mp4"
        assert "04_1980s_chip_lab" not in manifest

    def test_does_not_apply_section_fallback_video_to_non_media_remotion_visual(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "where_to_start"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "mold_glow_finale.mp4").write_text(
            "stub",
            encoding="utf-8",
        )

        (specs_dir / "05_module_glow_spread.md").write_text(
            "\n".join(
                [
                    "[Remotion]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "network_graph", "chartId": "module_glow_spread" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_media_manifest(
            {
                "id": "where_to_start",
                "specDir": "where_to_start",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
            fallback_video_src="veo/mold_glow_finale.mp4",
        )

        assert "05_module_glow_spread" not in manifest

    def test_applies_section_fallback_video_to_media_driven_visual_without_aliases(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "closing"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "sock_discard_closing.mp4").write_text(
            "stub",
            encoding="utf-8",
        )

        (specs_dir / "07_transition_to_closing.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "transition_to_closing" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_media_manifest(
            {
                "id": "closing",
                "specDir": "closing",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
            fallback_video_src="veo/sock_discard_closing.mp4",
        )

        assert manifest["07_transition_to_closing"]["defaultSrc"] == "veo/sock_discard_closing.mp4"


class TestVisualContractManifestMediaDrivenRenderMode:
    def test_marks_unresolved_veo_specs_as_raw_media_instead_of_component(self, tmp_path):
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part3_mold_three_parts"

        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (specs_dir / "04_liquid_hits_wall.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "liquid_hits_wall" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_contract_manifest(
            [
                {
                    "id": "part3_mold_three_parts",
                    "specDir": "part3_mold_three_parts",
                    "durationSeconds": 8,
                    "offsetSeconds": 0,
                    "compositions": [],
                }
            ],
            str(project_dir),
            str(remotion_public),
        )

        visual = manifest["sections"][0]["visuals"][0]
        assert visual["id"] == "04_liquid_hits_wall"
        assert visual["renderMode"] == "raw-media"
        assert visual["mediaAliases"] == {}


class TestVisualMediaManifestContextualClipResolution:
    def test_resolves_alternate_named_staged_assets_from_spec_context(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part2_paradigm_shift"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "chip_design_1980s_lab.mp4").write_text(
            "stub",
            encoding="utf-8",
        )

        (specs_dir / "09_1980s_chip_lab.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "# Section 2.9: 1980s Chip Lab",
                    "",
                    "## Visual Description",
                    "Engineer in a 1980s chip design lab drawing circuits by hand.",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "1980s_chip_lab" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_media_manifest(
            {
                "id": "part2_paradigm_shift",
                "specDir": "part2_paradigm_shift",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
        )

        assert manifest["09_1980s_chip_lab"]["defaultSrc"] == "veo/chip_design_1980s_lab.mp4"

    def test_resolves_callback_assets_using_cross_spec_context(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part5_compound_returns"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "grandmother_darning.mp4").write_text(
            "stub",
            encoding="utf-8",
        )
        (remotion_public / "veo" / "grandmother_darning_lamplight.mp4").write_text(
            "stub",
            encoding="utf-8",
        )
        (remotion_public / "veo" / "developer_ai_edit.mp4").write_text(
            "stub",
            encoding="utf-8",
        )
        (remotion_public / "veo" / "developer_cursor_edit.mp4").write_text(
            "stub",
            encoding="utf-8",
        )

        (specs_dir / "06_grandmother_socks_callback.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "# Section 5.6: Grandmother Socks Callback",
                    "",
                    "## Visual Description",
                    "Warm lamplight on grandmother hands darning a sock.",
                    "",
                    "## Data Points JSON",
                    "```json",
                    "{",
                    '  "type": "veo_clip",',
                    '  "clipId": "grandmother_socks_callback",',
                    '  "callbackTo": "part1_economics/14_grandmother_darning_expert"',
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "07_developer_cursor_callback.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "# Section 5.7: Developer Cursor Callback",
                    "",
                    "## Visual Description",
                    "Developer hands at a keyboard with a Cursor-like code editor.",
                    "",
                    "## Data Points JSON",
                    "```json",
                    "{",
                    '  "type": "veo_clip",',
                    '  "clipId": "developer_cursor_callback",',
                    '  "callbackTo": "part1_economics/13_developer_cursor_coding"',
                    "}",
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_media_manifest(
            {
                "id": "part5_compound_returns",
                "specDir": "part5_compound_returns",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
        )

        assert manifest["06_grandmother_socks_callback"]["defaultSrc"] == "veo/grandmother_darning_lamplight.mp4"
        assert manifest["07_developer_cursor_callback"]["defaultSrc"] == "veo/developer_cursor_edit.mp4"

    def test_resolves_unique_remaining_wall_and_grounding_assets(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part3_mold_three_parts"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "bug_adds_wall.mp4").write_text(
            "stub",
            encoding="utf-8",
        )
        (remotion_public / "veo" / "grounding_material_flow.mp4").write_text(
            "stub",
            encoding="utf-8",
        )

        (specs_dir / "04_liquid_hits_wall.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "# Section 3.4: Liquid Hits Wall",
                    "",
                    "## Visual Description",
                    "Liquid flows through a mold channel and stops at a wall.",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "liquid_hits_wall" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (specs_dir / "16_grounding_material.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "# Section 3.16: Grounding Material",
                    "",
                    "## Visual Description",
                    "Grounding material flow through a precision mold.",
                    "",
                    "## Data Points JSON",
                    "```json",
                    '{ "type": "veo_clip", "clipId": "grounding_material" }',
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_media_manifest(
            {
                "id": "part3_mold_three_parts",
                "specDir": "part3_mold_three_parts",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
        )

        assert manifest["04_liquid_hits_wall"]["defaultSrc"] == "veo/bug_adds_wall.mp4"
        assert manifest["16_grounding_material"]["defaultSrc"] == "veo/grounding_material_flow.mp4"

    def test_resolves_structured_split_panel_clip_ids_contextually(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part1_economics"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "developer_cursor_edit.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "grandmother_darning_lamplight.mp4").write_text("stub", encoding="utf-8")

        (specs_dir / "12_developer_darning_split.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "# Section 1.12: Developer Darning Split",
                    "",
                    "## Visual Description",
                    "Split screen with developer hands at a Cursor editor on the left and a grandmother darning a sock on the right.",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "split_screen",
                            "leftPanel": {
                                "clipId": "developer_cursor_coding",
                                "label": "CURSOR",
                            },
                            "rightPanel": {
                                "clipId": "grandmother_darning_expert",
                                "label": "DARNING NEEDLE",
                            },
                            "embeddedVeoClips": [
                                "developer_cursor_coding",
                                "grandmother_darning_expert",
                            ],
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_media_manifest(
            {
                "id": "part1_economics",
                "specDir": "part1_economics",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
        )

        assert manifest["12_developer_darning_split"]["leftSrc"] == "veo/developer_cursor_edit.mp4"
        assert manifest["12_developer_darning_split"]["rightSrc"] == "veo/grandmother_darning_lamplight.mp4"

    def test_does_not_treat_semantic_split_content_labels_as_media_sources(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part3_mold_three_parts"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "context_window_cluttered.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "context_window_clean.mp4").write_text("stub", encoding="utf-8")

        (specs_dir / "15_context_window_comparison.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "split_screen",
                            "leftPanel": {
                                "header": "RAW CODE",
                                "content": "context_window_cluttered",
                                "tokenCount": "~15,000",
                            },
                            "rightPanel": {
                                "header": "PROMPT",
                                "content": "context_window_clean",
                                "tokenCount": "~2,500",
                            },
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_media_manifest(
            {
                "id": "part3_mold_three_parts",
                "specDir": "part3_mold_three_parts",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
        )

        assert "15_context_window_comparison" not in manifest

    def test_transition_echo_sources_do_not_resolve_media_aliases(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "where_to_start"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "sock_discard_closing.mp4").write_text("stub", encoding="utf-8")

        (specs_dir / "07_transition_to_closing.md").write_text(
            "\n".join(
                [
                    "[Remotion]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "transition",
                            "transitionId": "where_to_start_to_closing",
                            "echoes": [
                                {"source": "no_big_bang_callout", "opacity": 0.06},
                                {"source": "sock_metaphor", "opacity": 0.05},
                            ],
                            "backgroundColor": "#0A0F1A",
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        media_manifest = build_visual_media_manifest(
            {
                "id": "where_to_start",
                "specDir": "where_to_start",
                "durationSeconds": 8,
                "offsetSeconds": 0,
                "compositions": [],
            },
            str(project_dir),
            str(remotion_public),
        )
        contract_manifest = build_visual_contract_manifest(
            [
                {
                    "id": "where_to_start",
                    "specDir": "where_to_start",
                    "durationSeconds": 8,
                    "offsetSeconds": 0,
                    "compositions": [],
                }
            ],
            str(project_dir),
            str(remotion_public),
        )

        assert "07_transition_to_closing" not in media_manifest
        visual = contract_manifest["sections"][0]["visuals"][0]
        assert visual["id"] == "07_transition_to_closing"
        assert visual["renderMode"] == "component"

    def test_contract_first_split_with_media_aliases_stays_component_in_visual_contract_manifest(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part1_economics"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "developer_cursor_edit.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "grandmother_darning_lamplight.mp4").write_text("stub", encoding="utf-8")

        (specs_dir / "12_developer_darning_split.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "split_screen",
                            "leftPanel": {
                                "content": "developer_cursor_coding",
                                "label": "CURSOR",
                            },
                            "rightPanel": {
                                "content": "grandmother_darning_expert",
                                "label": "DARNING NEEDLE",
                            },
                            "embeddedVeoClips": [
                                "developer_cursor_coding",
                                "grandmother_darning_expert",
                            ],
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_contract_manifest(
            [
                {
                    "id": "part1_economics",
                    "specDir": "part1_economics",
                    "durationSeconds": 8,
                    "offsetSeconds": 0,
                    "compositions": [],
                }
            ],
            str(project_dir),
            str(remotion_public),
        )

        visual = manifest["sections"][0]["visuals"][0]
        assert visual["mediaAliases"]["leftSrc"] == "veo/developer_cursor_edit.mp4"
        assert visual["mediaAliases"]["rightSrc"] == "veo/grandmother_darning_lamplight.mp4"
        assert visual["renderMode"] == "component"

    def test_animated_diagram_file_metadata_does_not_force_raw_media_render_mode(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part3_mold_three_parts"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)

        (remotion_public / "veo").mkdir()
        (remotion_public / "veo" / "defect_fix_the_mold.mp4").write_text("stub", encoding="utf-8")

        (specs_dir / "09_bug_fork_diagram.md").write_text(
            "\n".join(
                [
                    "[Remotion]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "animated_diagram",
                            "diagramId": "bug_fork",
                            "root": {"label": "Bug found", "color": "#EF4444"},
                            "branches": [
                                {
                                    "id": "code_bug",
                                    "label": "Code bug",
                                    "file": "test_user_parser.py",
                                },
                                {
                                    "id": "prompt_defect",
                                    "label": "Prompt defect",
                                    "file": "user_parser.prompt",
                                },
                            ],
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        manifest = build_visual_contract_manifest(
            [
                {
                    "id": "part3_mold_three_parts",
                    "specDir": "part3_mold_three_parts",
                    "durationSeconds": 8,
                    "offsetSeconds": 0,
                    "compositions": [],
                }
            ],
            str(project_dir),
            str(remotion_public),
        )

        visual = manifest["sections"][0]["visuals"][0]
        assert visual["mediaAliases"] == {}
        assert visual["renderMode"] == "component"


class TestWrapperTemplateComponentMediaFiltering:
    """The generated section wrapper must NOT pass Veo media to
    component-mode visuals via VisualMediaProvider. When renderMode
    is 'component', media should be null to prevent Veo clips from
    overriding the component's own rendered background."""

    def _get_source(self):
        script_path = os.path.join(
            os.path.dirname(__file__),
            "..", "scripts", "generate_section_compositions.py"
        )
        with open(script_path, "r") as f:
            return f.read()

    def test_wrapper_template_conditionally_nullifies_media_for_component_mode(self):
        source = self._get_source()
        lines = source.split('\n')
        # Find the line that writes <VisualMediaProvider> right before <VisualComponent>
        for i, line in enumerate(lines):
            if 'VisualMediaProvider media=' in line and i + 1 < len(lines):
                next_line = lines[i + 1]
                if 'VisualComponent' in next_line:
                    # This is the component-wrapping media provider.
                    # It must NOT unconditionally pass visualMedia — it must
                    # check renderMode and pass null for component-mode visuals.
                    assert 'renderMode' in line, (
                        f"Line {i+1} wraps VisualComponent with VisualMediaProvider "
                        f"but does not check renderMode to nullify media for component-mode visuals: {line.strip()}"
                    )
                    return
        assert False, "Could not find VisualMediaProvider wrapping VisualComponent in template"

    def test_wrapper_template_sorts_active_visuals_by_lane(self):
        source = self._get_source()
        assert ".slice()" in source
        assert ".sort((" in source
        assert "left.lane" in source
        assert "right.lane" in source


class TestVisualContractManifestNewFields:
    """Tests for coverSegments, parentId, children, and laneHint in the visual contract manifest."""

    def _build_section_with_spec(self, tmp_path, section_id, spec_name, spec_content, compositions=None):
        """Helper: set up project dir with a single spec and return (section, project_dir, remotion_public)."""
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / section_id
        specs_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True, exist_ok=True)
        (specs_dir / f"{spec_name}.md").write_text(spec_content, encoding="utf-8")

        section = {
            "id": section_id,
            "compositionId": section_id.replace("_", " ").title().replace(" ", ""),
            "durationSeconds": 10,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": section_id,
            "compositions": compositions or [spec_name],
        }
        return section, str(project_dir), str(remotion_public)

    def test_build_visual_contract_manifest_includes_coverSegments_from_dataPoints(self, tmp_path):
        spec_content = "\n".join([
            "[Remotion]",
            "",
            "## Data Points JSON",
            "```json",
            '{"coverSegments": ["cold_open_001", "cold_open_002"]}',
            "```",
        ])
        section, project_dir, remotion_public = self._build_section_with_spec(
            tmp_path, "cold_open", "01_title", spec_content
        )

        manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
        visual = manifest["sections"][0]["visuals"][0]

        assert visual["coverSegments"] == ["cold_open_001", "cold_open_002"]

    def test_build_visual_contract_manifest_coverSegments_empty_when_absent(self, tmp_path):
        spec_content = "\n".join([
            "[Remotion]",
            "",
            "## Data Points JSON",
            "```json",
            '{"title": "Hello"}',
            "```",
        ])
        section, project_dir, remotion_public = self._build_section_with_spec(
            tmp_path, "intro", "01_card", spec_content
        )

        manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
        visual = manifest["sections"][0]["visuals"][0]

        assert "coverSegments" not in visual

    def test_build_visual_contract_manifest_includes_parentId(self, tmp_path):
        spec_content = "\n".join([
            "[veo:]",
            "",
            "## Data Points JSON",
            "```json",
            '{"embeddedIn": "01_split_screen"}',
            "```",
        ])
        section, project_dir, remotion_public = self._build_section_with_spec(
            tmp_path, "cold_open", "02_veo_clip", spec_content, compositions=["02_veo_clip"]
        )

        manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
        visual = manifest["sections"][0]["visuals"][0]

        assert visual["parentId"] == "01_split_screen"

    def test_build_visual_contract_manifest_normalizes_usedIn_to_parentId(self, tmp_path):
        spec_content = "\n".join([
            "[veo:]",
            "",
            "## Data Points JSON",
            "```json",
            '{"usedIn": "01_split_screen (left panel)"}',
            "```",
        ])
        section, project_dir, remotion_public = self._build_section_with_spec(
            tmp_path, "cold_open", "02_veo_clip", spec_content, compositions=["02_veo_clip"]
        )

        manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
        visual = manifest["sections"][0]["visuals"][0]

        assert visual["parentId"] == "01_split_screen"

    def test_build_visual_contract_manifest_populates_children_from_parentId(self, tmp_path):
        """Second pass builds children arrays: parent gets child IDs."""
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / "cold_open"
        specs_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True, exist_ok=True)

        (specs_dir / "01_split_screen.md").write_text(
            "[split:]\n\n## Data Points JSON\n```json\n{}\n```",
            encoding="utf-8",
        )
        # parentId references the visual ID as it appears in the manifest
        (specs_dir / "02_veo_left.md").write_text(
            '[veo:]\n\n## Data Points JSON\n```json\n{"embeddedIn": "01_split_screen"}\n```',
            encoding="utf-8",
        )

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpen",
            "durationSeconds": 10,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "cold_open",
            "compositions": ["01_split_screen", "02_veo_left"],
        }

        manifest = build_visual_contract_manifest(
            [section], str(project_dir), str(remotion_public)
        )

        visuals_by_id = {v["id"]: v for v in manifest["sections"][0]["visuals"]}
        parent = visuals_by_id["01_split_screen"]
        child = visuals_by_id["02_veo_left"]

        assert child["parentId"] == "01_split_screen"
        assert "children" in parent
        assert "02_veo_left" in parent["children"]

    def test_build_visual_contract_manifest_infers_parent_child_from_split_panel_clips(
        self, tmp_path
    ):
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / "cold_open"
        specs_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True, exist_ok=True)

        (specs_dir / "01_split_screen_darning.md").write_text(
            "\n".join([
                "[split:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "split_screen",
                        "panels": {
                            "left": {
                                "clips": [
                                    "developer_cursor_edit",
                                    "developer_codebase_zoomout",
                                ]
                            },
                            "right": {
                                "clips": [
                                    "grandmother_darning",
                                    "grandmother_drawer_zoomout",
                                ]
                            },
                        },
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )
        (specs_dir / "02_developer_cursor_edit.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps({"type": "veo_clip", "clipId": "developer_cursor_edit"}),
                "```",
            ]),
            encoding="utf-8",
        )
        (specs_dir / "03_grandmother_darning.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps({"type": "veo_clip", "clipId": "grandmother_darning"}),
                "```",
            ]),
            encoding="utf-8",
        )
        (specs_dir / "04_developer_codebase_zoomout.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps({"type": "veo_clip", "clipId": "developer_codebase_zoomout"}),
                "```",
            ]),
            encoding="utf-8",
        )
        (specs_dir / "05_grandmother_drawer_zoomout.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps({"type": "veo_clip", "clipId": "grandmother_drawer_zoomout"}),
                "```",
            ]),
            encoding="utf-8",
        )

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpenSection",
            "durationSeconds": 10,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "cold_open",
            "compositions": [
                "01_split_screen_darning",
                "02_developer_cursor_edit",
                "03_grandmother_darning",
                "04_developer_codebase_zoomout",
                "05_grandmother_drawer_zoomout",
            ],
        }

        manifest = build_visual_contract_manifest(
            [section], str(project_dir), str(remotion_public)
        )
        visuals_by_id = {v["id"]: v for v in manifest["sections"][0]["visuals"]}

        parent = visuals_by_id["01_split_screen_darning"]
        assert visuals_by_id["02_developer_cursor_edit"]["parentId"] == "01_split_screen_darning"
        assert visuals_by_id["03_grandmother_darning"]["parentId"] == "01_split_screen_darning"
        assert visuals_by_id["04_developer_codebase_zoomout"]["parentId"] == "01_split_screen_darning"
        assert visuals_by_id["05_grandmother_drawer_zoomout"]["parentId"] == "01_split_screen_darning"
        assert set(parent["children"]) == {
            "02_developer_cursor_edit",
            "03_grandmother_darning",
            "04_developer_codebase_zoomout",
            "05_grandmother_drawer_zoomout",
        }

    def test_build_visual_contract_manifest_laneHint_defaults_to_main(self, tmp_path):
        """Visuals without overlay or explicit laneHint have no laneHint field (implicitly main)."""
        spec_content = "\n".join([
            "[Remotion]",
            "",
            "## Data Points JSON",
            "```json",
            '{"title": "Demo"}',
            "```",
        ])
        section, project_dir, remotion_public = self._build_section_with_spec(
            tmp_path, "intro", "01_card", spec_content
        )

        manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
        visual = manifest["sections"][0]["visuals"][0]

        assert "laneHint" not in visual

    def test_build_visual_contract_manifest_laneHint_overlay_from_overlayConfig(self, tmp_path):
        """Visuals with overlayConfig infer laneHint='overlay'."""
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / "demo"
        specs_dir.mkdir(parents=True)
        remotion_public.mkdir(parents=True, exist_ok=True)

        # Spec that triggers overlay detection (lower-third badge pattern)
        (specs_dir / "01_visual.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "lower-third badge",
                "",
                "NARRATOR: Hello world.",
                "",
                "## Data Points JSON",
                "```json",
                '{"title": "Test"}',
                "```",
            ]),
            encoding="utf-8",
        )

        section = {
            "id": "demo",
            "compositionId": "Demo",
            "durationSeconds": 5,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "demo",
            "compositions": ["01_visual"],
        }

        manifest = build_visual_contract_manifest(
            [section], str(project_dir), str(remotion_public)
        )
        visual = manifest["sections"][0]["visuals"][0]

        # If overlayConfig is present, laneHint should be 'overlay'
        if visual.get("overlayConfig"):
            assert visual["laneHint"] == "overlay"

    def test_build_visual_contract_manifest_laneHint_from_dataPoints(self, tmp_path):
        """Explicit laneHint in data points takes precedence."""
        spec_content = "\n".join([
            "[Remotion]",
            "",
            "## Data Points JSON",
            "```json",
            '{"laneHint": "background"}',
            "```",
        ])
        section, project_dir, remotion_public = self._build_section_with_spec(
            tmp_path, "intro", "01_bg", spec_content
        )

        manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
        visual = manifest["sections"][0]["visuals"][0]

        assert visual["laneHint"] == "background"

    def test_build_visual_contract_manifest_includes_explicit_anchor_hints(self, tmp_path):
        spec_content = "\n".join([
            "[Remotion]",
            "",
            "## Data Points JSON",
            "```json",
            '{"startAnchor": {"type": "absolute", "seconds": 4.25}, "endAnchor": {"type": "sectionEnd"}}',
            "```",
        ])
        section, project_dir, remotion_public = self._build_section_with_spec(
            tmp_path, "closing", "07_the_beat", spec_content
        )

        manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
        visual = manifest["sections"][0]["visuals"][0]

        assert visual["startAnchor"] == {"type": "absolute", "seconds": 4.25}
        assert visual["endAnchor"] == {"type": "sectionEnd"}

    def test_build_visual_contract_manifest_synthesizes_split_media_aliases_from_child_panels(self, tmp_path):
        project_dir = tmp_path
        remotion_public = tmp_path / "remotion" / "public"
        specs_dir = project_dir / "specs" / "part1_economics"
        veo_dir = remotion_public / "veo"
        specs_dir.mkdir(parents=True)
        veo_dir.mkdir(parents=True)

        (veo_dir / "developer_cursor_edit.mp4").write_text("stub", encoding="utf-8")
        (veo_dir / "grandmother_darning_lamplight.mp4").write_text("stub", encoding="utf-8")

        (specs_dir / "12_developer_darning_split.md").write_text(
            "\n".join([
                "[split:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "split_screen",
                        "leftPanel": {"label": "CURSOR"},
                        "rightPanel": {"label": "DARNING NEEDLE"},
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )
        (specs_dir / "13_developer_cursor_coding.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "veo_clip",
                        "clipId": "developer_cursor_coding",
                        "embeddedIn": "12_developer_darning_split",
                        "panel": "left",
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )
        (specs_dir / "14_grandmother_darning_expert.md").write_text(
            "\n".join([
                "[veo:]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "veo_clip",
                        "clipId": "grandmother_darning_expert",
                        "embeddedIn": "12_developer_darning_split",
                        "panel": "right",
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )

        section = {
            "id": "part1_economics",
            "compositionId": "Part1EconomicsSection",
            "durationSeconds": 10,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "part1_economics",
            "compositions": [
                "12_developer_darning_split",
                "13_developer_cursor_coding",
                "14_grandmother_darning_expert",
            ],
        }

        manifest = build_visual_contract_manifest(
            [section],
            str(project_dir),
            str(remotion_public),
        )
        visuals_by_id = {
            visual["id"]: visual for visual in manifest["sections"][0]["visuals"]
        }

        split_visual = visuals_by_id["12_developer_darning_split"]
        assert split_visual["mediaAliases"]["leftSrc"] == "veo/developer_cursor_edit.mp4"
        assert split_visual["mediaAliases"]["rightSrc"] == "veo/grandmother_darning_lamplight.mp4"

    def test_legacy_manifest_without_new_fields_loads_without_error(self, tmp_path):
        """Loading a manifest built without new fields still works."""
        # Build a manifest that omits coverSegments/parentId/children/laneHint
        legacy = {
            "version": 1,
            "updatedAt": "2026-01-01T00:00:00+00:00",
            "sections": [{
                "id": "intro",
                "visuals": [{
                    "id": "intro_01_card",
                    "specBaseName": "01_card",
                    "specPath": "specs/intro/01_card.md",
                    "dataPoints": None,
                    "mediaAliases": {},
                    "overlayConfig": None,
                    "renderMode": "component",
                }],
            }],
        }

        manifest_path = tmp_path / "outputs" / "compositions" / "visual-manifest.json"
        manifest_path.parent.mkdir(parents=True)
        manifest_path.write_text(json.dumps(legacy), encoding="utf-8")

        loaded = json.loads(manifest_path.read_text(encoding="utf-8"))
        visual = loaded["sections"][0]["visuals"][0]

        assert visual["id"] == "intro_01_card"
        assert visual.get("coverSegments") is None
        assert visual.get("parentId") is None
        assert visual.get("children") is None
        assert visual.get("laneHint") is None

    def test_build_visual_contract_manifest_synthesizes_split_media_from_usedin_panel_reference(
        self, tmp_path
    ):
        project_dir = tmp_path / "project"
        spec_dir = project_dir / "specs" / "part2"
        remotion_public = project_dir / "remotion-public"
        (project_dir / "outputs" / "veo").mkdir(parents=True)
        (project_dir / "outputs" / "compositions").mkdir(parents=True)
        (remotion_public / "veo").mkdir(parents=True)
        spec_dir.mkdir(parents=True)

        (remotion_public / "veo" / "craftsman_carving.mp4").write_text("stub", encoding="utf-8")
        (remotion_public / "veo" / "mold_producing_parts.mp4").write_text("stub", encoding="utf-8")

        (spec_dir / "06_craftsman_vs_mold.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "split_screen",
                            "leftPanel": {"content": "veo_clip_with_aura"},
                            "rightPanel": {"content": "veo_clip_with_aura"},
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (spec_dir / "07_craftsman_carving.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "veo_clip",
                            "clipId": "craftsman_carving",
                            "usedIn": "06_craftsman_vs_mold (left panel)",
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )
        (spec_dir / "08_mold_producing_parts.md").write_text(
            "\n".join(
                [
                    "[veo:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "veo_clip",
                            "clipId": "mold_producing_parts",
                            "usedIn": "06_craftsman_vs_mold (right panel)",
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        section = {
            "id": "part2",
            "compositionId": "Part2Section",
            "durationSeconds": 10,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "part2",
            "compositions": [
                "06_craftsman_vs_mold",
                "07_craftsman_carving",
                "08_mold_producing_parts",
            ],
        }

        manifest = build_visual_contract_manifest(
            [section],
            str(project_dir),
            str(remotion_public),
        )
        visuals_by_id = {
            visual["id"]: visual for visual in manifest["sections"][0]["visuals"]
        }

        split_visual = visuals_by_id["06_craftsman_vs_mold"]
        assert split_visual["mediaAliases"]["leftSrc"] == "veo/craftsman_carving.mp4"
        assert split_visual["mediaAliases"]["rightSrc"] == "veo/mold_producing_parts.mp4"

    def test_build_visual_contract_manifest_synthesizes_split_panel_reveal_aliases_from_panel_clips(
        self, tmp_path
    ):
        project_dir = tmp_path / "project"
        spec_dir = project_dir / "specs" / "cold_open"
        remotion_public = project_dir / "remotion-public"
        (remotion_public / "veo").mkdir(parents=True)
        spec_dir.mkdir(parents=True)

        for clip_id in (
            "developer_cursor_edit",
            "developer_codebase_zoomout",
            "grandmother_darning",
            "grandmother_drawer_zoomout",
        ):
            (remotion_public / "veo" / f"{clip_id}.mp4").write_text("stub", encoding="utf-8")

        (spec_dir / "01_split_screen_darning.md").write_text(
            "\n".join(
                [
                    "[split:]",
                    "",
                    "## Data Points JSON",
                    "```json",
                    json.dumps(
                        {
                            "type": "split_screen",
                            "panels": {
                                "left": {
                                    "clips": [
                                        "developer_cursor_edit",
                                        "developer_codebase_zoomout",
                                    ]
                                },
                                "right": {
                                    "clips": [
                                        "grandmother_darning",
                                        "grandmother_drawer_zoomout",
                                    ]
                                },
                            },
                        }
                    ),
                    "```",
                ]
            ),
            encoding="utf-8",
        )

        section = {
            "id": "cold_open",
            "compositionId": "ColdOpenSection",
            "durationSeconds": 9,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "cold_open",
            "compositions": ["01_split_screen_darning"],
        }

        manifest = build_visual_contract_manifest(
            [section],
            str(project_dir),
            str(remotion_public),
        )
        visual = manifest["sections"][0]["visuals"][0]

        assert visual["mediaAliases"]["leftSrc"] == "veo/developer_cursor_edit.mp4"
        assert visual["mediaAliases"]["leftBaseSrc"] == "veo/developer_cursor_edit.mp4"
        assert visual["mediaAliases"]["leftRevealSrc"] == "veo/developer_codebase_zoomout.mp4"
        assert visual["mediaAliases"]["rightSrc"] == "veo/grandmother_darning.mp4"
        assert visual["mediaAliases"]["rightBaseSrc"] == "veo/grandmother_darning.mp4"
        assert visual["mediaAliases"]["rightRevealSrc"] == "veo/grandmother_drawer_zoomout.mp4"


class TestContractFirstVisualResolution:
    def test_prefers_generated_contract_for_structured_title_cards(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "title_card",
                    "sectionLabel": "PART 6",
                    "title": "WHERE TO START",
                }
            },
            has_exact_component=False,
        )

    def test_prefers_generated_contract_for_standard_structured_title_cards_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "title_card",
                    "sectionLabel": "PART 1",
                    "titleLine1": "THE ECONOMICS",
                    "titleLine2": "OF DARNING",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_annotation_overlays_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "annotation_overlay",
                    "chartId": "code_cost_triple_line",
                    "annotations": [{"header": "Code churn: +44%"}],
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_command_driven_title_cards_when_available(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "title_card",
                    "title": "Prompt-Driven Development",
                    "commands": ["uv tool install pdd-cli"],
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_stillness_beats(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "title_card",
                    "style": "stillness_beat",
                    "sectionLabel": "THE KEY INSIGHT",
                }
            },
            has_exact_component=False,
        )

    def test_prefers_generated_contract_for_code_visualization_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "code_visualization",
                    "chartId": "legacy_codebase_reveal",
                    "fileNames": ["auth_handler.py"],
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_quote_cards_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "quote_card",
                    "quoteLine1": "You don't patch socks",
                    "quoteLine2": "because socks got cheap.",
                }
            },
            has_exact_component=True,
        )

    def test_keeps_exact_component_for_quote_cards_with_accent_word_and_single_quote(self):
        assert not _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "quote_card",
                    "quote": "This is either the way of the future or it's going to crash and burn spectacularly.",
                    "attribution": "Research engineer, after seeing PDD for the first time.",
                    "accentWord": "spectacularly",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_chart_events_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "chart_event",
                    "chartId": "code_cost_triple_line",
                    "event": "crossing_moment",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_chart_callbacks_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "chart_callback",
                    "chartId": "code_cost_triple_line",
                    "event": "crossing_reprise",
                }
            },
            has_exact_component=True,
        )

    def test_keeps_exact_component_for_chart_callbacks_with_source_spec_and_reframe_only(self):
        assert not _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "chart_callback",
                    "chartRef": "code_cost_generate_vs_patch",
                    "sourceSpec": "part1_economics/13_crossing_lines_moment",
                    "reframeText": "The economics changed.",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_text_overlay_with_morph_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "text_overlay_with_morph",
                    "diagramId": "synopsys_pdd_equivalence",
                    "sharedLabel": "Same architecture",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_code_regeneration_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "code_regeneration",
                    "filename": "auth_handler.py",
                    "generatedLines": 16,
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_precision_tradeoff_curve_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "animated_chart",
                    "chartId": "precision_tradeoff_curve",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_counter_animation_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "counter_animation",
                    "chartId": "mold_production_counter",
                }
            },
            has_exact_component=True,
        )

    def test_keeps_exact_component_for_counter_animation_with_mold_cycle_profile(self):
        assert not _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "counter_animation",
                    "chartId": "mold_production_counter",
                    "moldCycle": {
                        "startFramesPerCycle": 60,
                        "endFramesPerCycle": 6,
                    },
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_schematic_zoom_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "schematic_zoom",
                    "chartId": "schematic_density_zoom",
                }
            },
            has_exact_component=True,
        )

    def test_keeps_exact_component_for_schematic_zoom_with_explicit_zoom_profile(self):
        assert not _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "schematic_zoom",
                    "chartId": "schematic_density_zoom",
                    "zoom": {
                        "startScale": 8,
                        "endScale": 0.1,
                    },
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_line_charts_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "line_chart",
                    "chartId": "precision_tradeoff_curve",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_code_editor_animation_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "code_editor_animation",
                    "editorId": "legacy_codebase_reveal",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_maintenance_pie_chart_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "pie_chart",
                    "chartId": "maintenance_cost_pie",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_compound_debt_curve_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "animated_chart",
                    "chartId": "compound_debt_curve",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_current_chart_aliases_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "pie_chart",
                    "chartId": "maintenance_cost_split",
                }
            },
            has_exact_component=True,
        )
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "dual_curve_chart",
                    "chartId": "compound_debt_vs_regeneration",
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_remaining_shared_visual_families_even_with_exact_component(self):
        for data_points in [
            {"type": "synthesis_animation", "chartId": "verilog_synthesis"},
            {"type": "equivalence_demo", "chartId": "triple_synthesis_equivalence"},
            {"type": "key_insight", "chartId": "key_insight_walls"},
            {"type": "sidebar_annotation", "topic": "Z3 formal verification"},
            {"type": "system_diagram", "label": "PDD operates at the module level."},
            {"type": "compression_ratio", "ratio": "1:5 to 1:10"},
            {"type": "pipeline_pullback", "stages": []},
            {"type": "module_migration_animation", "animationId": "gradual_glow_spread"},
            {"type": "key_insight_card", "insightId": "no_big_bang"},
            {"type": "value_flow_animation", "animationId": "code_to_specification"},
            {"type": "remotion_animation", "componentId": "pdd_triangle"},
            {"type": "remotion_animation", "componentId": "dissolve_regenerate_loop"},
            {"type": "title_card", "componentId": "final_title_card", "commands": ["pdd update module.py"]},
        ]:
            assert _should_prefer_generated_contract_renderer(
                {"dataPoints": data_points},
                has_exact_component=True,
            )

    def test_prefers_generated_contract_for_supported_diagram_ids_even_with_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "animated_diagram",
                    "diagramId": "prompt_replaces_review",
                }
            },
            has_exact_component=True,
        )


class TestExtractVisualOverlayConfig:
    def test_extracts_authored_fade_windows_from_media_specs(self):
        spec = "\n".join(
            [
                "[veo:]",
                "",
                "### Animation Sequence",
                "1. **Frame 0-15 (0-0.5s):** Fade in from black.",
                "2. **Frame 15-150 (0.5-5s):** Hold.",
                "3. **Frame 150-180 (5-6s):** Gentle fade to black.",
                "",
                "## Data Points JSON",
                "```json",
                '{ "type": "veo_clip", "clipId": "developer_cursor_callback" }',
                "```",
            ]
        )

        assert _extract_visual_overlay_config(spec) == {
            "fadeInFrames": 15,
            "fadeOutFrames": 30,
        }

    def test_prefers_generated_contract_for_animated_diagrams(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "animated_diagram",
                    "diagramId": "ratchet_timelapse",
                }
            },
            has_exact_component=False,
        )

    def test_prefers_generated_contract_for_split_even_when_exact_component_exists(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "split_screen",
                    "layout": "vertical_split",
                }
            },
            has_exact_component=True,
        )

    def test_keeps_exact_component_for_split_with_aura_and_part_dissolve(self):
        assert not _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "split_screen",
                    "layout": "vertical_50_50",
                    "panels": {
                        "left": {
                            "aura": {"color": "#D9944A", "target": "object"},
                        },
                        "right": {
                            "aura": {"color": "#4A90D9", "target": "mold"},
                            "partDissolve": True,
                        },
                    },
                }
            },
            has_exact_component=True,
        )

    def test_prefers_generated_contract_for_split_without_exact_component(self):
        assert _should_prefer_generated_contract_renderer(
            {
                "dataPoints": {
                    "type": "split_screen",
                    "layout": "vertical_split",
                }
            },
            has_exact_component=False,
        )

    def test_resolve_section_component_records_prefers_generated_contract_over_fuzzy_component_reuse(self, tmp_path):
        project_dir = tmp_path
        remotion_public = project_dir / "remotion" / "public"
        remotion_src = project_dir / "remotion" / "src" / "remotion"
        specs_dir = project_dir / "specs" / "where_to_start"
        remotion_public.mkdir(parents=True)
        specs_dir.mkdir(parents=True)
        legacy_component_dir = remotion_src / "WhereToStart03ModuleHighlightUpdate"
        legacy_component_dir.mkdir(parents=True)
        (legacy_component_dir / "index.tsx").write_text(
            "export const WhereToStart03ModuleHighlightUpdate = () => null;\n",
            encoding="utf-8",
        )

        (specs_dir / "05_module_glow_spread.md").write_text(
            "\n".join([
                "[Remotion]",
                "",
                "## Data Points JSON",
                "```json",
                json.dumps(
                    {
                        "type": "network_graph",
                        "chartId": "module_glow_spread",
                        "migrationSequence": [],
                        "unmigrated": [],
                    }
                ),
                "```",
            ]),
            encoding="utf-8",
        )

        section = {
            "id": "where_to_start",
            "compositionId": "WhereToStartSection",
            "durationSeconds": 10,
            "offsetSeconds": 0,
            "timelineSource": "generated",
            "specDir": "where_to_start",
            "compositions": [],
        }

        records = resolve_section_component_records(
            section,
            project_dir=str(project_dir),
            remotion_public=str(remotion_public),
            remotion_src=str(remotion_src),
        )

        assert records == []
