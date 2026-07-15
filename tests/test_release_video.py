import builtins
import importlib.util
import json
import os
import shlex
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest
import yaml


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "release_video.py"


def release_video_env(extra: dict | None = None) -> dict:
    env = {**os.environ}
    for key in (
        "CLAUDE_MODEL",
        "CLAUDE_TIMEOUT",
        "CLAUDE_CLI",
        "CLAUDE_CODE_OAUTH_TOKEN",
        "CLAUDE_CODE_OAUTH_TOKEN_1",
        "CLAUDE_CODE_OAUTH_TOKEN_2",
        "CLAUDE_CODE_OAUTH_TOKEN_3",
        "RELEASE_VIDEO_CLAUDE_MODEL",
        "RELEASE_VIDEO_ATTEMPT_ID",
        "RELEASE_VIDEO_CLAUDE_TOOLS",
        "RELEASE_VIDEO_IDEMPOTENCY_KEY",
        "RELEASE_VIDEO_IDEMPOTENCY_PROVENANCE",
        "RELEASE_VIDEO_PROMPT_TEMPLATE",
        "RELEASE_VIDEO_BOOTSTRAP_SELECTED_PROJECT",
        "RELEASE_VIDEO_FORCE_REGENERATE",
        "RELEASE_VIDEO_METADATA_CONFLICT",
        "RELEASE_VIDEO_PDS_CLAUDE_MODEL",
        "RELEASE_VIDEO_PDS_CREATE_TIMEOUT",
        "RELEASE_VIDEO_RELEASE_NOTES_PATH",
        "RELEASE_VIDEO_SCRIPT_PATH",
        "PDS_CLI",
        "PDS_API_URL",
        "PDS_PROFILE",
        "PDS_RELEASE_TOKEN",
        "PDS_TOKEN",
        "CI",
        "GITHUB_ACTIONS",
    ):
        env.pop(key, None)
    if extra:
        env.update(extra)
    return env


def test_release_video_env_scrubs_pds_create_timeout(monkeypatch):
    monkeypatch.setenv("RELEASE_VIDEO_PDS_CREATE_TIMEOUT", "1")

    env = release_video_env()

    assert "RELEASE_VIDEO_PDS_CREATE_TIMEOUT" not in env


def test_release_video_claude_model_env_defaults_ignore_empty(monkeypatch):
    release_video = load_release_video_module()
    monkeypatch.delenv("RELEASE_VIDEO_CLAUDE_MODEL", raising=False)
    monkeypatch.setenv("CLAUDE_MODEL", "")

    empty_args = release_video.parse_args([])
    monkeypatch.setenv("CLAUDE_MODEL", "   ")
    whitespace_args = release_video.parse_args([])

    assert empty_args.claude_model == release_video.DEFAULT_CLAUDE_MODEL
    assert whitespace_args.claude_model == release_video.DEFAULT_CLAUDE_MODEL


def test_release_video_specific_claude_model_env_wins_over_global(monkeypatch):
    release_video = load_release_video_module()
    monkeypatch.setenv("CLAUDE_MODEL", "claude-global")
    monkeypatch.setenv("RELEASE_VIDEO_CLAUDE_MODEL", "claude-release-local")

    args = release_video.parse_args([])

    assert args.claude_model == "claude-release-local"


def test_release_video_command_env_defaults_ignore_empty(monkeypatch):
    release_video = load_release_video_module()
    monkeypatch.setenv("CLAUDE_CLI", "")
    monkeypatch.setenv("PDS_CLI", "   ")

    args = release_video.parse_args([])

    assert args.claude_cli == "claude"
    assert args.pds_cli == "pds"


def run(command, cwd: Path, **kwargs):
    return subprocess.run(
        command,
        cwd=cwd,
        text=True,
        capture_output=True,
        check=True,
        **kwargs,
    )


def write_executable(path: Path, content: str) -> Path:
    path.write_text(content, encoding="utf8")
    path.chmod(0o755)
    return path


def init_release_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    run(["git", "-c", "init.defaultBranch=main", "init"], repo)
    run(["git", "config", "user.email", "release@example.test"], repo)
    run(["git", "config", "user.name", "Release Bot"], repo)
    run(["git", "remote", "add", "origin", "https://github.com/promptdriven/pdd.git"], repo)

    (repo / "CHANGELOG.md").write_text(
        "# Changelog\n\n## Unreleased\n\n- Add release video automation.\n",
        encoding="utf8",
    )
    (repo / "pdd.py").write_text("print('first')\n", encoding="utf8")
    run(["git", "add", "."], repo)
    run(["git", "commit", "-m", "initial release"], repo)
    run(["git", "tag", "-a", "v1.0.0", "-m", "Release v1.0.0"], repo)

    (repo / "pdd.py").write_text("print('second')\n", encoding="utf8")
    run(["git", "add", "."], repo)
    run(["git", "commit", "-m", "add release video automation"], repo)
    run(["git", "tag", "-a", "v1.1.0", "-m", "Release v1.1.0"], repo)
    return repo


def claude_stub(tmp_path: Path) -> Path:
    return write_executable(
        tmp_path / "claude-stub.py",
        """#!/usr/bin/env python3
import json
import pathlib
import sys

prompt = sys.stdin.read()
pathlib.Path("claude_prompt.txt").write_text(prompt, encoding="utf8")
pathlib.Path("claude_argv.json").write_text(json.dumps(sys.argv[1:], indent=2), encoding="utf8")
print("# PDD v1.1.0 Release Video\\n\\n"
      "Hook: This release turns the PDD release process into a publishable video story.\\n\\n"
      "Narration: PDD v1.1.0 adds release video automation, using release context to create a concise update for developers. "
      "The narration explains the changed files, release tag, and path from script to YouTube upload. "
      "It closes with a reminder that the release artifact and the release story now ship together.\\n\\n"
      "Visual direction: a text-free matte package cube rests in a soft blue and violet light field.")
""",
    )


def claude_failure_stub(tmp_path: Path, stderr: str, exit_code: int = 1) -> Path:
    return write_executable(
        tmp_path / "claude-failure-stub.py",
        f"""#!/usr/bin/env python3
import sys

sys.stderr.write({stderr!r})
raise SystemExit({exit_code})
""",
    )


def claude_output_stub(tmp_path: Path, stdout: str) -> Path:
    return write_executable(
        tmp_path / "claude-output-stub.py",
        f"""#!/usr/bin/env python3
import sys

sys.stdout.write({stdout!r})
""",
    )


def reusable_script_text() -> str:
    return """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 ships release video automation so maintainers can publish a clear story for every CLI release without changing the package publishing path.

VISUAL: A text-free matte package cube rests in a soft blue and violet light field.

## Details

NARRATOR:
The script highlights what changed, why it matters for developers, and how the generated release artifact flows into the PDS publish step for an unlisted YouTube video.

VISUAL: A translucent shield surrounds a rounded orb in a diffuse color field.
"""


def visual_safety_script(*visual_cues: str) -> str:
    cues = "\n\n".join(f"VISUAL: {cue}" for cue in visual_cues)
    return f"""# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 makes release-video creation fail fast before paid generation when
visual direction would predictably conflict with the downstream video audit.

{cues}

## Close

NARRATOR:
The local validation artifact gives maintainers a stable reason code and keeps
the rejected script available for a safe, inexpensive rewrite and retry.
"""


def load_release_video_module():
    spec = importlib.util.spec_from_file_location("release_video", SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


@pytest.mark.parametrize(
    ("cue", "category", "check"),
    [
        (
            "Over-the-shoulder developer workstation with two monitors showing "
            "readable source code and terminal output.",
            "risky_readable_surface",
            "hasNoReadableSurfaceVisuals",
        ),
        (
            "Two soft strands align in perfectly parallel rows, never crossing, "
            "with an exact split-screen layout.",
            "brittle_exact_geometry",
            "hasNoExactGeometryVisuals",
        ),
        (
            "At exactly 2 seconds the left orb must cross the right orb, then the "
            "camera slowly pushes in.",
            "brittle_mandatory_motion",
            "hasNoMandatoryMotionVisuals",
        ),
    ],
)
def test_release_video_visual_safety_reports_stable_categories(
    cue: str,
    category: str,
    check: str,
):
    release_video = load_release_video_module()

    artifacts = release_video.prepare_release_video_script(
        visual_safety_script(cue),
        source="test",
    )

    validation = artifacts["validation"]
    assert validation["checks"][check] is False
    assert check in validation["errors"]
    assert category in {
        finding["category"] for finding in validation["visualSafetyFindings"]
    }


def test_release_video_visual_safety_allows_safe_abstract_cues():
    release_video = load_release_video_module()
    script = visual_safety_script(
        "A text-free field of soft blue and violet light surrounds a simple matte orb.",
        "A translucent shield and rounded package cube rest in a diffuse color "
        "field; an optional gentle camera drift may be used.",
    )

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert artifacts["validation"]["visualSafetyFindings"] == []
    assert artifacts["validation"]["checks"]["hasNoReadableSurfaceVisuals"] is True
    assert artifacts["validation"]["checks"]["hasNoExactGeometryVisuals"] is True
    assert artifacts["validation"]["checks"]["hasNoMandatoryMotionVisuals"] is True
    assert artifacts["validation"]["errors"] == []


@pytest.mark.parametrize(
    "cue",
    [
        "Optional particles may appear; the camera must push in toward the orb.",
        "The orb can be blue while the camera pushes in toward it.",
        "An optional camera drift may be used; the camera must tilt down afterward.",
        "An optional camera must slowly pan toward the package cube.",
        "The orb can be blue as the camera pushes in toward it.",
        "Optional particles may appear near the orb before the camera pushes in.",
    ],
)
def test_release_video_visual_safety_scopes_camera_optionality_to_local_action(
    cue: str,
):
    release_video = load_release_video_module()

    categories = release_video.visual_safety_categories(cue)

    assert "brittle_mandatory_motion" in categories


@pytest.mark.parametrize(
    "cue",
    [
        "An IDE editor window with syntax-highlighted functions and a toolbar.",
        "A spreadsheet table with cells, column headers, and a data grid.",
        "A chart and graph with readable axes, captions, and subtitles.",
        "A generic application window with menus, a form, and UI controls.",
        "A browser window displays a readable web app screen.",
        "A graphical interface presents a table of status values and controls.",
    ],
)
def test_release_video_visual_safety_rejects_readable_interface_equivalents(
    cue: str,
):
    release_video = load_release_video_module()

    categories = release_video.visual_safety_categories(cue)

    assert "risky_readable_surface" in categories


@pytest.mark.parametrize(
    "cue",
    [
        "A slow camera tilt reveals the matte orb.",
        "The camera cranes upward and then rolls around the shield.",
        "Rack focus from the package cube to the orb.",
        "At the 2-second mark, one orb moves into the other.",
        "After 2 sec, the shield rotates around the package cube.",
        "At the two-second mark, one orb moves into the other.",
        "On frame 24, the package cube transforms into an orb.",
        "At second 3, the camera must pan toward the shield.",
        "At 0:02, the package cube moves into the shield.",
    ],
)
def test_release_video_visual_safety_rejects_common_mandatory_or_timed_motion(
    cue: str,
):
    release_video = load_release_video_module()

    categories = release_video.visual_safety_categories(cue)

    assert "brittle_mandatory_motion" in categories


@pytest.mark.parametrize(
    "cue",
    [
        "A static zoomed-out view of a matte orb in a soft blue field.",
        "An optional gentle camera transition may be used around the shield.",
        "A soft violet field surrounds a package cube; the camera may tilt gently.",
        "The view may gently pan across a soft blue field.",
        "An optional slow smooth push-in may be used around the matte orb.",
        "Soft ambient light forms a halo around a matte orb.",
        "A text-free abstract composition of matte cubes in diffuse blue light.",
    ],
)
def test_release_video_visual_safety_allows_static_or_optional_camera_wording(
    cue: str,
):
    release_video = load_release_video_module()

    categories = release_video.visual_safety_categories(cue)

    assert categories == []


@pytest.mark.parametrize("script_source", ["generated", "script-path"])
def test_release_video_rejects_unsafe_visual_before_pds_for_all_script_sources(
    tmp_path: Path,
    script_source: str,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    unsafe_script = visual_safety_script(
        "Show a terminal screen with exact readable command text and highlighted source code."
    )
    script_path = tmp_path / "unsafe-release-video.md"
    script_path.write_text(unsafe_script, encoding="utf8")
    source_args = (
        ["--script-path", str(script_path)]
        if script_source == "script-path"
        else ["--claude-cli", str(claude_output_stub(tmp_path, unsafe_script))]
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            *source_args,
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/unsafe"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    validation = json.loads(
        (
            tmp_path
            / "videos"
            / "v1.1.0"
            / "release_video_script_validation.json"
        ).read_text(encoding="utf8")
    )
    assert result.returncode == 1
    assert "PDS was not invoked" in result.stderr
    assert "hasNoReadableSurfaceVisuals" in validation["errors"]
    assert not capture.exists()


def pds_stub(tmp_path: Path, response: dict) -> Path:
    response_literal = repr(response)
    return write_executable(
        tmp_path / "pds-stub.py",
        f"""#!/usr/bin/env python3
import json
import os
import pathlib
import sys

capture = pathlib.Path(os.environ["PDS_STUB_CAPTURE"])
capture.write_text(json.dumps({{"argv": sys.argv[1:]}}, indent=2), encoding="utf8")
print(json.dumps({response_literal}))
""",
    )


def pds_output_stub(
    tmp_path: Path,
    *,
    stdout: str = "",
    stderr: str = "",
    exit_code: int = 0,
) -> Path:
    return write_executable(
        tmp_path / "pds-output-stub.py",
        f"""#!/usr/bin/env python3
import json
import os
import pathlib
import sys

capture = pathlib.Path(os.environ["PDS_STUB_CAPTURE"])
capture.write_text(json.dumps({{"argv": sys.argv[1:]}}, indent=2), encoding="utf8")
sys.stdout.write({stdout!r})
sys.stderr.write({stderr!r})
raise SystemExit({exit_code})
""",
    )


def pds_timeout_stub(
    tmp_path: Path,
    *,
    stdout: str = "",
    stderr: str = "",
) -> Path:
    return write_executable(
        tmp_path / "pds-timeout-stub.py",
        f"""#!/usr/bin/env python3
import json
import os
import pathlib
import sys
import time

capture = pathlib.Path(os.environ["PDS_STUB_CAPTURE"])
capture.write_text(json.dumps({{"argv": sys.argv[1:]}}, indent=2), encoding="utf8")
sys.stdout.write({stdout!r})
sys.stdout.flush()
sys.stderr.write({stderr!r})
sys.stderr.flush()
time.sleep(60)
""",
    )


def pds_version_stub(tmp_path: Path, version_output: str) -> Path:
    return write_executable(
        tmp_path / "pds-version-stub.py",
        f"""#!/usr/bin/env python3
import sys

sys.stdout.write({version_output!r})
""",
    )


def pds_idempotency_key(capture: Path) -> str:
    pds_call = pds_capture_argv(capture)
    return pds_call[pds_call.index("--idempotency-key") + 1]


def pds_capture_argv(capture: Path) -> list[str]:
    return json.loads(capture.read_text(encoding="utf8"))["argv"]


def assert_audit_fix_policy_args(argv: list[str]) -> None:
    """Assert the release wrapper's bounded audit-repair policy argv."""
    expected = (
        ("--audit-fix-max-passes", "2"),
        ("--audit-fix-max-annotations-per-pass", "3"),
        ("--audit-fix-max-spend-pddc", "24"),
        ("--audit-fix-source-approval", "not-required"),
    )
    for flag, value in expected:
        assert argv[argv.index(flag) + 1] == value


def run_release_video_with_existing_script(
    tmp_path: Path,
    *,
    extra_args: list[str] | None = None,
    env_extra: dict | None = None,
) -> tuple[subprocess.CompletedProcess[str], Path]:
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    env = release_video_env(
        {
            "PDS_STUB_CAPTURE": str(capture),
            **(env_extra or {}),
        }
    )
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {
                        "ok": True,
                        "summary": {"youtubeUrl": "https://youtu.be/recovery"},
                    },
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
            *(extra_args or []),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )
    return result, capture


def test_release_video_existing_script_forwards_bounded_audit_fix_policy(
    tmp_path: Path,
):
    _, capture = run_release_video_with_existing_script(tmp_path)

    pds_call = pds_capture_argv(capture)

    assert pds_call[:2] == ["release-video", "create"]
    assert_audit_fix_policy_args(pds_call)


def test_release_video_generates_script_and_invokes_pds_publish(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})
    pds = pds_stub(
        tmp_path,
        {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/pdd-release"}},
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--claude-cli",
            str(claude_stub(tmp_path)),
            "--pds-cli",
            str(pds),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    assert "https://youtu.be/pdd-release" in result.stdout
    output_dir = tmp_path / "videos" / "v1.1.0"
    script_text = (output_dir / "release_video_script.md").read_text(encoding="utf8")
    assert script_text.startswith("# PDD v1.1.0 Release Video")
    assert "\n## Release Overview (0:00 - 1:00)" in script_text
    assert "\nNARRATOR:\n" in script_text
    assert "\nvisual: a text-free matte package cube" in script_text.lower()
    claude_prompt = (repo / "claude_prompt.txt").read_text(encoding="utf8")
    assert "Research requirement:" in claude_prompt
    assert "Business-value requirements:" in claude_prompt
    assert "Visual requirements:" in claude_prompt
    assert "what changed, why it matters, and the practical business value" in claude_prompt
    assert "## Release hook (0:00 - 0:12)" in claude_prompt
    assert "Every spoken narration block starts with `NARRATOR:` on its own line." in claude_prompt
    assert (
        "Every non-spoken visual cue is written on one line as `VISUAL: <cue text>`."
        in claude_prompt
    )
    assert "Default to transform-safe, text-free abstract visuals" in claude_prompt
    assert "Do not request monitors, screens, terminals" in claude_prompt
    assert "Do not require exact geometry or layout" in claude_prompt
    assert "Camera direction must be optional and transform-safe" in claude_prompt
    assert "release video automation" in claude_prompt
    claude_argv = json.loads((repo / "claude_argv.json").read_text(encoding="utf8"))
    assert claude_argv[claude_argv.index("--model") + 1] == "claude-opus-4-8"
    assert "--allowedTools" not in claude_argv
    pds_call = json.loads(capture.read_text(encoding="utf8"))["argv"]
    assert pds_call[:2] == ["release-video", "create"]
    assert pds_call[pds_call.index("--target") + 1] == "publish"
    assert pds_call[pds_call.index("--platform") + 1] == "youtube"
    assert pds_call[pds_call.index("--privacy") + 1] == "unlisted"
    assert pds_call[pds_call.index("--release-tag") + 1] == "v1.1.0"
    assert pds_call[pds_call.index("--repo-name") + 1] == "promptdriven/pdd"
    assert pds_call[pds_call.index("--claude-model") + 1] == "glm-5.2"
    assert_audit_fix_policy_args(pds_call)
    idempotency_key = pds_call[pds_call.index("--idempotency-key") + 1]
    assert idempotency_key.startswith("pdd-release-video:v1.1.0:")


def test_release_video_rejects_explicit_empty_claude_model_before_claude(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--claude-model",
            "   ",
            "--claude-cli",
            str(claude_stub(tmp_path)),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {
                        "ok": True,
                        "summary": {"youtubeUrl": "https://youtu.be/pdd-release"},
                    },
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    assert "Claude Code script-generation model must not be empty" in result.stderr
    assert not (repo / "claude_argv.json").exists()
    assert not capture.exists()


def test_release_video_sanitizes_generated_script_before_invoking_pds(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    raw_script = """Here is the release video script you asked for:

# PDD v1.1.0 Release Video

## Opening

NARRATOR:
NARRATOR:
PDD v1.1.0 turns the release notes into a short operator-ready video story that tells maintainers what shipped, why it matters, and how the release path changed.

VISUAL: a text-free matte package cube rests in a soft blue and violet light field.

## Reliability

NARRATOR: NARRATOR: The release path now keeps generated assets, PDS run state, and publishing evidence together so recovery work can continue without guessing which artifact was sent downstream.

VISUAL: a translucent shield surrounds a rounded orb in a diffuse color field.

Let me know if you want a punchier version.
"""
    pds = pds_stub(
        tmp_path,
        {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/sanitized"}},
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--claude-cli",
            str(claude_output_stub(tmp_path, raw_script)),
            "--pds-cli",
            str(pds),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    assert "https://youtu.be/sanitized" in result.stdout
    output_dir = tmp_path / "videos" / "v1.1.0"
    raw_artifact = (output_dir / "release_video_script.raw.md").read_text(encoding="utf8")
    script_text = (output_dir / "release_video_script.md").read_text(encoding="utf8")
    validation = json.loads(
        (output_dir / "release_video_script_validation.json").read_text(encoding="utf8")
    )
    pds_call = pds_capture_argv(capture)
    sent_script = Path(pds_call[pds_call.index("--script") + 1]).read_text(encoding="utf8")

    assert "Here is the release video script" in raw_artifact
    assert "Here is the release video script" not in script_text
    assert "Let me know if you want" not in script_text
    assert "NARRATOR: NARRATOR:" not in script_text
    assert "\nNARRATOR:\n\nNARRATOR:\n" not in script_text
    assert sent_script == script_text
    assert validation["normalized"] is True
    assert "stripped_model_wrapper_text" in validation["changes"]
    assert "collapsed_duplicate_narrator_labels" in validation["changes"]
    assert validation["checks"]["hasNoModelWrapperText"] is True
    assert validation["checks"]["hasNoDuplicateNarratorLabels"] is True
    assert validation["errors"] == []


def test_release_video_normalizes_label_only_visual_blocks():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 makes release-video recovery easier to audit by preserving the
generated script, the normalized script, and the validation evidence before
the PDS create step receives anything.

VISUAL:

a text-free matte cube and translucent shield rest in a diffuse violet field with a soft ambient light pulse.

## Recovery

NARRATOR:
Operators can compare the raw model output with the final script and quickly
see which sanitation steps ran, which reduces guesswork during release
recovery and keeps publishing diagnostics reproducible.

VISUAL:
a rounded orb rests in a soft blue field; an optional gentle camera drift may be used.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "\nVISUAL:\n" not in artifacts["script"]
    assert (
        "\nVISUAL: a text-free matte cube and translucent shield"
        in artifacts["script"]
    )
    assert "\nVISUAL: a rounded orb rests in a soft blue field" in artifacts["script"]
    assert artifacts["validation"]["checks"]["hasVisual"] is True
    assert "collapsed_label_only_visual_cues" in artifacts["validation"]["changes"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_normalizes_wrapped_label_only_visual_cue_paragraph():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 keeps release-video recovery auditable by preserving the raw model
output, normalized script, validation JSON, and PDS run state before the
publish command can hand the script to downstream video generation.

VISUAL:
a matte package cube rests beneath a translucent shield in a soft blue field;
an optional gentle camera drift may be used while a diffuse light pulse
brightens the background.

## Recovery

NARRATOR:
The normalized script must keep the entire visual direction together so the
video generator receives one complete storyboard cue instead of dropping the
wrapped continuation text.

VISUAL: a rounded orb rests in a text-free violet field.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert (
        "\nVISUAL: a matte package cube rests beneath a translucent shield in a "
        "soft blue field; an optional gentle camera drift may be used while a "
        "diffuse light pulse brightens the background."
        in artifacts["script"]
    )
    assert "\nan optional gentle camera drift" not in artifacts["script"]
    assert "\nbrightens the background" not in artifacts["script"]
    assert artifacts["validation"]["checks"]["hasVisual"] is True
    assert artifacts["validation"]["errors"] == []


def test_release_video_normalizes_wrapped_same_line_visual_cue_continuation():
    release_video = load_release_video_module()
    script = """Hook: PDD v1.1.0 turns release-video recovery into an operator-visible
path instead of a best-effort publish step that can fail without enough context.

Narration: The release wrapper now keeps generated scripts, validation evidence,
PDS run handles, status query diagnostics, and recovery commands together before
the publish request reaches PDS. Maintainers can reattach to the same run, see
whether a running sidecar is stale, and retry with a stable idempotency key
without regenerating the release story or losing the incident trail.

Visual direction: a text-free matte cube rests beneath a translucent shield
in a soft blue field with a diffuse ambient light pulse.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert (
        "\nVISUAL: a text-free matte cube rests beneath a translucent shield "
        "in a soft blue field with a diffuse ambient light pulse."
        in artifacts["script"]
    )
    assert "\nNARRATOR:\nin a soft blue field" not in artifacts["script"]
    assert "collapsed_wrapped_visual_cues" in artifacts["validation"]["changes"]
    assert artifacts["validation"]["checks"]["hasVisual"] is True
    assert artifacts["validation"]["errors"] == []


def test_release_video_validation_rejects_leftover_label_only_visual_cues():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
The release-video wrapper must not let empty storyboard labels reach PDS just
because a later scene contains one valid visual cue. Empty visual labels can
become blank scenes or parser failures downstream, so validation has to keep
the normalized script contract strict before create runs.

VISUAL:

## Recovery

NARRATOR:
The recovery workflow still includes enough narration and a concrete valid
visual later in the script to satisfy all other validation checks, isolating
the failure to the leftover label-only visual cue.

VISUAL: a text-free matte cube rests in a soft amber field.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "\nVISUAL:\n" in artifacts["script"]
    assert artifacts["validation"]["checks"]["hasVisual"] is True
    assert artifacts["validation"]["checks"]["hasNoLabelOnlyVisualCues"] is False
    assert "hasNoLabelOnlyVisualCues" in artifacts["validation"]["errors"]


def test_release_video_does_not_swallow_unsafe_label_only_visual_blocks():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
The wrapper must avoid converting structural lines or wrapper prose into visual
cues when a model emits an empty visual label without useful cue text after it.

VISUAL:

## Recovery

VISUAL:

NARRATOR:
This narration remains a narrator block instead of becoming a visual cue,
because the line after the empty visual label is another script label.

VISUAL:

Here is the release video script you asked for:

VISUAL:

a translucent shield surrounds a matte package cube in a diffuse blue field
with a soft ambient light pulse.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "\nVISUAL: ## Recovery" not in artifacts["script"]
    assert "\nVISUAL: NARRATOR:" not in artifacts["script"]
    assert "\nVISUAL: Here is the release video script" not in artifacts["script"]
    assert (
        "\nVISUAL: a translucent shield surrounds a matte package cube"
        in artifacts["script"]
    )
    assert artifacts["validation"]["checks"]["hasVisual"] is True
    assert artifacts["validation"]["checks"]["hasNoModelWrapperText"] is False


def test_release_video_preserves_exact_raw_claude_output_artifact(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    raw_script = """```markdown
# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 keeps exact raw script diagnostics while sending a normalized script
to PDS, so release recovery can compare the generated content with the content
that downstream systems received.

VISUAL: a text-free matte cube and translucent shield rest in a soft blue field.

## Recovery

NARRATOR:
Operators can inspect the raw Claude output, the final script, and validation
metadata without guessing which transformation happened before PDS create.

VISUAL: a rounded orb rests in a diffuse violet field.
```
"""

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--claude-cli",
            str(claude_output_stub(tmp_path, raw_script)),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/raw"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    output_dir = tmp_path / "videos" / "v1.1.0"
    assert (output_dir / "release_video_script.raw.md").read_text(encoding="utf8") == raw_script
    normalized = (output_dir / "release_video_script.md").read_text(encoding="utf8")
    assert not normalized.startswith("```")
    assert "PDD v1.1.0 keeps exact raw script diagnostics" in normalized


def test_release_video_strips_wrapped_markdown_fence_from_final_script():
    release_video = load_release_video_module()
    script = """Here is the release video script:

```markdown
# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 keeps release-video recovery visible with durable scripts, status
metadata, and validation evidence that helps maintainers recover failed
publishes without guessing.

VISUAL: a text-free matte cube rests in a soft blue field.

## Close

NARRATOR:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: a translucent shield surrounds a rounded orb in a diffuse violet field.
```

Let me know if you want a shorter version.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "```" not in artifacts["script"]
    assert "Here is the release video script" not in artifacts["script"]
    assert "Let me know if you want" not in artifacts["script"]
    assert artifacts["validation"]["checks"]["hasNoMarkdownFences"] is True
    assert artifacts["validation"]["errors"] == []


def test_release_video_rejects_mid_document_model_wrapper_text():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 keeps release-video recovery visible with durable scripts, status
metadata, and validation evidence that helps maintainers recover failed
publishes without guessing.

VISUAL: a text-free matte cube rests in a soft blue field.

Sure, here is the next section of the release-video script:

## Close

NARRATOR:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: a translucent shield surrounds a rounded orb in a diffuse violet field.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert artifacts["validation"]["checks"]["hasNoModelWrapperText"] is False
    assert "hasNoModelWrapperText" in artifacts["validation"]["errors"]


def test_release_video_strips_common_assistant_preamble():
    release_video = load_release_video_module()
    script = """Below is the release video script you requested:

# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 keeps release-video recovery visible with durable scripts, status
metadata, and validation evidence that helps maintainers recover failed
publishes without guessing.

VISUAL: a text-free matte cube rests in a soft blue field.

## Close

NARRATOR:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: a translucent shield surrounds a rounded orb in a diffuse violet field.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Below is the release video script" not in artifacts["script"]
    assert artifacts["validation"]["changes"] == ["stripped_model_wrapper_text"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_strips_additional_assistant_preamble_variants():
    release_video = load_release_video_module()
    preambles = [
        "I've drafted the release video script below:",
        "I drafted the release video script below:",
        "I prepared the release video script below:",
        "I created the release video script below:",
        "I wrote the release video script below:",
        "Absolutely, here's the release video script:",
        "Here\u2019s the release video script:",
        "Below you'll find the release video script:",
    ]

    for preamble in preambles:
        script = f"""{preamble}

# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 keeps release-video recovery visible with durable scripts, status
metadata, and validation evidence that helps maintainers recover failed
publishes without guessing.

VISUAL: a text-free matte cube rests in a soft blue field.

## Close

NARRATOR:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: a translucent shield surrounds a rounded orb in a diffuse violet field.
"""

        artifacts = release_video.prepare_release_video_script(script, source="test")

        assert preamble not in artifacts["script"]
        assert "stripped_model_wrapper_text" in artifacts["validation"]["changes"]
        assert artifacts["validation"]["errors"] == []


def test_release_video_rejects_wrapper_text_inside_narrator_block():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 keeps release-video recovery visible with durable scripts, status
metadata, and validation evidence that helps maintainers recover failed
publishes without guessing.

VISUAL: a text-free matte cube rests in a soft blue field.

## Close

NARRATOR:
Sure, here is the next section of the release-video script:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: a translucent shield surrounds a rounded orb in a diffuse violet field.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert artifacts["validation"]["checks"]["hasNoModelWrapperText"] is False
    assert "hasNoModelWrapperText" in artifacts["validation"]["errors"]


def test_release_video_preserves_valid_here_is_narration_line():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
Here is the command maintainers run after tagging a release, and the reason it
matters for recovery: the release-video wrapper keeps PDS status, scripts, and
validation evidence together.

VISUAL: a text-free package cube rests beneath a soft ambient light pulse.

## Close

NARRATOR:
The recovery artifacts stay readable and complete, so operators can reattach to
the release run without depending on stale local profile state.

VISUAL: a translucent shield rests in a diffuse blue field.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Here is the command maintainers run" in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_preserves_trailing_here_is_narration_line():
    release_video = load_release_video_module()
    script = "\n".join(
        [
            "# PDD v1.1.0 Release Video",
            "",
            "## Opening",
            "",
            "NARRATOR:",
            "PDD v1.1.0 keeps release recovery visible with durable scripts and",
            "status evidence for maintainers who need to debug failed video publishes.",
            "",
            "VISUAL: a text-free matte cube rests in a soft blue field.",
            "",
            "## Close",
            "",
            "NARRATOR:",
            (
                "Here is the takeaway: v1.1.0 gives maintainers a recoverable "
                "release-video path with clear artifacts and durable PDS status."
            ),
        ]
    )

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Here is the takeaway" in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_preserves_blank_after_label_trailing_here_is_narration():
    release_video = load_release_video_module()
    script = "\n".join(
        [
            "# PDD v1.1.0 Release Video",
            "",
            "## Opening",
            "",
            "NARRATOR:",
            "PDD v1.1.0 keeps release recovery visible with durable scripts and",
            "status evidence for maintainers who need to debug failed video publishes.",
            "",
            "VISUAL: a text-free matte cube rests in a soft blue field.",
            "",
            "## Close",
            "",
            "NARRATOR:",
            "",
            (
                "Here is the takeaway: v1.1.0 gives maintainers a recoverable "
                "release-video path with clear artifacts, validation evidence, "
                "and durable PDS status."
            ),
        ]
    )

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Here is the takeaway" in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_preserves_multiparagraph_trailing_here_is_narration():
    release_video = load_release_video_module()
    script = "\n".join(
        [
            "# PDD v1.1.0 Release Video",
            "",
            "## Opening",
            "",
            "NARRATOR:",
            "PDD v1.1.0 keeps release recovery visible with durable scripts and",
            "status evidence for maintainers who need to debug failed video publishes.",
            "",
            "VISUAL: a text-free matte cube rests in a soft blue field.",
            "",
            "## Close",
            "",
            "NARRATOR:",
            "The closing paragraph summarizes the publish recovery path and why the",
            "generated assets matter to maintainers during a release incident.",
            "",
            (
                "Here is the takeaway: v1.1.0 gives maintainers a recoverable "
                "release-video path with clear artifacts, validation evidence, "
                "and durable PDS status after a failed PDS publish."
            ),
        ]
    )

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "The closing paragraph summarizes" in artifacts["script"]
    assert "Here is the takeaway" in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_preserves_plain_narration_before_first_visual():
    release_video = load_release_video_module()
    script = """Hook: PDD v1.1.0 turns release-video recovery into an operator-visible
path instead of a best-effort publish step that can fail without enough context.

Narration: The release wrapper now keeps generated scripts, validation evidence,
PDS run handles, status query diagnostics, and recovery commands together before
the publish request reaches PDS. Maintainers can reattach to the same run, see
whether a running sidecar is stale, and retry with a stable idempotency key
without regenerating the release story or losing the incident trail.

Visual direction: a text-free matte package cube rests beneath a translucent
shield in a diffuse blue field with a soft ambient light pulse.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Hook: PDD v1.1.0 turns release-video recovery" in artifacts["script"]
    assert "Narration: The release wrapper now keeps generated scripts" in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_preserves_plain_preamble_before_first_narrator_label():
    release_video = load_release_video_module()
    script = """Hook: PDD v1.1.0 makes release-video recovery explicit for
maintainers before the first formal narrator block appears.

NARRATOR:
The release-video workflow now preserves enough diagnostics for operators to
recover a failed publish without guessing. Generated scripts, validation
evidence, PDS run handles, and status query diagnostics stay attached to the
release attempt so maintainers can continue recovery with a stable audit trail.

VISUAL: a text-free matte cube and shield rest in a diffuse blue field.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Hook: PDD v1.1.0 makes release-video recovery explicit" in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_strips_final_assistant_footer_after_narrator_block():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
PDD v1.1.0 keeps release recovery visible with durable scripts and status
evidence for maintainers who need to debug failed video publishes.

VISUAL: a text-free rounded orb rests in a soft violet field.

## Close

NARRATOR:
The closing paragraph summarizes the publish recovery path and why generated
assets matter to maintainers during a release incident.

Let me know if you want a punchier version.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "The closing paragraph summarizes" in artifacts["script"]
    assert "Let me know if you want" not in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_collapses_empty_duplicate_narrator_label():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
NARRATOR: NARRATOR:
The wrapper should collapse duplicate speaker labels even when the duplicated
label line has no narration body, because the final script is what PDS receives
for section specification and rendering.

VISUAL: a matte package cube rests in a diffuse blue field.

## Recovery

NARRATOR:
The validation artifact records the normalization and the script stays free of
duplicated speaker labels before the create command runs.

VISUAL: a translucent shield surrounds a rounded orb.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "NARRATOR: NARRATOR:" not in artifacts["script"]
    assert "collapsed_duplicate_narrator_labels" in artifacts["validation"]["changes"]
    assert artifacts["validation"]["checks"]["hasNoDuplicateNarratorLabels"] is True
    assert artifacts["validation"]["errors"] == []


def test_release_video_collapses_many_duplicate_narrator_labels():
    release_video = load_release_video_module()
    duplicated_labels = "NARRATOR:" + "\tNARRATOR:" * 40
    script = f"""# PDD v1.1.0 Release Video

## Opening

{duplicated_labels}
The wrapper should collapse a long repeated speaker-label run without relying
on a backtracking-heavy regular expression, because generated scripts can echo
speaker labels many times after a model formatting failure.

VISUAL: a matte cube rests beneath a soft ambient light pulse.

## Recovery

NARRATOR:
The final script remains readable, validation stays clean, and PDS receives one
stable narrator block instead of repeated labels.

VISUAL: a translucent shield rests in a diffuse violet field.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "\tNARRATOR:" not in artifacts["script"]
    assert "collapsed_duplicate_narrator_labels" in artifacts["validation"]["changes"]
    assert artifacts["validation"]["checks"]["hasNoDuplicateNarratorLabels"] is True
    assert artifacts["validation"]["errors"] == []


def test_release_video_normalizes_standalone_bold_narrator_labels():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

**NARRATOR:**
Opening narration should follow the narrator label without an extra markdown
marker in the spoken body, because generated scripts sometimes bold speaker
labels while keeping them on their own line.

VISUAL: a text-free package cube rests in a soft blue field.

## Close

**NARRATOR:**
The workflow stores raw output, normalized narration, and validation evidence
before publish, keeping the release story auditable through recovery.

VISUAL: a translucent shield surrounds a matte orb.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Opening narration should follow the narrator label" in artifacts["script"]
    assert "\n**\n" not in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_normalizes_spaced_standalone_bold_narrator_labels():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

**NARRATOR: **
Opening narration should follow the narrator label without a literal markdown
marker in the spoken body, even when generated scripts put whitespace before
the closing bold marker.

VISUAL: a text-free package cube rests in a soft blue field.

## Close

**NARRATOR: **
The workflow stores raw output, normalized narration, and validation evidence
before publish, keeping the release story auditable through recovery.

VISUAL: a translucent shield surrounds a matte orb.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Opening narration should follow the narrator label" in artifacts["script"]
    assert "\n**\n" not in artifacts["script"]
    assert "\n** The workflow" not in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_preserves_wrapped_script_with_bold_narrator_labels():
    release_video = load_release_video_module()
    script = """Here is the release video script you asked for:

**NARRATOR:**
Opening narration should be preserved because it explains the release value and
recovery path for maintainers before the first visual direction appears.

VISUAL: a text-free package cube rests in a soft blue field.

**NARRATOR:**
The workflow stores raw output, normalized narration, and validation evidence
before publish, keeping the release story auditable through recovery.

VISUAL: a translucent shield surrounds a matte orb.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "Here is the release video script" not in artifacts["script"]
    assert "Opening narration should be preserved" in artifacts["script"]
    assert "\n**\n" not in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_normalizes_spaced_inline_bold_narrator_labels():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

**NARRATOR: ** PDD v1.1.0 turns release-video recovery into a visible operator
path, with generated scripts, validation artifacts, and PDS run metadata
preserved before the publish step is allowed to continue.

VISUAL: a text-free matte cube rests in a diffuse violet field.

## Recovery

**NARRATOR: ** The wrapper keeps narration labels out of the spoken body while
still providing the standalone narrator blocks PDS expects for scene generation
and video rendering.

VISUAL: a translucent shield surrounds a rounded orb in soft light.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "\nNARRATOR:\nPDD v1.1.0 turns release-video recovery" in artifacts["script"]
    assert "\n** PDD v1.1.0 turns release-video recovery" not in artifacts["script"]
    assert "\n** The wrapper keeps narration labels" not in artifacts["script"]
    assert artifacts["validation"]["errors"] == []


def test_release_video_normalizes_inline_narrator_labels():
    release_video = load_release_video_module()
    script = """# PDD v1.1.0 Release Video

## Opening

NARRATOR: PDD v1.1.0 turns release-video recovery into a visible operator path,
with generated scripts, validation artifacts, and PDS run metadata preserved
before the publish step is allowed to continue.

VISUAL: a text-free matte cube rests in a diffuse violet field.

## Recovery

NARRATOR: The wrapper keeps narration labels out of the spoken body while still
providing the standalone narrator blocks PDS expects for scene generation and
video rendering.

VISUAL: a translucent shield surrounds a rounded orb in soft light.
"""

    artifacts = release_video.prepare_release_video_script(script, source="test")

    assert "\nNARRATOR:\nPDD v1.1.0 turns release-video recovery" in artifacts["script"]
    assert "\nNARRATOR: PDD v1.1.0 turns release-video recovery" not in artifacts["script"]
    assert "\nNARRATOR: The wrapper keeps narration labels" not in artifacts["script"]
    assert "collapsed_duplicate_narrator_labels" in artifacts["validation"]["changes"]
    assert artifacts["validation"]["checks"]["hasNoDuplicateNarratorLabels"] is True
    assert artifacts["validation"]["errors"] == []


def test_release_video_rejects_malformed_script_before_invoking_pds(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    malformed_script = tmp_path / "malformed_release_video_script.md"
    malformed_script.write_text(
        """# PDD v1.1.0 Release Video

## Opening

NARRATOR:
This script is long enough to pass the old length check, but it never gives PDS
any visual direction. That means the wrapper should stop before create rather
than handing downstream systems an ambiguous narration-only artifact that an
operator must diagnose during release recovery.

## Details

NARRATOR:
The second section repeats the same problem with more words so the script
remains realistic, but it still lacks any visual cue or storyboard line. The
release-video wrapper must explain the missing contract field and keep
diagnostics on disk.
""",
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(malformed_script),
            "--pds-cli",
            str(pds_stub(tmp_path, {"ok": True})),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    assert "release-video script validation failed" in result.stderr
    assert not capture.exists()
    validation = json.loads(
        (output_dir / "v1.1.0" / "release_video_script_validation.json").read_text(
            encoding="utf8"
        )
    )
    assert validation["checks"]["hasVisual"] is False
    assert "hasVisual" in validation["errors"]


def test_release_video_default_idempotency_key_uses_tag_and_git_sha(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})
    pds = pds_stub(
        tmp_path,
        {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/default-key"}},
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(pds),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    assert pds_idempotency_key(capture) == "pdd-release-video:v1.1.0:abc123def456:local"


def test_release_video_release_notes_path_reuses_original_artifact(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_release_notes = tmp_path / "existing_release_notes.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    original_notes = "## Commits\n\n- Preserve the exact retry release notes.\n"
    existing_release_notes.write_text(original_notes, encoding="utf8")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--release-notes-path",
            str(existing_release_notes),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/retry"}},
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 0, result.stderr
    preserved_notes = output_dir / "v1.1.0" / "release_notes.md"
    assert preserved_notes.read_text(encoding="utf8") == original_notes
    pds_call = pds_capture_argv(capture)
    assert pds_call[pds_call.index("--release-notes") + 1] == str(preserved_notes)


def test_release_video_default_idempotency_key_separates_local_and_ci_provenance(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")

    local_capture = tmp_path / "local-pds-capture.json"
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/local"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "local-videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(local_capture)}),
        check=True,
    )

    ci_capture = tmp_path / "ci-pds-capture.json"
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/ci"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "ci-videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env(
            {"PDS_STUB_CAPTURE": str(ci_capture), "GITHUB_ACTIONS": "true"}
        ),
        check=True,
    )

    assert pds_idempotency_key(local_capture) == (
        "pdd-release-video:v1.1.0:abc123def456:local"
    )
    assert pds_idempotency_key(ci_capture) == (
        "pdd-release-video:v1.1.0:abc123def456:github-actions"
    )


def test_release_video_falsey_ci_env_uses_local_idempotency_provenance(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")

    for falsey_value in ("false", "0", "no", "off"):
        capture = tmp_path / f"pds-capture-{falsey_value}.json"
        subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--repo",
                str(repo),
                "--tag",
                "v1.1.0",
                "--git-sha",
                "abc123def456",
                "--script-path",
                str(existing_script),
                "--pds-cli",
                str(
                    pds_stub(
                        tmp_path,
                        {
                            "ok": True,
                            "summary": {"youtubeUrl": f"https://youtu.be/{falsey_value}"},
                        },
                    )
                ),
                "--output-dir",
                str(tmp_path / f"videos-{falsey_value}"),
            ],
            cwd=repo,
            text=True,
            capture_output=True,
            env=release_video_env({"PDS_STUB_CAPTURE": str(capture), "CI": falsey_value}),
            check=True,
        )

        assert pds_idempotency_key(capture) == (
            "pdd-release-video:v1.1.0:abc123def456:local"
        )


def test_release_video_env_full_idempotency_key_overrides_default(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    env = release_video_env(
        {
            "PDS_STUB_CAPTURE": str(capture),
            "RELEASE_VIDEO_IDEMPOTENCY_KEY": "manual-release-video-key",
        }
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/env-key"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    assert pds_idempotency_key(capture) == "manual-release-video-key"


def test_release_video_attempt_id_adds_retry_suffix(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/retry"}},
                )
            ),
            "--idempotency-attempt-id",
            "20260620-001",
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    assert (
        pds_idempotency_key(capture)
        == "pdd-release-video:v1.1.0:abc123def456:local:retry-20260620-001"
    )


def test_release_video_env_attempt_id_adds_retry_suffix(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    env = release_video_env(
        {
            "PDS_STUB_CAPTURE": str(capture),
            "RELEASE_VIDEO_ATTEMPT_ID": "ops-retry",
        }
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/env-retry"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    assert (
        pds_idempotency_key(capture)
        == "pdd-release-video:v1.1.0:abc123def456:local:retry-ops-retry"
    )


def test_release_video_fails_when_full_key_and_attempt_id_are_both_supplied(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/conflict"}},
                )
            ),
            "--idempotency-key",
            "manual-release-video-key",
            "--idempotency-attempt-id",
            "ops-retry",
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )

    assert result.returncode == 1
    assert (
        "Use either a full release-video idempotency key or an attempt id, not both."
        in result.stderr
    )
    assert not capture.exists()


def test_release_video_idempotency_conflict_fails_before_claude_generation(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--claude-cli",
            str(tmp_path / "missing-claude"),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/conflict"}},
                )
            ),
            "--idempotency-key",
            "manual-release-video-key",
            "--idempotency-attempt-id",
            "ops-retry",
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )

    assert result.returncode == 1
    assert (
        "Use either a full release-video idempotency key or an attempt id, not both."
        in result.stderr
    )
    assert "Claude CLI" not in result.stderr
    assert not (repo / "claude_prompt.txt").exists()
    assert not capture.exists()


def test_release_video_cli_can_bootstrap_selected_project(tmp_path: Path):
    _result, capture = run_release_video_with_existing_script(
        tmp_path,
        extra_args=["--bootstrap-selected-project"],
    )

    assert "--bootstrap-selected-project" in pds_capture_argv(capture)


def test_release_video_env_can_bootstrap_selected_project(tmp_path: Path):
    _result, capture = run_release_video_with_existing_script(
        tmp_path,
        env_extra={"RELEASE_VIDEO_BOOTSTRAP_SELECTED_PROJECT": "1"},
    )

    assert "--bootstrap-selected-project" in pds_capture_argv(capture)


def test_release_video_cli_can_force_regenerate(tmp_path: Path):
    _result, capture = run_release_video_with_existing_script(
        tmp_path,
        extra_args=["--force-regenerate"],
    )

    assert "--force-regenerate" in pds_capture_argv(capture)


def test_release_video_env_can_force_regenerate(tmp_path: Path):
    _result, capture = run_release_video_with_existing_script(
        tmp_path,
        env_extra={"RELEASE_VIDEO_FORCE_REGENERATE": "1"},
    )

    assert "--force-regenerate" in pds_capture_argv(capture)


def test_release_video_cli_can_set_metadata_conflict_use_existing(tmp_path: Path):
    _result, capture = run_release_video_with_existing_script(
        tmp_path,
        extra_args=["--metadata-conflict", "use-existing"],
    )

    pds_call = pds_capture_argv(capture)
    assert pds_call[pds_call.index("--metadata-conflict") + 1] == "use-existing"


def test_release_video_env_can_set_metadata_conflict_replace_with_force(
    tmp_path: Path,
):
    _result, capture = run_release_video_with_existing_script(
        tmp_path,
        env_extra={
            "RELEASE_VIDEO_METADATA_CONFLICT": "replace",
            "RELEASE_VIDEO_FORCE_REGENERATE": "1",
        },
    )

    pds_call = pds_capture_argv(capture)
    assert pds_call[pds_call.index("--metadata-conflict") + 1] == "replace"
    assert "--force-regenerate" in pds_call


def test_release_video_metadata_conflict_replace_requires_force_regenerate(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/recovery"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
            "--metadata-conflict",
            "replace",
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    assert (
        "--metadata-conflict replace requires --force-regenerate"
        in result.stderr
    )
    assert not capture.exists()


def test_release_video_recovery_flags_default_to_disabled(tmp_path: Path):
    _result, capture = run_release_video_with_existing_script(tmp_path)

    pds_call = pds_capture_argv(capture)
    assert "--bootstrap-selected-project" not in pds_call
    assert "--force-regenerate" not in pds_call
    assert "--metadata-conflict" not in pds_call


def test_release_video_empty_pds_claude_model_omits_downstream_override(
    tmp_path: Path,
):
    _result, capture = run_release_video_with_existing_script(
        tmp_path,
        extra_args=["--pds-claude-model", "   "],
    )

    pds_call = pds_capture_argv(capture)
    assert "--claude-model" not in pds_call


def test_release_video_makefile_passes_idempotency_env_vars():
    makefile_text = (ROOT / "Makefile").read_text(encoding="utf8")

    assert "RELEASE_VIDEO_IDEMPOTENCY_KEY ?=" in makefile_text
    assert "RELEASE_VIDEO_IDEMPOTENCY_PROVENANCE ?=" in makefile_text
    assert "RELEASE_VIDEO_ATTEMPT_ID ?=" in makefile_text
    assert (
        'RELEASE_VIDEO_IDEMPOTENCY_KEY="$(RELEASE_VIDEO_IDEMPOTENCY_KEY)"'
        in makefile_text
    )
    assert (
        'RELEASE_VIDEO_IDEMPOTENCY_PROVENANCE='
        '"$(RELEASE_VIDEO_IDEMPOTENCY_PROVENANCE)"'
        in makefile_text
    )
    assert (
        'RELEASE_VIDEO_ATTEMPT_ID="$(RELEASE_VIDEO_ATTEMPT_ID)"'
        in makefile_text
    )


def test_release_video_makefile_passes_recovery_env_vars():
    makefile_text = (ROOT / "Makefile").read_text(encoding="utf8")

    assert "RELEASE_VIDEO_BOOTSTRAP_SELECTED_PROJECT ?= 0" in makefile_text
    assert "RELEASE_VIDEO_FORCE_REGENERATE ?= 0" in makefile_text
    assert "RELEASE_VIDEO_METADATA_CONFLICT ?=" in makefile_text
    assert (
        'RELEASE_VIDEO_BOOTSTRAP_SELECTED_PROJECT="$(RELEASE_VIDEO_BOOTSTRAP_SELECTED_PROJECT)"'
        in makefile_text
    )
    assert (
        'RELEASE_VIDEO_FORCE_REGENERATE="$(RELEASE_VIDEO_FORCE_REGENERATE)"'
        in makefile_text
    )
    assert (
        'RELEASE_VIDEO_METADATA_CONFLICT="$(RELEASE_VIDEO_METADATA_CONFLICT)"'
        in makefile_text
    )


def test_release_video_makefile_pds_cli_default_avoids_stale_global_cli():
    makefile_text = (ROOT / "Makefile").read_text(encoding="utf8")

    assert (
        "PDS_CLI ?= npx -y @promptdriven/pds@0.1.11 --timeout 120s"
        in makefile_text
    )


def test_release_video_makefile_passes_local_claude_model_default():
    makefile_text = (ROOT / "Makefile").read_text(encoding="utf8")

    release_video = subprocess.run(
        ["make", "-n", "release-video", "RELEASE_TAG=v1.1.0"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    preflight = subprocess.run(
        ["make", "-n", "check-release-video-config"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )

    assert "RELEASE_VIDEO_CLAUDE_MODEL ?= claude-opus-4-8" in makefile_text
    assert '--claude-model "$(RELEASE_VIDEO_CLAUDE_MODEL)"' in makefile_text
    assert '--claude-model "claude-opus-4-8"' in release_video.stdout
    assert '--claude-model "claude-opus-4-8"' in preflight.stdout


def test_release_video_makefile_empty_local_defaults_are_unset():
    release_video = subprocess.run(
        [
            "make",
            "-n",
            "release-video",
            "RELEASE_TAG=v1.1.0",
            "RELEASE_VIDEO_CLAUDE_MODEL=   ",
            "CLAUDE_CLI=",
            "PDS_CLI=",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    preflight = subprocess.run(
        [
            "make",
            "-n",
            "check-release-video-config",
            "RELEASE_VIDEO_CLAUDE_MODEL=",
            "PDS_CLI=   ",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )

    assert '--claude-cli "claude"' in release_video.stdout
    assert '--claude-model "claude-opus-4-8"' in release_video.stdout
    assert '--pds-cli "npx -y @promptdriven/pds@0.1.11 --timeout 120s"' in (
        release_video.stdout
    )
    assert '--claude-model "claude-opus-4-8"' in preflight.stdout
    assert '--pds-cli "npx -y @promptdriven/pds@0.1.11 --timeout 120s"' in (
        preflight.stdout
    )


def test_release_video_workflow_defaults_and_preflights_recovery_capable_pds_cli():
    workflow_text = (ROOT / ".github" / "workflows" / "release.yml").read_text(
        encoding="utf8"
    )

    assert (
        "PDS_CLI_PACKAGE: "
        "${{ vars.PDS_CLI_PACKAGE || '@promptdriven/pds@0.1.11' }}"
        in workflow_text
    )
    assert "make check-release-video-config" in workflow_text


def test_release_video_metadata_conflict_recovery_is_documented():
    doc_text = (
        ROOT / "docs" / "contributors" / "pdd-cli-release-process.md"
    ).read_text(encoding="utf8")

    assert "Keep `RELEASE_VIDEO_METADATA_CONFLICT` unset" in doc_text
    assert "RELEASE_VIDEO_METADATA_CONFLICT=replace" in doc_text
    assert "RELEASE_VIDEO_FORCE_REGENERATE=1" in doc_text
    assert "--metadata-conflict replace --force-regenerate" in doc_text


def test_release_video_makefile_has_status_target():
    makefile_text = (ROOT / "Makefile").read_text(encoding="utf8")

    default = subprocess.run(
        ["make", "-n", "release-video-status", "RELEASE_TAG=v0.0.289"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    with_query = subprocess.run(
        [
            "make",
            "-n",
            "release-video-status",
            "RELEASE_TAG=v0.0.289",
            "RELEASE_VIDEO_STATUS_QUERY=1",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )

    assert "RELEASE_VIDEO_STATUS_QUERY ?= 0" in makefile_text
    assert "release-video-status:" in makefile_text
    assert "--status" in makefile_text
    assert "--status-query" not in default.stdout
    assert "--status-query" in with_query.stdout
    assert 'RELEASE_TAG is required' in makefile_text


def test_release_video_can_select_existing_pds_project(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--claude-cli",
            str(claude_stub(tmp_path)),
            "--pds-cli",
            str(pds_stub(tmp_path, {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/existing"}})),
            "--project-id",
            "release-project",
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    pds_call = json.loads(capture.read_text(encoding="utf8"))["argv"]
    assert pds_call[:2] == ["--project", "release-project"]
    assert pds_call[2:4] == ["release-video", "create"]
    assert "--project-name" not in pds_call


def test_release_video_can_pass_custom_claude_tool_allowlist(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    env = release_video_env(
        {
            "PDS_STUB_CAPTURE": str(capture),
            "RELEASE_VIDEO_CLAUDE_TOOLS": "Read,Grep,Bash(git show *)",
        }
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--claude-cli",
            str(claude_stub(tmp_path)),
            "--pds-cli",
            str(pds_stub(tmp_path, {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/tools"}})),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    claude_argv = json.loads((repo / "claude_argv.json").read_text(encoding="utf8"))
    assert claude_argv[claude_argv.index("--allowedTools") + 1] == "Read,Grep,Bash(git show *)"


def test_release_video_can_reuse_existing_script_without_invoking_claude(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--script-path",
            str(existing_script),
            "--claude-cli",
            str(tmp_path / "missing-claude"),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/reused"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    assert f"using prewritten script from {existing_script}" in result.stdout
    assert "https://youtu.be/reused" in result.stdout
    assert not (repo / "claude_prompt.txt").exists()
    output_dir = tmp_path / "videos" / "v1.1.0"
    script_text = (output_dir / "release_video_script.md").read_text(encoding="utf8")
    assert "\n## Opening (0:00 - 0:30)" in script_text
    assert "\n## Details (0:30 - 1:00)" in script_text
    pds_call = json.loads(capture.read_text(encoding="utf8"))["argv"]
    assert pds_call[pds_call.index("--script") + 1] == str(
        output_dir / "release_video_script.md"
    )


def test_release_video_claude_quota_failure_is_script_generation_diagnostic(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})
    claude = claude_failure_stub(
        tmp_path,
        "You've hit your weekly limit; resets on Jun 12, 2026 at 9am UTC\n",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--claude-cli",
            str(claude),
            "--pds-cli",
            str(
                pds_stub(
                    tmp_path,
                    {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/quota"}},
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )

    assert result.returncode == 1
    assert "Claude Code script generation failed before PDS publish" in result.stderr
    assert "PDS was not invoked" in result.stderr
    assert "quota/auth class 'credential-limit'" in result.stderr
    assert "RELEASE_VIDEO_SCRIPT_PATH" in result.stderr
    assert not capture.exists()


def test_release_video_claude_generation_prefers_oauth_over_inherited_api_key(
    tmp_path: Path,
    monkeypatch,
):
    release_video = load_release_video_module()
    prompt_template = tmp_path / "release_video_LLM.prompt"
    prompt_template.write_text("Context:\n{release_context}\n", encoding="utf8")
    captured: dict[str, object] = {}

    def fake_run(
        command,
        *,
        cwd: Path,
        input_text: str | None = None,
        timeout: float | None = None,
        env: dict[str, str] | None = None,
        check: bool = True,
    ):
        captured["command"] = command
        captured["input_text"] = input_text
        captured["env"] = env
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=reusable_script_text(),
            stderr="",
        )

    monkeypatch.setenv("ANTHROPIC_API_KEY", "stale-depleted-api-key")
    monkeypatch.setenv("ANTHROPIC_AUTH_TOKEN", "stale-auth-token")
    monkeypatch.setenv("CLAUDE_CODE_OAUTH_TOKEN", "oauth-token")
    monkeypatch.delenv("PDD_KEEP_ANTHROPIC_API_KEY", raising=False)
    monkeypatch.setattr(release_video, "ensure_command_exists", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(release_video, "run", fake_run)

    script = release_video.generate_script_with_claude(
        context="# PDD release context",
        claude_cli="claude",
        claude_model="claude-opus-4-8",
        claude_tools="",
        prompt_template=prompt_template,
        timeout=60,
        cwd=tmp_path,
    )

    claude_env = captured["env"]
    assert isinstance(claude_env, dict)
    assert "ANTHROPIC_API_KEY" not in claude_env
    assert "ANTHROPIC_AUTH_TOKEN" not in claude_env
    assert claude_env["CLAUDE_CODE_OAUTH_TOKEN"] == "oauth-token"
    assert os.environ["ANTHROPIC_API_KEY"] == "stale-depleted-api-key"
    assert os.environ["ANTHROPIC_AUTH_TOKEN"] == "stale-auth-token"
    assert "--model" in captured["command"]
    assert "PDD release context" in captured["input_text"]
    assert "\nNARRATOR:\n" in script


def test_release_video_claude_generation_rotates_oauth_token_slots(
    tmp_path: Path,
    monkeypatch,
    capsys,
):
    release_video = load_release_video_module()
    prompt_template = tmp_path / "release_video_LLM.prompt"
    prompt_template.write_text("Context:\n{release_context}\n", encoding="utf8")
    attempted_tokens: list[str | None] = []

    def fake_run(
        command,
        *,
        cwd: Path,
        input_text: str | None = None,
        timeout: float | None = None,
        env: dict[str, str] | None = None,
        check: bool = True,
    ):
        token = env.get("CLAUDE_CODE_OAUTH_TOKEN") if env else None
        attempted_tokens.append(token)
        assert env is not None
        assert "ANTHROPIC_API_KEY" not in env
        if token == "limited-token":
            return subprocess.CompletedProcess(
                command,
                1,
                stdout="You've hit your weekly limit; resets tomorrow.",
                stderr="",
            )
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=reusable_script_text(),
            stderr="",
        )

    monkeypatch.setenv("ANTHROPIC_API_KEY", "stale-depleted-api-key")
    monkeypatch.setenv("CLAUDE_CODE_OAUTH_TOKEN_1", "limited-token")
    monkeypatch.setenv("CLAUDE_CODE_OAUTH_TOKEN_2", "fresh-token")
    monkeypatch.delenv("CLAUDE_CODE_OAUTH_TOKEN_3", raising=False)
    monkeypatch.delenv("CLAUDE_CODE_OAUTH_TOKEN", raising=False)
    monkeypatch.setattr(release_video, "ensure_command_exists", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(release_video, "run", fake_run)

    script = release_video.generate_script_with_claude(
        context="# PDD release context",
        claude_cli="claude",
        claude_model="claude-opus-4-8",
        claude_tools="",
        prompt_template=prompt_template,
        timeout=60,
        cwd=tmp_path,
    )

    assert attempted_tokens == ["limited-token", "fresh-token"]
    assert "\nNARRATOR:\n" in script
    assert "CLAUDE_CODE_OAUTH_TOKEN_1 failed" in capsys.readouterr().err


def test_release_video_claude_generation_rotates_organization_disabled_slot(
    tmp_path: Path,
    monkeypatch,
    capsys,
):
    release_video = load_release_video_module()
    prompt_template = tmp_path / "release_video_LLM.prompt"
    prompt_template.write_text("Context:\n{release_context}\n", encoding="utf8")
    disabled_token = "secret-organization-disabled-token"
    fresh_token = "secret-fresh-token"
    attempted_tokens: list[str | None] = []

    def fake_run(
        command,
        *,
        cwd: Path,
        input_text: str | None = None,
        timeout: float | None = None,
        env: dict[str, str] | None = None,
        check: bool = True,
    ):
        token = env.get("CLAUDE_CODE_OAUTH_TOKEN") if env else None
        attempted_tokens.append(token)
        if token == disabled_token:
            return subprocess.CompletedProcess(
                command,
                1,
                stdout=(
                    "Your organization has disabled Claude subscription access for "
                    "Claude Code · Use an Anthropic API key instead, or ask your admin "
                    "to enable access"
                ),
                stderr="",
            )
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=reusable_script_text(),
            stderr="",
        )

    monkeypatch.setenv("CLAUDE_CODE_OAUTH_TOKEN_1", disabled_token)
    monkeypatch.setenv("CLAUDE_CODE_OAUTH_TOKEN_2", fresh_token)
    monkeypatch.delenv("CLAUDE_CODE_OAUTH_TOKEN_3", raising=False)
    monkeypatch.delenv("CLAUDE_CODE_OAUTH_TOKEN", raising=False)
    monkeypatch.setattr(release_video, "ensure_command_exists", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(release_video, "run", fake_run)

    script = release_video.generate_script_with_claude(
        context="# PDD release context",
        claude_cli="claude",
        claude_model="claude-opus-4-8",
        claude_tools="",
        prompt_template=prompt_template,
        timeout=60,
        cwd=tmp_path,
    )

    captured = capsys.readouterr()
    assert attempted_tokens == [disabled_token, fresh_token]
    assert "\nNARRATOR:\n" in script
    assert "CLAUDE_CODE_OAUTH_TOKEN_1 failed" in captured.err
    assert disabled_token not in captured.out + captured.err
    assert fresh_token not in captured.out + captured.err


def test_release_video_env_oauth_strip_does_not_import_pdd(monkeypatch):
    release_video = load_release_video_module()
    env = {
        "ANTHROPIC_API_KEY": "stale-depleted-api-key",
        "ANTHROPIC_AUTH_TOKEN": "stale-auth-token",
        "CLAUDE_CODE_OAUTH_TOKEN": "oauth-token",
    }
    real_import = builtins.__import__

    def guarded_import(name, *args, **kwargs):
        if name == "pdd" or name.startswith("pdd."):
            raise AssertionError(f"unexpected pdd import: {name}")
        return real_import(name, *args, **kwargs)

    with monkeypatch.context() as guard:
        guard.setattr(builtins, "__import__", guarded_import)
        assert release_video.strip_anthropic_creds_for_claude_subprocess(env) is True

    assert "ANTHROPIC_API_KEY" not in env
    assert "ANTHROPIC_AUTH_TOKEN" not in env
    assert env["CLAUDE_CODE_OAUTH_TOKEN"] == "oauth-token"


def test_release_video_env_oauth_strip_recognizes_token_slots(monkeypatch):
    release_video = load_release_video_module()
    env = {
        "ANTHROPIC_API_KEY": "stale-depleted-api-key",
        "CLAUDE_CODE_OAUTH_TOKEN_2": "oauth-token",
    }

    assert release_video.strip_anthropic_creds_for_claude_subprocess(env) is True

    assert "ANTHROPIC_API_KEY" not in env
    assert env["CLAUDE_CODE_OAUTH_TOKEN_2"] == "oauth-token"


def test_release_video_strip_missing_optional_pdd_dependency_is_nonfatal(monkeypatch):
    release_video = load_release_video_module()
    env = {"ANTHROPIC_API_KEY": "stale-depleted-api-key"}
    real_import = builtins.__import__

    def missing_yaml_import(name, *args, **kwargs):
        if name == "pdd.agentic_common":
            raise ModuleNotFoundError("No module named 'yaml'", name="yaml")
        return real_import(name, *args, **kwargs)

    with monkeypatch.context() as guard:
        guard.setattr(builtins, "__import__", missing_yaml_import)
        assert release_video.strip_anthropic_creds_for_claude_subprocess(env) is False

    assert env["ANTHROPIC_API_KEY"] == "stale-depleted-api-key"


def test_release_video_claude_quota_auth_classifier():
    release_video = load_release_video_module()

    assert (
        release_video.classify_claude_quota_auth_failure(
            "You've hit your weekly limit; resets tomorrow."
        )
        == "credential-limit"
    )
    assert (
        release_video.classify_claude_quota_auth_failure("please run /login")
        == "oauth/login"
    )
    assert release_video.classify_claude_quota_auth_failure("401 unauthorized") == "auth"
    assert (
        release_video.classify_claude_quota_auth_failure(
            "Your organization has disabled Claude subscription access for Claude Code "
            "· Use an Anthropic API key instead, or ask your admin to enable access"
        )
        == "auth"
    )
    assert release_video.classify_claude_quota_auth_failure("temporary network error") is None


def test_release_video_fails_for_missing_prompt_template(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    missing_prompt = tmp_path / "missing_release_video_LLM.prompt"
    env = release_video_env(
        {
            "PDS_STUB_CAPTURE": str(tmp_path / "pds-capture.json"),
            "RELEASE_VIDEO_PROMPT_TEMPLATE": str(missing_prompt),
        }
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--claude-cli",
            str(claude_stub(tmp_path)),
            "--pds-cli",
            str(pds_stub(tmp_path, {"ok": True, "summary": {"youtubeUrl": "https://youtu.be/prompt"}})),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )

    assert result.returncode == 1
    assert f"Release-video prompt template not found: {missing_prompt}" in result.stderr
    assert not (repo / "claude_prompt.txt").exists()


def test_release_video_preflight_warns_for_project_scoped_profile(tmp_path: Path):
    config_home = tmp_path / "config"
    pds_config_dir = config_home / "pds"
    pds_config_dir.mkdir(parents=True)
    (pds_config_dir / "config.json").write_text(
        json.dumps(
            {
                "currentProfile": "v18finish",
                "profiles": {
                    "v18finish": {
                        "apiUrl": "https://video.promptdriven.ai",
                        "projectId": "pdd-release-v0-0-260",
                        "token": "local-secret-token",
                    }
                },
            }
        ),
        encoding="utf8",
    )
    env = release_video_env({"XDG_CONFIG_HOME": str(config_home)})
    env.pop("PDS_TOKEN", None)
    env.pop("PDS_PROFILE", None)
    env.pop("RELEASE_VIDEO_PROJECT_ID", None)

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--preflight",
            "--pds-cli",
            str(pds_version_stub(tmp_path, "0.1.11\n")),
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )

    assert result.returncode == 0
    assert "release-video preflight warning" in result.stderr
    assert "v18finish" in result.stderr
    assert "pdd-release-v0-0-260" in result.stderr
    assert "PDS agent token is not allowed for this project" in result.stderr
    assert "local-secret-token" not in result.stdout + result.stderr


def test_release_video_preflight_allows_env_token_without_printing_it(tmp_path: Path):
    config_home = tmp_path / "config"
    pds_config_dir = config_home / "pds"
    pds_config_dir.mkdir(parents=True)
    (pds_config_dir / "config.json").write_text(
        json.dumps(
            {
                "currentProfile": "v18finish",
                "profiles": {
                    "v18finish": {
                        "projectId": "pdd-release-v0-0-260",
                        "token": "local-secret-token",
                    }
                },
            }
        ),
        encoding="utf8",
    )
    env = {
        **release_video_env(),
        "XDG_CONFIG_HOME": str(config_home),
        "PDS_TOKEN": "env-secret-token",
    }
    env.pop("PDS_PROFILE", None)
    env.pop("RELEASE_VIDEO_PROJECT_ID", None)

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--preflight",
            "--pds-cli",
            str(pds_version_stub(tmp_path, "0.1.11\n")),
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )

    assert result.returncode == 0
    assert "PDS_TOKEN is set" in result.stdout
    assert "local preflight cannot verify token scopes or project access" in result.stdout
    assert "PDS server preflight" in result.stdout
    assert "continue accessing it afterward" in result.stdout
    assert "release-video preflight warning" not in result.stderr
    assert "env-secret-token" not in result.stdout + result.stderr
    assert "local-secret-token" not in result.stdout + result.stderr


def test_release_video_preflight_with_env_token_and_project_reports_fixed_project(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    env = release_video_env({"PDS_TOKEN": "env-secret-token"})

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--preflight",
            "--project-id",
            "fixed-project-123",
            "--pds-cli",
            str(pds_version_stub(tmp_path, "0.1.11\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )

    assert "using explicit PDS project fixed-project-123" in result.stdout
    assert "PDS_TOKEN is set for explicit PDS project fixed-project-123" in result.stdout
    assert "access to that fixed project" in result.stdout
    assert "Normal create-mode creates a new per-release project" not in result.stdout
    assert "env-secret-token" not in result.stdout + result.stderr


def test_release_video_preflight_reports_redacted_pds_cli_command_and_version(
    tmp_path: Path,
):
    pds_cli = (
        f"{pds_version_stub(tmp_path, '@promptdriven/pds 0.1.11\\n')} "
        "--token secret-preflight-token"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--preflight",
            "--pds-cli",
            pds_cli,
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        env=release_video_env(),
        check=True,
    )

    assert "release-video preflight: PDS CLI command:" in result.stdout
    assert "--token '[redacted]'" in result.stdout
    assert "release-video preflight: PDS CLI version: 0.1.11" in result.stdout
    assert "secret-preflight-token" not in result.stdout + result.stderr


def test_release_video_preflight_rejects_stale_pds_cli_version(tmp_path: Path):
    pds_cli = (
        f"{pds_version_stub(tmp_path, '@promptdriven/pds 0.1.10\\n')} "
        "--token secret-preflight-token"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--preflight",
            "--pds-cli",
            pds_cli,
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        env=release_video_env(),
        check=False,
    )

    assert result.returncode == 1
    assert "PDS CLI 0.1.10 is older than required 0.1.11" in result.stderr
    assert "--token '[redacted]'" in result.stdout
    assert "secret-preflight-token" not in result.stdout + result.stderr


def test_release_video_preflight_rejects_unknown_pds_cli_version(tmp_path: Path):
    pds_cli = (
        f"{pds_version_stub(tmp_path, 'pds development build\\n')} "
        "--token secret-preflight-token"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--preflight",
            "--pds-cli",
            pds_cli,
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        env=release_video_env(),
        check=False,
    )

    assert result.returncode == 1
    assert "could not determine PDS CLI version" in result.stderr
    assert "could not parse --version output" in result.stderr
    assert "--token '[redacted]'" in result.stdout
    assert "secret-preflight-token" not in result.stdout + result.stderr


def test_release_video_preflight_skip_allows_unknown_pds_cli_version(
    tmp_path: Path,
):
    pds_cli = pds_version_stub(tmp_path, "pds development build\n")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--preflight",
            "--pds-cli",
            str(pds_cli),
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        env=release_video_env({"RELEASE_VIDEO": "0"}),
        check=True,
    )

    assert "release-video preflight: skipped because RELEASE_VIDEO=0." in result.stdout


def test_release_video_publish_requires_youtube_url(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--claude-cli",
            str(claude_stub(tmp_path)),
            "--pds-cli",
            str(pds_stub(tmp_path, {"ok": True, "summary": {}})),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )

    assert result.returncode == 1
    assert "did not return a YouTube URL" in result.stderr


def test_release_video_accepts_noisy_create_stdout_json_without_leaking_secrets(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    stdout = (
        "debug Authorization: Bearer secret-create-stdout-token\n"
        + json.dumps({"youtubeUrl": "https://youtu.be/pdd-release"})
        + "\n"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=stdout)),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 0
    assert "https://youtu.be/pdd-release" in result.stdout
    assert "secret-create-stdout-token" not in result.stdout + result.stderr


def test_release_video_prefers_final_create_response_after_json_diagnostic(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    stdout = "\n".join(
        [
            json.dumps({"debug": True, "message": "starting release-video create"}),
            json.dumps({"youtubeUrl": "https://youtu.be/pdd-release"}),
        ]
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=stdout + "\n")),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 0
    assert "https://youtu.be/pdd-release" in result.stdout
    response = json.loads(
        (output_dir / "v1.1.0" / "pds_response.json").read_text(encoding="utf8")
    )
    assert response == {"youtubeUrl": "https://youtu.be/pdd-release"}


def test_release_video_create_parse_failure_redacts_stdout_secrets(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=(
                        "not json Authorization: Bearer "
                        "secret-invalid-stdout-token\n"
                    ),
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    assert "secret-invalid-stdout-token" not in result.stdout + result.stderr
    assert "Authorization: [redacted]" in result.stderr


def test_release_video_request_hash_mismatch_reports_idempotency_hint(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr='{"error":"request_hash_mismatch"}\n',
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    assert "request_hash_mismatch" in result.stderr
    assert "same idempotency key was reused with a different request body" in result.stderr


def test_pds_failure_hint_classifies_structured_quota_without_leaking():
    release_video = load_release_video_module()
    completed = subprocess.CompletedProcess(
        ["pds", "release-video", "create"],
        1,
        stdout=json.dumps(
            {
                "error": {
                    "code": "component_generation_provider_quota",
                    "token": "secret-provider-token",
                }
            }
        ),
        stderr="",
    )

    hint = release_video.pds_failure_hint(completed)

    assert "provider quota" in hint.lower()
    assert "No YouTube URL is expected" in hint
    assert "Do not rerun package/tag/PyPI" in hint
    assert "make release-video-skip" in hint
    assert "secret-provider-token" not in hint


def test_pds_failure_hint_classifies_plain_audit_gate_failure_from_stderr():
    release_video = load_release_video_module()
    completed = subprocess.CompletedProcess(
        ["pds", "release-video", "create"],
        1,
        stdout="",
        stderr="error: Distribution audit gate failed\n",
    )

    hint = release_video.pds_failure_hint(completed)

    assert "audit gate" in hint.lower()
    assert "No YouTube URL is expected" in hint
    assert "make release-video-skip" in hint


def test_pds_failure_hint_classifies_bounded_provider_429_plaintext():
    release_video = load_release_video_module()
    completed = subprocess.CompletedProcess(
        ["pds", "release-video", "create"],
        1,
        stdout="provider request failed with HTTP 429 quota exhausted\n",
        stderr="",
    )

    assert "provider quota" in release_video.pds_failure_hint(completed).lower()


def test_pds_failure_hint_recognizes_all_stable_provider_quota_codes():
    release_video = load_release_video_module()

    for code in (
        "provider_quota",
        "PROVIDER_QUOTA",
        "spec_generation_provider_quota",
        "component_generation_provider_quota",
    ):
        completed = subprocess.CompletedProcess(
            ["pds", "release-video", "create"],
            1,
            stdout=f"error: {code}\n",
            stderr="",
        )
        assert "provider quota" in release_video.pds_failure_hint(completed).lower()


def test_pds_failure_hint_ignores_misleading_or_unbounded_failure_prose():
    release_video = load_release_video_module()
    prose = (
        "The operator guide discusses provider quota and later mentions status 429, "
        "but this command failed because the network is offline."
    )
    completed = subprocess.CompletedProcess(
        ["pds", "release-video", "create"],
        1,
        stdout=prose,
        stderr="",
    )

    assert release_video.pds_failure_hint(completed) == ""


def test_pds_terminal_status_hint_ignores_prior_run_failure_codes():
    release_video = load_release_video_module()
    metadata = {
        "runId": "agent_run_current",
        "status": "failed",
        "lastStatusQuery": {
            "ok": True,
            "response": {
                "run": {"runId": "agent_run_current", "status": "failed"},
                "error": {"code": "render_failed"},
                "history": [
                    {
                        "runId": "agent_run_old",
                        "status": "failed",
                        "error": {"code": "provider_quota"},
                    }
                ],
            },
        },
    }

    assert release_video.pds_terminal_failure_hint_from_status(metadata) == ""


def test_pds_terminal_status_hint_rejects_mismatched_last_query_run():
    release_video = load_release_video_module()
    metadata = {
        "runId": "agent_run_current",
        "status": "failed",
        "lastStatusQuery": {
            "ok": True,
            "runId": "agent_run_old",
            "response": {
                "runId": "agent_run_old",
                "status": "failed",
                "error": {"code": "provider_quota"},
            },
        },
    }

    assert release_video.pds_terminal_failure_hint_from_status(metadata) == ""


def test_release_video_nonzero_status_ignores_mismatched_run_quota(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    response = {
        "runId": "agent_run_old",
        "status": "failed",
        "error": {
            "code": "provider_quota",
            "token": "secret-old-run-token",
        },
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(response) + "\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined = result.stdout + result.stderr
    assert result.returncode == 1
    assert "provider quota interrupted" not in combined.lower()
    assert "No YouTube URL is expected" not in combined
    assert "secret-old-run-token" not in combined


def test_release_video_nonzero_status_ignores_current_generic_failure_history(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    response = {
        "run": {"runId": "agent_run_current", "status": "failed"},
        "error": {"code": "render_failed"},
        "history": [
            {
                "runId": "agent_run_old",
                "status": "failed",
                "error": {"code": "provider_quota"},
            }
        ],
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(response) + "\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined = result.stdout + result.stderr
    assert result.returncode == 1
    assert "provider quota interrupted" not in combined.lower()
    assert "No YouTube URL is expected" not in combined


def test_release_video_create_ignores_historical_request_hash_failure(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    response = {
        "run": {"runId": "agent_run_current", "status": "failed"},
        "error": {"code": "render_failed"},
        "history": [
            {
                "runId": "agent_run_old",
                "status": "failed",
                "error": {"code": "request_hash_mismatch"},
            }
        ],
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr=json.dumps(response) + "\n",
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    assert "same idempotency key was reused" not in result.stderr


def test_release_video_create_provider_quota_reports_recovery_without_retry(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr=json.dumps(
                        {
                            "error": {
                                "code": "provider_quota",
                                "apiKey": "secret-provider-api-key",
                            }
                        }
                    )
                    + "\n",
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(tmp_path / "videos"),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined = result.stdout + result.stderr
    assert result.returncode == 1
    assert "provider quota" in combined.lower()
    assert "No YouTube URL is expected" in combined
    assert "Do not rerun package/tag/PyPI" in combined
    assert "make release-video-skip" in combined
    assert "secret-provider-api-key" not in combined
    assert "YouTube video:" not in combined
    assert len(json.loads(capture.read_text(encoding="utf8"))) > 0


def test_release_video_status_query_reports_delayed_terminal_provider_quota(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_quota",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "run": {"runId": "agent_run_quota", "status": "failed"},
        "error": {
            "code": "spec_generation_provider_quota",
            "authorization": "secret-status-authorization",
        },
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined = result.stdout + result.stderr
    assert result.returncode == 0
    assert "provider quota" in combined.lower()
    assert "No YouTube URL is expected" in combined
    assert "Do not rerun package/tag/PyPI" in combined
    assert "make release-video-skip" in combined
    assert "secret-status-authorization" not in combined
    assert "YouTube video:" not in combined


def test_release_video_nonzero_status_query_reports_audit_gate_recovery_hint(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_audit",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(
                        {
                            "ok": False,
                            "runId": "agent_run_audit",
                            "status": "failed",
                            "error": {
                                "code": "audit_failed",
                                "token": "secret-audit-token",
                            },
                        }
                    )
                    + "\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined = result.stdout + result.stderr
    assert result.returncode == 1
    assert "audit gate" in combined.lower()
    assert "No YouTube URL is expected" in combined
    assert "make release-video-skip" in combined
    assert "fresh RELEASE_VIDEO_ATTEMPT_ID" in combined
    assert "secret-audit-token" not in combined


def test_release_video_plain_status_audit_hint_requires_matching_run_handle(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_plain_audit",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    diagnostic = (
        "[pds] release-video run handle: "
        "runId=agent_run_plain_audit status=failed\n"
        "error: Distribution audit gate failed\n"
        "Authorization: Bearer secret-plain-audit-token\n"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr=diagnostic,
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined = result.stdout + result.stderr
    assert result.returncode == 1
    assert "audit gate blocked" in combined.lower()
    assert "fresh RELEASE_VIDEO_ATTEMPT_ID" in combined
    assert "Do not rerun package/tag/PyPI" in combined
    assert "secret-plain-audit-token" not in combined


def test_release_video_create_failure_redacts_pds_cli_command_secrets(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    pds_cli = (
        f"{pds_output_stub(tmp_path, stderr='pds unavailable\\n', exit_code=1)} "
        "--token secret-create-token --authorization secret-create-auth"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            pds_cli,
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    assert "secret-create-token" not in result.stderr
    assert "secret-create-auth" not in result.stderr
    assert "--token '[redacted]'" in result.stderr
    assert "--authorization '[redacted]'" in result.stderr


def test_release_video_create_uses_configured_pds_process_timeout(
    tmp_path: Path,
    monkeypatch,
):
    release_video = load_release_video_module()
    repo = init_release_repo(tmp_path)
    script_path = tmp_path / "release_video_script.md"
    release_notes_path = tmp_path / "release_notes.md"
    run_metadata_path = tmp_path / "pds_run.json"
    script_path.write_text(reusable_script_text(), encoding="utf8")
    release_notes_path.write_text("Release notes\n", encoding="utf8")
    observed_timeouts = []

    def fake_run(command, **kwargs):
        timeout = kwargs["timeout"]
        observed_timeouts.append(timeout)
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=json.dumps(
                {"summary": {"youtubeUrl": "https://youtu.be/timeout"}}
            ),
            stderr="",
        )

    monkeypatch.setattr(release_video, "run", fake_run)

    response = release_video.create_release_video(
        args=SimpleNamespace(
            pds_cli=sys.executable,
            project_id="",
            project_name="",
            idempotency_key="",
            idempotency_attempt_id="",
            idempotency_provenance="local-test",
            preset="release-notes",
            target="publish",
            platform="youtube",
            privacy="unlisted",
            bootstrap_selected_project=False,
            metadata_conflict="",
            force_regenerate=False,
            dry_run=False,
            pds_create_timeout=42.0,
        ),
        repo=repo,
        tag="v1.1.0",
        git_sha="abc123def456",
        repo_url="https://github.com/promptdriven/pdd",
        repo_name="promptdriven/pdd",
        script_path=script_path,
        release_notes_path=release_notes_path,
        changelog_path=Path("CHANGELOG.md"),
        run_metadata_path=run_metadata_path,
    )

    assert response["summary"]["youtubeUrl"] == "https://youtu.be/timeout"
    assert observed_timeouts == [42.0]


def test_release_video_create_timeout_persists_partial_pds_run_metadata(
    tmp_path: Path,
    monkeypatch,
):
    release_video = load_release_video_module()
    repo = init_release_repo(tmp_path)
    script_path = tmp_path / "release_video_script.md"
    release_notes_path = tmp_path / "release_notes.md"
    run_metadata_path = tmp_path / "pds_run.json"
    script_path.write_text(reusable_script_text(), encoding="utf8")
    release_notes_path.write_text("Release notes\n", encoding="utf8")
    timed_out_run = {
        "runId": "agent_run_timeout123",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
    }

    def fake_subprocess_run(command, **kwargs):
        raise subprocess.TimeoutExpired(
            command,
            kwargs["timeout"],
            output=json.dumps(timed_out_run) + "\n",
            stderr="[pds] still waiting\n",
        )

    monkeypatch.setattr(release_video.subprocess, "run", fake_subprocess_run)

    response = release_video.create_release_video(
        args=SimpleNamespace(
            pds_cli=sys.executable,
            project_id="",
            project_name="",
            idempotency_key="",
            idempotency_attempt_id="",
            idempotency_provenance="local-test",
            preset="release-notes",
            target="publish",
            platform="youtube",
            privacy="unlisted",
            bootstrap_selected_project=False,
            metadata_conflict="use-existing",
            force_regenerate=False,
            dry_run=False,
            pds_create_timeout=0.01,
        ),
        repo=repo,
        tag="v1.1.0",
        git_sha="abc123def456",
        repo_url="https://github.com/promptdriven/pdd",
        repo_name="promptdriven/pdd",
        script_path=script_path,
        release_notes_path=release_notes_path,
        changelog_path=Path("CHANGELOG.md"),
        run_metadata_path=run_metadata_path,
    )

    persisted = json.loads(run_metadata_path.read_text(encoding="utf8"))
    assert persisted["runId"] == "agent_run_timeout123"
    assert persisted["projectId"] == "pdd-v1-1-0-release"
    assert "release-video status --run-id agent_run_timeout123 --json" in persisted[
        "recoverCommand"
    ]
    assert "jobs watch --run-id agent_run_timeout123 --jsonl" in persisted[
        "watchCommand"
    ]
    assert response["ok"] is False
    assert response["pending"] is True
    assert response["reason"] == "pds_create_timeout_active_run"
    assert response["status"] == "running"
    assert response["runId"] == "agent_run_timeout123"
    assert response["projectId"] == "pdd-v1-1-0-release"
    assert response["pdsRun"] == persisted
    assert response["recoverCommand"] == persisted["recoverCommand"]
    assert response["watchCommand"] == persisted["watchCommand"]
    assert (
        response["statusCommand"]
        == "make release-video-status RELEASE_TAG=v1.1.0 RELEASE_VIDEO_STATUS_QUERY=1"
    )
    assert (
        response["backfillCommand"]
        == "make release-video-discord-backfill "
        "RELEASE_TAG=v1.1.0 RELEASE_VIDEO_YOUTUBE_URL=<youtube-url>"
    )


def test_release_video_main_timeout_with_active_project_run_reports_pending(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    timed_out_run = {
        "runId": "agent_run_timeout_cli",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_timeout_stub(
                    tmp_path,
                    stdout=json.dumps(timed_out_run) + "\n",
                    stderr="[pds] still waiting for release video create\n",
                )
            ),
            "--pds-create-timeout",
            "0.5",
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined_output = result.stdout + result.stderr
    make_prefix = f"make RELEASE_VIDEO_OUTPUT_DIR={shlex.quote(str(output_dir))}"
    response = json.loads(
        (output_dir / "v1.1.0" / "pds_response.json").read_text(encoding="utf8")
    )
    sidecar = json.loads(
        (output_dir / "v1.1.0" / "pds_run.json").read_text(encoding="utf8")
    )
    assert result.returncode == 0
    assert response["pending"] is True
    assert response["reason"] == "pds_create_timeout_active_run"
    assert sidecar["runId"] == "agent_run_timeout_cli"
    assert "release-video: PDS release-video create is still running" in combined_output
    assert "projectId=pdd-v1-1-0-release" in combined_output
    assert "runId=agent_run_timeout_cli" in combined_output
    assert "status=running" in combined_output
    assert (
        f"{make_prefix} release-video-status RELEASE_TAG=v1.1.0 "
        "RELEASE_VIDEO_STATUS_QUERY=1"
    ) in combined_output
    assert (
        f"{make_prefix} release-video-discord-backfill RELEASE_TAG=v1.1.0 "
        "RELEASE_VIDEO_YOUTUBE_URL=<youtube-url>"
    ) in combined_output
    assert "did not return a YouTube URL" not in combined_output


def test_release_video_project_exists_conflict_with_active_run_reports_pending(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    active_run = {
        "runId": "agent_run_existing_project",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr=(
                        "Project pdd-v1-1-0-release already exists; "
                        "metadata conflict while create is still active\n"
                        f"{json.dumps(active_run)}\n"
                    ),
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined_output = result.stdout + result.stderr
    response = json.loads(
        (output_dir / "v1.1.0" / "pds_response.json").read_text(encoding="utf8")
    )
    persisted = json.loads(
        (output_dir / "v1.1.0" / "pds_run.json").read_text(encoding="utf8")
    )
    assert result.returncode == 0
    assert response["pending"] is True
    assert response["reason"] == "pds_create_project_exists_active_run"
    assert response["runId"] == "agent_run_existing_project"
    assert persisted["runId"] == "agent_run_existing_project"
    pds_call = pds_capture_argv(capture)
    assert "--metadata-conflict" not in pds_call
    assert "release-video: PDS release-video create is still running" in combined_output
    assert "projectId=pdd-v1-1-0-release" in combined_output
    assert "runId=agent_run_existing_project" in combined_output
    assert "status=running" in combined_output
    assert "did not return a YouTube URL" not in combined_output


def test_release_video_pds_cli_timeout_with_active_run_reports_pending(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    active_run = {
        "runId": "agent_run_cli_timeout",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr=(
                        "release-video create timed out after 120s; "
                        "run is still active\n"
                        f"{json.dumps(active_run)}\n"
                    ),
                    exit_code=124,
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined_output = result.stdout + result.stderr
    response = json.loads(
        (output_dir / "v1.1.0" / "pds_response.json").read_text(encoding="utf8")
    )
    persisted = json.loads(
        (output_dir / "v1.1.0" / "pds_run.json").read_text(encoding="utf8")
    )
    assert result.returncode == 0
    assert response["pending"] is True
    assert response["reason"] == "pds_create_timeout_active_run"
    assert response["runId"] == "agent_run_cli_timeout"
    assert persisted["runId"] == "agent_run_cli_timeout"
    assert "release-video: PDS release-video create is still running" in combined_output
    assert "runId=agent_run_cli_timeout" in combined_output
    assert "did not return a YouTube URL" not in combined_output


def test_release_video_persists_structured_pds_run_handle_sidecar(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    structured_run = {
        "runId": "agent_run_json123",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
        "attemptId": "attempt-json123",
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr=json.dumps(structured_run) + "\n",
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    assert sidecar.exists()
    persisted = json.loads(sidecar.read_text(encoding="utf8"))
    assert persisted["runId"] == "agent_run_json123"
    assert persisted["projectId"] == "pdd-v1-1-0-release"
    assert persisted["status"] == "running"
    assert persisted["attemptId"] == "attempt-json123"
    assert (
        "release-video status --run-id agent_run_json123 --json"
        in persisted["recoverCommand"]
    )
    assert str(sidecar) in result.stderr


def test_release_video_persists_parent_project_for_wrapped_run_metadata(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    wrapped_run = {
        "ok": True,
        "projectId": "pdd-v1-1-0-release",
        "result": {
            "runId": "agent_run_wrapped_project",
            "status": "running",
        },
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr=json.dumps(wrapped_run) + "\n",
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    persisted = json.loads(sidecar.read_text(encoding="utf8"))
    assert persisted["runId"] == "agent_run_wrapped_project"
    assert persisted["projectId"] == "pdd-v1-1-0-release"
    assert "--project pdd-v1-1-0-release" in persisted["recoverCommand"]
    assert "--project pdd-v1-1-0-release" in persisted["watchCommand"]


def test_release_video_persists_explicit_project_when_pds_run_lacks_project_id(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--project-id",
            "fixed-release-project",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr=json.dumps(
                        {"runId": "agent_run_fixed_project", "status": "running"}
                    )
                    + "\n",
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    persisted = json.loads(sidecar.read_text(encoding="utf8"))
    assert persisted["projectId"] == "fixed-release-project"
    assert "--project fixed-release-project" in persisted["recoverCommand"]
    assert "--project fixed-release-project" in persisted["watchCommand"]


def test_release_video_persists_compatibility_run_handle_sidecar(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    compat_output = (
        "[pds] release-video run handle: "
        "runId=agent_run_line456 projectId=pdd-v1-1-0-release status=running\n"
        "[pds] recover: pds release-video status --run-id agent_run_line456 --json\n"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=compat_output,
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    assert result.returncode == 1
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    assert sidecar.exists()
    persisted = json.loads(sidecar.read_text(encoding="utf8"))
    assert persisted["runId"] == "agent_run_line456"
    assert persisted["projectId"] == "pdd-v1-1-0-release"
    assert persisted["status"] == "running"
    assert "jobs watch --run-id agent_run_line456 --jsonl" in persisted["watchCommand"]
    assert str(sidecar) in result.stderr


def test_release_video_redacts_pds_supplied_recovery_commands(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    output_dir = tmp_path / "videos"
    existing_script = tmp_path / "existing_release_video_script.md"
    existing_script.write_text(reusable_script_text(), encoding="utf8")
    compat_output = (
        "[pds] release-video run handle: "
        "runId=agent_run_secret_line status=running\n"
        "[pds] recover: pds --token secret-recover-token "
        "release-video status --run-id agent_run_secret_line --json\n"
        "[pds] watch: pds --pds-token secret-watch-token "
        "jobs watch --run-id agent_run_secret_line --jsonl\n"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--git-sha",
            "abc123def456",
            "--script-path",
            str(existing_script),
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=compat_output,
                    exit_code=1,
                )
            ),
            "--output-dir",
            str(output_dir),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    sidecar_text = (output_dir / "v1.1.0" / "pds_run.json").read_text(encoding="utf8")
    persisted = json.loads(sidecar_text)
    assert result.returncode == 1
    assert "secret-recover-token" not in sidecar_text
    assert "secret-watch-token" not in sidecar_text
    assert "--token" not in persisted["recoverCommand"]
    assert "--pds-token" not in persisted["watchCommand"]
    assert "release-video status --run-id agent_run_secret_line --json" in persisted[
        "recoverCommand"
    ]
    assert "jobs watch --run-id agent_run_secret_line --jsonl" in persisted["watchCommand"]


def test_release_video_pds_metadata_prefers_terminal_json_status():
    release_video = load_release_video_module()

    metadata = release_video.extract_pds_run_metadata(
        "\n".join(
            [
                json.dumps({"runId": "agent_run_multi", "status": "running"}),
                json.dumps(
                    {
                        "runId": "agent_run_multi",
                        "projectId": "pdd-v1-1-0-release",
                        "status": "failed",
                    }
                ),
            ]
        )
    )

    assert metadata == {
        "runId": "agent_run_multi",
        "projectId": "pdd-v1-1-0-release",
        "status": "failed",
    }


def test_release_video_pds_metadata_keeps_nested_project_context():
    release_video = load_release_video_module()

    metadata = release_video.extract_pds_run_metadata(
        json.dumps(
            {
                "run": {"runId": "agent_run_nested", "status": "running"},
                "project": {"projectId": "pdd-v1-1-0-release"},
            }
        )
    )

    assert metadata == {
        "runId": "agent_run_nested",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
    }


def test_release_video_pds_metadata_keeps_parent_project_for_nested_run_without_project():
    release_video = load_release_video_module()

    metadata = release_video.extract_pds_run_metadata(
        json.dumps(
            {
                "projectId": "pdd-v1-1-0-release",
                "run": {"id": "agent_run_nested_parent", "status": "running"},
            }
        )
    )

    assert metadata == {
        "runId": "agent_run_nested_parent",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
    }


def test_release_video_pds_metadata_keeps_current_run_over_nested_history():
    release_video = load_release_video_module()

    metadata = release_video.extract_pds_run_metadata(
        json.dumps(
            {
                "run": {"runId": "agent_run_current", "status": "running"},
                "project": {"projectId": "pdd-v1-1-0-release"},
                "history": [{"runId": "agent_run_old", "status": "failed"}],
            }
        )
    )

    assert metadata == {
        "runId": "agent_run_current",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
    }


def test_release_video_pds_metadata_prefers_result_over_history():
    release_video = load_release_video_module()

    metadata = release_video.extract_pds_run_metadata(
        json.dumps(
            {
                "history": [{"runId": "agent_run_old", "status": "failed"}],
                "result": {
                    "runId": "agent_run_current",
                    "projectId": "pdd-v1-1-0-release",
                    "status": "running",
                },
            }
        )
    )

    assert metadata == {
        "runId": "agent_run_current",
        "projectId": "pdd-v1-1-0-release",
        "status": "running",
    }


def test_release_video_status_prints_persisted_run_sidecar(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_status789",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
                "recoverCommand": (
                    "pds release-video status --run-id agent_run_status789 --json"
                ),
            }
        ),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env(),
        check=True,
    )

    assert "agent_run_status789" in result.stdout
    assert (
        "recover: pds --project pdd-v1-1-0-release release-video status "
        "--run-id agent_run_status789 --json"
        in result.stdout
    )
    assert result.stderr == ""


def test_release_video_status_marks_running_sidecar_as_stale(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_stale",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env(),
        check=True,
    )

    assert "agent_run_stale" in result.stdout
    assert "stale" in result.stdout.lower()
    assert "RELEASE_VIDEO_STATUS_QUERY=1" in result.stdout
    assert result.stderr == ""


def test_release_video_status_ignores_create_idempotency_conflict_env(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_status_env",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env(
            {
                "RELEASE_VIDEO_IDEMPOTENCY_KEY": "manual-key",
                "RELEASE_VIDEO_ATTEMPT_ID": "retry-operator",
            }
        ),
        check=True,
    )

    assert "agent_run_status_env" in result.stdout
    assert result.stderr == ""


def test_release_video_status_explicit_tag_does_not_require_local_git_tag(
    tmp_path: Path,
):
    repo = tmp_path / "repo-without-tags"
    repo.mkdir()
    output_dir = tmp_path / "videos"
    sidecar = output_dir / "v9.9.9" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps({"runId": "agent_run_no_local_tag", "status": "running"}),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v9.9.9",
            "--output-dir",
            str(output_dir),
            "--status",
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env(),
        check=True,
    )

    assert "agent_run_no_local_tag" in result.stdout
    assert result.stderr == ""


def test_release_video_status_query_uses_persisted_run_id(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_status_query",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(
                        {"runId": "agent_run_status_query", "status": "succeeded"}
                    )
                    + "\n",
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    assert pds_capture_argv(capture) == [
        "--project",
        "pdd-v1-1-0-release",
        "release-video",
        "status",
        "--run-id",
        "agent_run_status_query",
        "--json",
    ]
    assert '"status": "succeeded"' in result.stdout
    assert result.stderr == ""


def test_release_video_status_query_refreshes_sidecar_with_terminal_status_and_context(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_terminal",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "ok": True,
        "runId": "agent_run_terminal",
        "projectId": "pdd-v1-1-0-release",
        "status": "failed",
        "runError": {
            "code": "provider_capacity",
            "message": "Provider capacity failure",
            "retryable": True,
            "details": {"failedStage": "specs"},
        },
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env(
            {
                "PDS_STUB_CAPTURE": str(capture),
                "PDS_API_URL": "https://status.example.test",
                "PDS_TOKEN": "secret-status-token",
            }
        ),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["status"] == "failed"
    assert refreshed["lastStatusQuery"]["ok"] is True
    assert refreshed["lastStatusQuery"]["runStatus"] == "failed"
    assert refreshed["lastStatusQuery"]["response"]["runError"]["details"] == {
        "failedStage": "specs"
    }
    assert refreshed["pdsContext"]["apiUrl"] == "https://status.example.test"
    assert refreshed["pdsContext"]["apiUrlSource"] == "PDS_API_URL"
    assert refreshed["pdsContext"]["tokenSource"] == "PDS_TOKEN"
    assert "secret-status-token" not in sidecar.read_text(encoding="utf8")
    assert '"status": "failed"' in result.stdout
    assert result.stderr == ""


def test_release_video_status_query_nonzero_terminal_run_refreshes_sidecar(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_terminal_nonzero",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "runId": "agent_run_terminal_nonzero",
        "projectId": "pdd-v1-1-0-release",
        "status": "failed",
        "error": {"code": "render_failed", "message": "render step failed"},
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(status_response) + "\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert result.returncode == 1
    assert refreshed["runId"] == "agent_run_terminal_nonzero"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "failed"
    assert refreshed["statusStale"] is False
    assert refreshed["lastStatusQuery"]["ok"] is True
    assert refreshed["lastStatusQuery"]["runStatus"] == "failed"
    assert "--project pdd-v1-1-0-release" in refreshed["recoverCommand"]


def test_release_video_status_query_keeps_terminal_status_over_duplicate_running_handle(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_terminal_duplicate",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(
                        {
                            "runId": "agent_run_terminal_duplicate",
                            "projectId": "pdd-v1-1-0-release",
                            "status": "succeeded",
                        }
                    )
                    + "\n",
                    stderr=json.dumps(
                        {
                            "runId": "agent_run_terminal_duplicate",
                            "projectId": "pdd-v1-1-0-release",
                            "status": "running",
                        }
                    )
                    + "\n",
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["status"] == "succeeded"
    assert refreshed["lastStatusQuery"]["runStatus"] == "succeeded"
    assert refreshed["statusStale"] is False


def test_release_video_status_query_redacts_secret_diagnostics(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_secret_diagnostics",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(
                        {
                            "ok": False,
                            "error": {
                                "code": "auth_required",
                                "message": "Authorization: Bearer secret-status-token",
                            },
                            "signedUrl": "https://example.test/render?token=secret-url-token",
                        }
                    )
                    + "\n",
                    stderr="Authorization: Bearer secret-stderr-token\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    persisted_text = sidecar.read_text(encoding="utf8")
    persisted = json.loads(persisted_text)
    assert result.returncode == 1
    assert "secret-status-token" not in persisted_text
    assert "secret-stderr-token" not in persisted_text
    assert "secret-url-token" not in persisted_text
    assert "[redacted]" in persisted_text
    assert persisted["lastStatusQuery"]["errorMessage"] == "Authorization: [redacted]"
    assert "auth_required" in result.stderr


def test_release_video_status_query_redacts_structured_signed_url_fields(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_signed_fields",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    failure_response = {
        "ok": False,
        "X-Amz-Signature": "secret-structured-signature",
        "X-Amz-Credential": "secret-structured-credential",
        "error": {"message": "provider rejected signed upload"},
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(failure_response) + "\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    combined_output = result.stdout + result.stderr + sidecar_text
    persisted = json.loads(sidecar_text)
    assert result.returncode == 1
    assert "secret-structured-signature" not in combined_output
    assert "secret-structured-credential" not in combined_output
    assert persisted["lastStatusQuery"]["response"]["X-Amz-Signature"] == "[redacted]"
    assert persisted["lastStatusQuery"]["response"]["X-Amz-Credential"] == "[redacted]"


def test_release_video_status_query_redacts_plaintext_access_key_diagnostics(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_plaintext_credentials",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=(
                        "signature=secret-stdout-signature\n"
                        "AWS_ACCESS_KEY_ID=secret-stdout-access-key\n"
                    ),
                    stderr=(
                        "accessKeyId=secret-stderr-access-key\n"
                        "aws_secret_access_key=secret-stderr-secret-key\n"
                    ),
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    combined_output = result.stdout + result.stderr + sidecar_text
    assert result.returncode == 1
    assert "secret-stdout-signature" not in combined_output
    assert "secret-stdout-access-key" not in combined_output
    assert "secret-stderr-access-key" not in combined_output
    assert "secret-stderr-secret-key" not in combined_output
    assert combined_output.count("[redacted]") >= 4


def test_release_video_redacts_access_key_command_options_in_status_diagnostics(
    tmp_path: Path,
):
    release_video = load_release_video_module()
    completed = subprocess.CompletedProcess(
        ["pds"],
        1,
        stdout=(
            "retry with pds --access-key-id AKIASTDOUT "
            "--secret-access-key SECRETSTDOUT release-video status\n"
        ),
        stderr=(
            "retry with pds --access-key-id=AKIASTDERR "
            "--secret-access-key=SECRETSTDERR release-video status\n"
        ),
    )

    process_details = release_video.redacted_process_details(completed)
    status_stdout = release_video.redact_status_output_text(completed.stdout)
    status_stderr = release_video.redact_status_output_text(completed.stderr)
    sidecar = tmp_path / "pds_run.json"
    release_video.persist_status_query_failure(
        metadata={"runId": "agent_run_current", "status": "running"},
        path=sidecar,
        completed=completed,
        pds_cli="pds",
    )

    combined = (
        process_details
        + status_stdout
        + status_stderr
        + sidecar.read_text(encoding="utf8")
    )
    assert "AKIASTDOUT" not in combined
    assert "SECRETSTDOUT" not in combined
    assert "AKIASTDERR" not in combined
    assert "SECRETSTDERR" not in combined
    assert combined.count("[redacted]") >= 8


def test_release_video_redacts_status_query_output_and_command_secrets(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_secret_output",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    failure_response = {
        "ok": False,
        "runId": "agent_run_secret_output",
        "status": "running",
        "message": (
            "diagnostic at https://example.test/render?"
            "X-Amz-Signature=secret-sig&token=secret-url-token"
        ),
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(failure_response) + "\n",
                    stderr=(
                        "pds --token secret-token --pds-token secret-pds-token "
                        "--api-key secret-api-key failed\n"
                    ),
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    combined_output = result.stdout + result.stderr
    sidecar_text = sidecar.read_text(encoding="utf8")
    assert result.returncode == 1
    for secret in (
        "secret-token",
        "secret-pds-token",
        "secret-api-key",
        "secret-sig",
        "secret-url-token",
    ):
        assert secret not in combined_output
        assert secret not in sidecar_text
    assert "[redacted]" in combined_output
    assert "[redacted]" in sidecar_text


def test_release_video_status_query_redacts_pds_api_url_context(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_api_url",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(
                        {
                            "runId": "agent_run_api_url",
                            "projectId": "pdd-v1-1-0-release",
                            "status": "succeeded",
                        }
                    )
                    + "\n",
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env(
            {
                "PDS_STUB_CAPTURE": str(capture),
                "PDS_API_URL": (
                    "https://release-user:release-pass@status.example.test/status"
                    "?token=secret-url-token&X-Amz-Signature=secret-sig"
                ),
            }
        ),
        check=True,
    )

    persisted_text = sidecar.read_text(encoding="utf8")
    persisted = json.loads(persisted_text)
    for secret in (
        "release-user",
        "release-pass",
        "secret-url-token",
        "secret-sig",
    ):
        assert secret not in persisted_text
    assert "[redacted]" in persisted["pdsContext"]["apiUrl"]
    assert persisted["pdsContext"]["apiUrlSource"] == "PDS_API_URL"


def test_release_video_status_query_redacts_access_key_pds_cli_commands(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_access_key_cli",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {"runId": "agent_run_access_key_cli", "status": "succeeded"}
    pds_cli = (
        f"{pds_output_stub(tmp_path, stdout=json.dumps(status_response) + chr(10))} "
        "--secret-access-key value-space-alpha "
        "--aws-secret-access-key=value-equals-beta "
        "--access-key-id value-id-gamma "
        "--access-key=value-access-delta"
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            pds_cli,
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    combined_output = result.stdout + result.stderr + sidecar_text
    for secret in (
        "value-space-alpha",
        "value-equals-beta",
        "value-id-gamma",
        "value-access-delta",
    ):
        assert secret not in combined_output
    assert "[redacted]" in combined_output


def test_release_video_status_query_ignores_historical_terminal_runs(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "run": {"runId": "agent_run_current", "status": "running"},
        "project": {"projectId": "pdd-v1-1-0-release"},
        "history": [{"runId": "agent_run_old", "status": "failed"}],
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "running"
    assert refreshed["lastStatusQuery"]["runId"] == "agent_run_current"
    assert refreshed["lastStatusQuery"]["runStatus"] == "running"


def test_release_video_status_query_ignores_unrelated_terminal_json_values(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_stdout = "\n".join(
        [
            json.dumps({"runId": "agent_run_old", "status": "failed"}),
            json.dumps(
                {
                    "runId": "agent_run_current",
                    "projectId": "pdd-v1-1-0-release",
                    "status": "running",
                }
            ),
        ]
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=status_stdout + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "running"
    assert refreshed["lastStatusQuery"]["runId"] == "agent_run_current"
    assert refreshed["lastStatusQuery"]["runStatus"] == "running"


def test_release_video_status_query_ignores_unscoped_terminal_json_after_current_run(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_stdout = "\n".join(
        [
            json.dumps(
                {
                    "runId": "agent_run_current",
                    "projectId": "pdd-v1-1-0-release",
                    "status": "running",
                }
            ),
            json.dumps({"status": "failed", "message": "old unrelated terminal event"}),
        ]
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=status_stdout + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is False
    assert refreshed["lastStatusQuery"]["response"]["runId"] == "agent_run_current"
    assert refreshed["lastStatusQuery"]["runStatus"] == "running"


def test_release_video_status_query_prefers_wrapped_current_run_over_unscoped_terminal(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_stdout = "\n".join(
        [
            json.dumps(
                {
                    "ok": True,
                    "result": {
                        "runId": "agent_run_current",
                        "projectId": "pdd-v1-1-0-release",
                        "status": "succeeded",
                    },
                }
            ),
            json.dumps({"status": "failed", "message": "old unrelated terminal event"}),
        ]
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=status_stdout + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "succeeded"
    assert refreshed["statusStale"] is False
    assert refreshed["lastStatusQuery"]["response"]["result"]["runId"] == "agent_run_current"
    assert refreshed["lastStatusQuery"]["runStatus"] == "succeeded"


def test_release_video_status_query_keeps_stale_for_unscoped_status_wrapper(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout='{"ok": true, "status": "success"}\n')),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is True
    assert refreshed["lastStatusQuery"]["runStatus"] == "running"


def test_release_video_status_query_keeps_project_for_unscoped_project_response(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "projectId": "wrong-project",
        "status": "succeeded",
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is True
    assert "--project pdd-v1-1-0-release" in refreshed["recoverCommand"]
    assert "wrong-project" not in refreshed["recoverCommand"]
    assert "wrong-project" not in refreshed["watchCommand"]


def test_release_video_status_query_keeps_project_for_nested_run_wrapper_project(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "ok": True,
        "projectId": "wrong-project",
        "run": {"runId": "agent_run_current", "status": "running"},
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is False
    assert "--project pdd-v1-1-0-release" in refreshed["recoverCommand"]
    assert "wrong-project" not in refreshed["recoverCommand"]
    assert "wrong-project" not in refreshed["watchCommand"]


def test_release_video_status_query_prefers_nested_run_status_over_wrapper_status(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "ok": True,
        "status": "success",
        "run": {"runId": "agent_run_current", "status": "running"},
        "project": {"projectId": "pdd-v1-1-0-release"},
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is False
    assert refreshed["lastStatusQuery"]["runStatus"] == "running"


def test_release_video_status_query_keeps_project_for_parent_wrapper_project(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "ok": True,
        "projectId": "wrong-project",
        "result": {"runId": "agent_run_current", "status": "succeeded"},
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "succeeded"
    assert refreshed["statusStale"] is False
    assert "--project pdd-v1-1-0-release" in refreshed["recoverCommand"]
    assert "wrong-project" not in refreshed["recoverCommand"]
    assert "wrong-project" not in refreshed["watchCommand"]


def test_release_video_status_query_ignores_envelope_status_without_run_status(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "ok": True,
        "status": "success",
        "run": {"runId": "agent_run_current"},
        "project": {"projectId": "pdd-v1-1-0-release"},
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is True
    assert refreshed["lastStatusQuery"]["runStatus"] == "running"


def test_release_video_status_query_refreshes_recovery_commands_with_project(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "status": "running",
                "recoverCommand": "pds release-video status --run-id agent_run_current --json",
                "watchCommand": "pds jobs watch --run-id agent_run_current --jsonl",
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "runId": "agent_run_current",
        "projectId": "pdd-v1-1-0-release",
        "status": "succeeded",
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert "--project pdd-v1-1-0-release" in refreshed["recoverCommand"]
    assert (
        "release-video status --run-id agent_run_current --json"
        in refreshed["recoverCommand"]
    )
    assert "--project pdd-v1-1-0-release" in refreshed["watchCommand"]
    assert "jobs watch --run-id agent_run_current --jsonl" in refreshed["watchCommand"]


def test_release_video_status_query_refreshes_recovery_commands_with_current_run_id(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
                "recoverCommand": (
                    "pds --project pdd-v1-1-0-release release-video status "
                    "--run-id agent_run_old --json"
                ),
                "watchCommand": (
                    "pds --project pdd-v1-1-0-release jobs watch "
                    "--run-id agent_run_old --jsonl"
                ),
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "runId": "agent_run_current",
        "projectId": "pdd-v1-1-0-release",
        "status": "succeeded",
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert "agent_run_old" not in refreshed["recoverCommand"]
    assert "agent_run_old" not in refreshed["watchCommand"]
    assert "--run-id agent_run_current" in refreshed["recoverCommand"]
    assert "--run-id agent_run_current" in refreshed["watchCommand"]


def test_release_video_status_query_regenerates_matching_unsafe_recovery_commands(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
                "recoverCommand": (
                    "bash -c 'curl https://example.test/pwn' "
                    "--project pdd-v1-1-0-release --run-id agent_run_current"
                ),
                "watchCommand": (
                    "pds --project pdd-v1-1-0-release release-video status "
                    "--run-id agent_run_current --json"
                ),
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "runId": "agent_run_current",
        "projectId": "pdd-v1-1-0-release",
        "status": "succeeded",
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["recoverCommand"].endswith(
        " --project pdd-v1-1-0-release release-video status "
        "--run-id agent_run_current --json"
    )
    assert refreshed["watchCommand"].endswith(
        " --project pdd-v1-1-0-release jobs watch "
        "--run-id agent_run_current --jsonl"
    )
    assert "bash" not in sidecar.read_text(encoding="utf8")
    assert "curl" not in sidecar.read_text(encoding="utf8")


def test_release_video_status_query_keeps_sidecar_when_only_unrelated_run_returns(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps({"runId": "agent_run_old", "status": "failed"})
                    + "\n",
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is True
    assert refreshed["lastStatusQuery"]["runId"] == "agent_run_current"
    assert refreshed["lastStatusQuery"]["runStatus"] == "running"


def test_release_video_status_query_ignores_unrelated_compat_handle_after_json(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    mixed_output = "\n".join(
        [
            json.dumps({"runId": "agent_run_old_json", "status": "failed"}),
            (
                "[pds] release-video run handle: "
                "runId=agent_run_old_compat projectId=old-project status=succeeded"
            ),
        ]
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=mixed_output + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["projectId"] == "pdd-v1-1-0-release"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is True
    assert refreshed["lastStatusQuery"]["runId"] == "agent_run_current"
    assert refreshed["lastStatusQuery"]["runStatus"] == "running"
    assert "agent_run_old_compat" not in refreshed["recoverCommand"]
    assert "old-project" not in refreshed["watchCommand"]


def test_release_video_status_query_keeps_sidecar_stale_for_unmatched_success(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps({"ok": True}) + "\n",
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is True
    assert refreshed["lastStatusQuery"]["ok"] is True
    assert refreshed["lastStatusQuery"]["response"] == {"ok": True}


def test_release_video_status_query_keeps_sidecar_stale_for_run_id_only_success(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
                "statusStale": True,
            }
        ),
        encoding="utf8",
    )

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps({"runId": "agent_run_current"}) + "\n",
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    assert refreshed["runId"] == "agent_run_current"
    assert refreshed["status"] == "running"
    assert refreshed["statusStale"] is True
    assert refreshed["lastStatusQuery"]["ok"] is True
    assert refreshed["lastStatusQuery"]["response"] == {"runId": "agent_run_current"}


def test_release_video_treats_unknown_pds_status_as_active_not_terminal():
    release_video = load_release_video_module()

    for status in ("processing", "rendering", "uploading", "starting"):
        assert release_video.release_video_status_is_running(status) is True
        assert release_video.status_value_is_terminal(status) is False

    for status in ("succeeded", "completed", "failed", "cancelled"):
        assert release_video.release_video_status_is_running(status) is False
        assert release_video.status_value_is_terminal(status) is True


def test_release_video_status_note_warns_when_stale_flag_survives_success():
    release_video = load_release_video_module()
    note = release_video.release_video_status_note(
        {
            "runId": "agent_run_current",
            "status": "running",
            "statusStale": True,
            "lastStatusQuery": {"ok": True},
        }
    )

    assert "create-time run metadata may be stale" in note


def test_release_video_status_query_prints_refreshed_recovery_commands(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
                "recoverCommand": (
                    "pds --project pdd-v1-1-0-release release-video status "
                    "--run-id agent_run_old --json"
                ),
                "watchCommand": (
                    "pds --project pdd-v1-1-0-release jobs watch "
                    "--run-id agent_run_old --jsonl"
                ),
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "runId": "agent_run_current",
        "projectId": "pdd-v1-1-0-release",
        "status": "succeeded",
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    assert "agent_run_old" not in result.stdout
    assert "recover: " in result.stdout
    assert (
        "--project pdd-v1-1-0-release release-video status "
        "--run-id agent_run_current --json"
    ) in result.stdout
    assert "watch: " in result.stdout
    assert (
        "--project pdd-v1-1-0-release jobs watch "
        "--run-id agent_run_current --jsonl"
    ) in result.stdout
    status_argv = pds_capture_argv(capture)
    refreshed = json.loads(sidecar.read_text(encoding="utf8"))
    audit_fix_flags = (
        "--audit-fix-max-passes",
        "--audit-fix-max-annotations-per-pass",
        "--audit-fix-max-spend-pddc",
        "--audit-fix-source-approval",
    )
    assert status_argv[:4] == [
        "--project",
        "pdd-v1-1-0-release",
        "release-video",
        "status",
    ]
    for flag in audit_fix_flags:
        assert flag not in status_argv
        assert flag not in refreshed["recoverCommand"]
        assert flag not in refreshed["watchCommand"]


def test_release_video_status_query_success_redacts_legacy_sidecar_secrets(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_current",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
                "token": "secret-persisted-token",
                "recoverCommand": (
                    "pds --token secret-command-token "
                    "release-video status --run-id agent_run_current --json"
                ),
            }
        ),
        encoding="utf8",
    )
    status_response = {
        "runId": "agent_run_current",
        "projectId": "pdd-v1-1-0-release",
        "status": "succeeded",
    }

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(pds_output_stub(tmp_path, stdout=json.dumps(status_response) + "\n")),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=True,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    persisted = json.loads(sidecar_text)
    assert "secret-persisted-token" not in sidecar_text
    assert "secret-command-token" not in sidecar_text
    assert persisted["token"] == "[redacted]"
    assert persisted["recoverCommand"].endswith(
        " --project pdd-v1-1-0-release release-video status "
        "--run-id agent_run_current --json"
    )


def test_release_video_status_query_failure_records_diagnostic_without_refreshing(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_auth_failed",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    failure_response = {
        "ok": False,
        "error": {
            "code": "auth_required",
            "message": "Invalid or expired PDS agent token",
            "details": {},
        },
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(failure_response) + "\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env(
            {
                "PDS_STUB_CAPTURE": str(capture),
                "PDS_API_URL": "https://status.example.test",
                "PDS_TOKEN": "secret-status-token",
            }
        ),
        check=False,
    )

    assert result.returncode == 1
    persisted = json.loads(sidecar.read_text(encoding="utf8"))
    assert persisted["status"] == "running"
    assert persisted["statusStale"] is True
    assert persisted["lastStatusQuery"]["ok"] is False
    assert persisted["lastStatusQuery"]["errorCode"] == "auth_required"
    assert persisted["lastStatusQuery"]["errorMessage"] == "Invalid or expired PDS agent token"
    assert persisted["lastStatusQuery"]["pdsContext"]["apiUrl"] == "https://status.example.test"
    assert "secret-status-token" not in sidecar.read_text(encoding="utf8")
    assert "auth_required" in result.stderr


def test_release_video_status_query_failure_redacts_sensitive_status_details(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_auth_failed",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
                "authorization": "secret-sidecar-authz",
                "recoverCommand": (
                    "pds --token secret-recover-token "
                    "release-video status --run-id agent_run_auth_failed --json"
                ),
            }
        ),
        encoding="utf8",
    )
    failure_response = {
        "ok": False,
        "credential": "secret-status-credential",
        "authorization": "secret-status-authz",
        "error": {
            "code": "auth_required",
            "message": "credential secret-status-credential expired",
        },
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(failure_response) + "\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    persisted = json.loads(sidecar_text)
    combined_output = result.stdout + result.stderr + sidecar_text
    assert result.returncode == 1
    assert "secret-status-credential" not in combined_output
    assert "secret-status-authz" not in combined_output
    assert "secret-sidecar-authz" not in combined_output
    assert "secret-recover-token" not in combined_output
    assert persisted["authorization"] == "[redacted]"
    assert persisted["lastStatusQuery"]["response"]["credential"] == "[redacted]"
    assert persisted["lastStatusQuery"]["response"]["authorization"] == "[redacted]"
    assert "[redacted]" in persisted["lastStatusQuery"]["details"]


def test_release_video_status_query_failure_redacts_basic_authorization_details(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_auth_failed",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stderr="Authorization: Basic secret-basic-token\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    persisted = json.loads(sidecar_text)
    combined_output = result.stdout + result.stderr + sidecar_text
    assert result.returncode == 1
    assert "secret-basic-token" not in combined_output
    assert "Authorization: [redacted]" in result.stderr
    assert "Authorization: [redacted]" in persisted["lastStatusQuery"]["details"]


def test_release_video_status_query_failure_redacts_arbitrary_authorization_details(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_auth_failed",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    failure_response = {
        "ok": False,
        "message": "Authorization: ApiKey secret-api-key",
        "authorization": 'Digest username="u", nonce="secret-json-nonce"',
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(failure_response) + "\n",
                    stderr=(
                        "Authorization: Custom secret-custom-token secret-tail\n"
                        "Authorization: Digest username=\"u\", "
                        "nonce=\"secret-nonce\", response=\"secret-response\"\n"
                    ),
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    combined_output = result.stdout + result.stderr + sidecar_text
    assert result.returncode == 1
    for secret in (
        "secret-api-key",
        "secret-custom-token",
        "secret-tail",
        "secret-nonce",
        "secret-response",
        "secret-json-nonce",
    ):
        assert secret not in combined_output
    assert "Authorization: [redacted]" in result.stdout
    assert "Authorization: [redacted]" in result.stderr
    assert "Authorization: [redacted]" in sidecar_text


def test_release_video_status_query_failure_redacts_stdout_authorization_details(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_auth_failed",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    failure_response = {
        "ok": False,
        "authorization": 'Digest username="u", nonce="secret-json-nonce"',
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=json.dumps(failure_response) + "\n",
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    combined_output = result.stdout + result.stderr + sidecar_text
    assert result.returncode == 1
    assert "secret-json-nonce" not in combined_output
    assert '"authorization": "[redacted]"' in result.stdout
    assert '"authorization": "[redacted]"' in sidecar_text


def test_release_video_status_query_failure_redacts_embedded_stdout_json_authorization(
    tmp_path: Path,
):
    repo = init_release_repo(tmp_path)
    output_dir = tmp_path / "videos"
    capture = tmp_path / "pds-status-capture.json"
    sidecar = output_dir / "v1.1.0" / "pds_run.json"
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "runId": "agent_run_auth_failed",
                "projectId": "pdd-v1-1-0-release",
                "status": "running",
            }
        ),
        encoding="utf8",
    )
    failure_response = {
        "ok": False,
        "authorization": 'Digest username="u", nonce="secret-mixed-json-nonce"',
        "message": "Authorization: ApiKey secret-mixed-json-api-key",
    }

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--output-dir",
            str(output_dir),
            "--status",
            "--status-query",
            "--pds-cli",
            str(
                pds_output_stub(
                    tmp_path,
                    stdout=(
                        "pds debug before json\n"
                        f"{json.dumps(failure_response)}\n"
                        "pds debug after json\n"
                    ),
                    exit_code=1,
                )
            ),
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=release_video_env({"PDS_STUB_CAPTURE": str(capture)}),
        check=False,
    )

    sidecar_text = sidecar.read_text(encoding="utf8")
    combined_output = result.stdout + result.stderr + sidecar_text
    assert result.returncode == 1
    assert "secret-mixed-json-nonce" not in combined_output
    assert "secret-mixed-json-api-key" not in combined_output
    assert '"authorization": "[redacted]"' in result.stdout
    assert '"authorization": "[redacted]"' in sidecar_text
    assert "Authorization: [redacted]" in sidecar_text


def test_release_video_dry_run_does_not_require_youtube_url(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    env = release_video_env({"PDS_STUB_CAPTURE": str(capture)})

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo",
            str(repo),
            "--tag",
            "v1.1.0",
            "--claude-cli",
            str(claude_stub(tmp_path)),
            "--pds-cli",
            str(pds_stub(tmp_path, {"ok": True, "status": "planned"})),
            "--output-dir",
            str(tmp_path / "videos"),
            "--dry-run",
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
        check=True,
    )
    pds_call = json.loads(capture.read_text(encoding="utf8"))["argv"]
    assert "--dry-run" in pds_call


RETRY_SCRIPT = Path("scripts/claude_code_oauth_retry.sh").resolve()
RELEASE_WORKFLOW = Path(".github/workflows/release.yml")
BACKFILL_WORKFLOW = Path(".github/workflows/backfill-release-notes.yml")
AUTH_DIAGNOSTIC = (
    "Your organization has disabled Claude subscription access for Claude Code."
)
TOKEN_NAMES = (
    "CLAUDE_CODE_OAUTH_TOKEN_1",
    "CLAUDE_CODE_OAUTH_TOKEN_2",
    "CLAUDE_CODE_OAUTH_TOKEN_3",
    "CLAUDE_CODE_OAUTH_TOKEN",
)


@pytest.fixture
def fake_claude(tmp_path: Path) -> Path:
    command = tmp_path / "fake-claude"
    command.write_text(
        """#!/usr/bin/env bash
set -u
printf '%s\n' "${CLAUDE_CODE_OAUTH_TOKEN:-no-token}" >>"$ATTEMPTS_FILE"
case "${CLAUDE_CODE_OAUTH_TOKEN:-no-token}" in
  zero-stdout)
    printf '%s\n' "$AUTH_DIAGNOSTIC"
    exit 0
    ;;
  zero-stderr)
    printf '%s\n' 'These notes must not be accepted.'
    printf '%s\n' "$AUTH_DIAGNOSTIC" >&2
    exit 0
    ;;
  nonzero-stdout)
    printf '%s\n' 'Authentication failed: expired credential'
    exit 23
    ;;
  nonzero-stderr)
    printf '%s\n' 'quota exceeded' >&2
    exit 24
    ;;
  organization-disabled)
    printf '%s\n' "$AUTH_DIAGNOSTIC · Use an Anthropic API key instead, or ask your admin to enable access"
    exit 25
    ;;
  organization-disabled-prose)
    printf '%s\n' "This release handles '$AUTH_DIAGNOSTIC' without hiding valid notes."
    exit 0
    ;;
  large-after-diagnostic)
    printf '%s\n' "$AUTH_DIAGNOSTIC" >&2
    dd if=/dev/zero bs=1048576 count=2 2>/dev/null | tr '\0' x
    exit 0
    ;;
  typed_*)
    IFS=_ read -r _ envelope stream outcome <<EOF
${CLAUDE_CODE_OAUTH_TOKEN}
EOF
    case "$envelope" in
      api) message='API Error: 401 Invalid API key' ;;
      failed) message='Failed to authenticate. API Error: 401 Invalid bearer token' ;;
      json) message='{"type":"error","error":{"type":"authentication_error","message":"invalid x-api-key"}}' ;;
      login) message='Not logged in · Please run /login' ;;
      login401) message='Please run /login · API Error: 401 Invalid bearer token' ;;
      *) exit 98 ;;
    esac
    if [ "$stream" = stderr ]; then
      printf '%s\n' "$message" >&2
    else
      printf '%s\n' "$message"
    fi
    if [ "$outcome" = nonzero ]; then exit 25; fi
    exit 0
    ;;
  secret-stderr-*)
    printf 'provider rejected credential %s\n' "$CLAUDE_CODE_OAUTH_TOKEN" >&2
    exit 42
    ;;
  access-prose)
    printf '%s\n' 'Access denied: diagnostics now include remediation guidance.'
    exit 0
    ;;
  permission-prose)
    printf '%s\n' 'Permission denied: errors now identify the affected path.'
    exit 0
    ;;
  authentication-prose)
    printf '%s\n' 'Authentication failed: messages now explain how to recover.'
    exit 0
    ;;
  fatal)
    printf '%s\n' 'render process failed unexpectedly' >&2
    exit 42
    ;;
  empty)
    exit 0
    ;;
  prose)
    printf '%s\n' 'This release explains why authentication failed and how users can recover.'
    exit 0
    ;;
  good|no-token)
    printf '%s\n' 'A concise release summary.'
    exit 0
    ;;
  *)
    printf '%s\n' 'unexpected test token slot' >&2
    exit 99
    ;;
esac
"""
    )
    command.chmod(0o755)
    return command


def _run_wrapper(
    tmp_path: Path,
    fake_claude: Path,
    *tokens: str,
    output_file: Path | None = None,
    extra_env: dict[str, str] | None = None,
) -> tuple[subprocess.CompletedProcess[str], Path, list[str]]:
    output_file = output_file or tmp_path / "notes.md"
    attempts_file = tmp_path / "attempts"
    env = os.environ.copy()
    for name in TOKEN_NAMES:
        env.pop(name, None)
    env.update(
        {
            "ATTEMPTS_FILE": str(attempts_file),
            "AUTH_DIAGNOSTIC": AUTH_DIAGNOSTIC,
        }
    )
    env.update(dict(zip(TOKEN_NAMES, tokens, strict=False)))
    env.update(extra_env or {})
    result = subprocess.run(
        [str(RETRY_SCRIPT), str(output_file), str(fake_claude)],
        input="release context\n",
        text=True,
        capture_output=True,
        check=False,
        env=env,
    )
    attempts = attempts_file.read_text().splitlines() if attempts_file.exists() else []
    return result, output_file, attempts


def test_early_diagnostic_with_output_larger_than_pipe_buffer_retries(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, "large-after-diagnostic", "good"
    )

    assert result.returncode == 0, result.stderr
    assert output_file.stat().st_size < 1024
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == ["large-after-diagnostic", "good"]


@pytest.mark.parametrize("envelope", ["api", "failed", "json", "login", "login401"])
@pytest.mark.parametrize("stream", ["stdout", "stderr"])
@pytest.mark.parametrize("outcome", ["zero", "nonzero"])
def test_typed_claude_auth_envelopes_retry_next_token(
    tmp_path: Path,
    fake_claude: Path,
    envelope: str,
    stream: str,
    outcome: str,
) -> None:
    diagnostic_token = f"typed_{envelope}_{stream}_{outcome}"
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, diagnostic_token, "good"
    )

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == [diagnostic_token, "good"]


def test_non_diagnostic_failure_never_replays_oauth_secret(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    secret = "secret-stderr-super-secret-oauth-value"
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, secret
    )

    assert result.returncode == 42
    assert secret not in result.stdout
    assert secret not in result.stderr
    assert not output_file.exists()
    assert attempts == [secret]


@pytest.mark.parametrize(
    "token",
    ["access-prose", "permission-prose", "authentication-prose"],
)
def test_ambiguous_diagnostic_prefix_in_release_prose_is_valid(
    tmp_path: Path,
    fake_claude: Path,
    token: str,
) -> None:
    result, output_file, attempts = _run_wrapper(tmp_path, fake_claude, token)

    assert result.returncode == 0, result.stderr
    assert output_file.read_text().endswith(".\n")
    assert attempts == [token]


def test_atomic_publish_failure_preserves_preexisting_output(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    output_file = tmp_path / "notes.md"
    output_file.write_text("Existing generated notes\n")
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    failing_mv = fake_bin / "mv"
    failing_mv.write_text("#!/usr/bin/env bash\nexit 73\n")
    failing_mv.chmod(0o755)

    result, _, attempts = _run_wrapper(
        tmp_path,
        fake_claude,
        "good",
        output_file=output_file,
        extra_env={"PATH": f"{fake_bin}{os.pathsep}{os.environ['PATH']}"},
    )

    assert result.returncode != 0
    assert output_file.read_text() == "Existing generated notes\n"
    assert attempts == ["good"]


def test_unwritable_publish_target_returns_failure(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    output_file = tmp_path / "missing-directory" / "notes.md"

    result, _, attempts = _run_wrapper(
        tmp_path, fake_claude, "good", output_file=output_file
    )

    assert result.returncode != 0
    assert not output_file.exists()
    assert attempts == ["good"]


@pytest.mark.parametrize(
    "diagnostic_token",
    ["zero-stdout", "zero-stderr", "nonzero-stdout", "nonzero-stderr"],
)
def test_recognized_auth_or_quota_diagnostic_retries_next_token(
    tmp_path: Path,
    fake_claude: Path,
    diagnostic_token: str,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, diagnostic_token, "good"
    )

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == [diagnostic_token, "good"]
    assert diagnostic_token not in result.stderr


def test_organization_disabled_diagnostic_retries_without_leaking_tokens(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    disabled_token = "organization-disabled"
    fresh_token = "good"
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, disabled_token, fresh_token
    )

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == [disabled_token, fresh_token]
    assert disabled_token not in result.stderr
    assert fresh_token not in result.stderr


def test_organization_disabled_sentence_inside_release_notes_is_valid_output(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, "organization-disabled-prose"
    )

    assert result.returncode == 0, result.stderr
    assert output_file.read_text().startswith("This release handles")
    assert attempts == ["organization-disabled-prose"]


def test_all_retryable_tokens_fail_without_returning_diagnostic_as_notes(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path,
        fake_claude,
        "zero-stdout",
        "nonzero-stderr",
        "nonzero-stdout",
        "zero-stderr",
    )

    assert result.returncode != 0
    assert not output_file.exists() or output_file.read_text() == ""
    assert attempts == [
        "zero-stdout",
        "nonzero-stderr",
        "nonzero-stdout",
        "zero-stderr",
    ]
    assert all(token not in result.stderr for token in attempts)


def test_non_diagnostic_failure_keeps_status_and_does_not_rotate(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, "fatal", "good"
    )

    assert result.returncode == 42
    assert not output_file.exists() or output_file.read_text() == ""
    assert attempts == ["fatal"]


def test_empty_success_is_rejected(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(tmp_path, fake_claude, "empty", "good")

    assert result.returncode != 0
    assert not output_file.exists() or output_file.read_text() == ""
    assert attempts == ["empty"]


def test_non_diagnostic_prose_is_valid_notes(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(tmp_path, fake_claude, "prose")

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == (
        "This release explains why authentication failed and how users can recover.\n"
    )
    assert attempts == ["prose"]


def test_no_configured_token_preserves_direct_command_fallback(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(tmp_path, fake_claude)

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == ["no-token"]


def _workflow_step(path: Path, name: str) -> str:
    workflow = yaml.safe_load(path.read_text())
    jobs = workflow["jobs"]
    for job in jobs.values():
        for step in job.get("steps", []):
            if step.get("name") == name:
                return step["run"]
    raise AssertionError(f"Missing workflow step {name!r} in {path}")


def _workflow_rewrite_boundary(path: Path) -> str:
    script = _workflow_step(path, "Rewrite release notes with Claude Code")
    start = script.index("notes_file=$(mktemp")
    end_marker = 'echo "Updated release notes for $tag."'
    end = script.index(end_marker, start) + len(end_marker)
    return script[start:end]


def _run_workflow_rewrite_failure(
    tmp_path: Path,
    workflow_path: Path,
) -> tuple[subprocess.CompletedProcess[str], str, list[str]]:
    fake_bin = tmp_path / "workflow-bin"
    fake_bin.mkdir()
    fake_mktemp = fake_bin / "mktemp"
    fake_mktemp.write_text(
        "#!/usr/bin/env bash\n"
        "exec /usr/bin/mktemp \"${TMPDIR:-/tmp}/workflow.XXXXXX\"\n"
    )
    fake_mktemp.chmod(0o755)
    fake_claude = fake_bin / "claude"
    fake_claude.write_text(
        "#!/usr/bin/env bash\n"
        f"printf '%s\\n' '{AUTH_DIAGNOSTIC}'\n"
        "exit 0\n"
    )
    fake_claude.chmod(0o755)

    release_state = tmp_path / "release-state.md"
    release_state.write_text("Existing GitHub-generated notes\n")
    gh_calls = tmp_path / "gh-calls"
    fake_gh = fake_bin / "gh"
    fake_gh.write_text(
        """#!/usr/bin/env bash
printf '%s\n' "$*" >>"$GH_CALLS"
if [ "${1:-} ${2:-}" = "release edit" ]; then
  printf '%s\n' 'MUTATED' >"$RELEASE_STATE"
fi
"""
    )
    fake_gh.chmod(0o755)

    prompt_file = tmp_path / "prompt"
    prompt_file.write_text("release prompt context\n")
    attempts_file = tmp_path / "attempts"
    env = os.environ.copy()
    for name in TOKEN_NAMES:
        env.pop(name, None)
    env.update(
        {
            "PATH": f"{fake_bin}{os.pathsep}{env['PATH']}",
            "CLAUDE_CODE_OAUTH_TOKEN_1": "workflow-disabled-slot",
            "GH_CALLS": str(gh_calls),
            "RELEASE_STATE": str(release_state),
            "ATTEMPTS_FILE": str(attempts_file),
            "prompt_file": str(prompt_file),
            "auto_notes": "GitHub-generated attribution",
            "tag": "v-test",
        }
    )
    result = subprocess.run(
        [
            "bash",
            "-c",
            f"set -euo pipefail\n{_workflow_rewrite_boundary(workflow_path)}",
        ],
        cwd=RETRY_SCRIPT.parent.parent,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    calls = gh_calls.read_text().splitlines() if gh_calls.exists() else []
    return result, release_state.read_text(), calls


def test_release_workflow_behavior_keeps_generated_notes_on_validation_failure(
    tmp_path: Path,
) -> None:
    result, release_state, gh_calls = _run_workflow_rewrite_failure(
        tmp_path, RELEASE_WORKFLOW
    )

    assert result.returncode == 0, result.stderr
    assert "keeping auto-generated notes" in result.stdout
    assert release_state == "Existing GitHub-generated notes\n"
    assert all(not call.startswith("release edit") for call in gh_calls)


def test_backfill_workflow_behavior_preserves_release_on_validation_failure(
    tmp_path: Path,
) -> None:
    result, release_state, gh_calls = _run_workflow_rewrite_failure(
        tmp_path, BACKFILL_WORKFLOW
    )

    assert result.returncode != 0
    assert release_state == "Existing GitHub-generated notes\n"
    assert all(not call.startswith("release edit") for call in gh_calls)
