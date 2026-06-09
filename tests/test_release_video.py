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
        "RELEASE_VIDEO_CLAUDE_TOOLS",
        "RELEASE_VIDEO_PROMPT_TEMPLATE",
        "RELEASE_VIDEO_SCRIPT_PATH",
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
