import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "release_video.py"


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
import pathlib
import sys

prompt = sys.stdin.read()
pathlib.Path("claude_prompt.txt").write_text(prompt, encoding="utf8")
print("# PDD v1.1.0 Release Video\\n\\n"
      "Hook: This release turns the PDD release process into a publishable video story.\\n\\n"
      "Narration: PDD v1.1.0 adds release video automation, using release context to create a concise update for developers. "
      "The video shows the changed files, the release tag, and the path from script to YouTube upload. "
      "It closes with a reminder that the release artifact and the release story now ship together.\\n\\n"
      "Visual direction: show the changelog, a terminal running make release, and the uploaded YouTube receipt.")
""",
    )


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
    env = {**os.environ, "PDS_STUB_CAPTURE": str(capture)}
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
    assert 'exactly like "## Release hook (0:00 - 0:12)"' in claude_prompt
    assert '"NARRATOR:" on its own line' in claude_prompt
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
    env = {**os.environ, "PDS_STUB_CAPTURE": str(capture)}

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


def test_release_video_publish_requires_youtube_url(tmp_path: Path):
    repo = init_release_repo(tmp_path)
    capture = tmp_path / "pds-capture.json"
    env = {**os.environ, "PDS_STUB_CAPTURE": str(capture)}

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
    env = {**os.environ, "PDS_STUB_CAPTURE": str(capture)}

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
