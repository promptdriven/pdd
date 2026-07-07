"""Tests for the non-billing Codex routing probe.

The always-on tests drive :func:`run_probe` with a *fake* codex binary — a
tiny script that behaves the way the probe expects the real CLI to behave
(reads the generated config, routes to its base_url, executes the ordered
command locally, writes a session log). That keeps the suite hermetic while
pinning the probe's verdict logic.

The real-binary integration run is opt-in (it invokes whatever ``codex`` is
on PATH — still zero-billing, loopback-only)::

    RB_CODEX_PROBE=1 python3 -m pytest harness/runner/tests/test_codex_probe.py
"""

from __future__ import annotations

import json
import os
import shutil
import stat
import subprocess
import sys
import textwrap

import pytest

from harness.runner.codex_probe import PROBE_MARKER, run_probe

FAKE_VERSION = "codex-cli 0.0.0-fake"


def _write_fake_codex(tmp_path, *, skip_local_exec=False, leak_get=False):
    """A minimal stand-in for the pinned CLI, faithful to probe expectations."""
    script = tmp_path / "fake-codex"
    body = textwrap.dedent(
        f"""\
        #!{sys.executable}
        import json, os, re, sys, urllib.request

        if "--version" in sys.argv:
            print("{FAKE_VERSION}")
            raise SystemExit(0)

        home = os.environ["CODEX_HOME"]
        config = open(os.path.join(home, "config.toml")).read()
        base_url = re.search(r'base_url = "([^"]+)"', config).group(1)
        workdir = sys.argv[sys.argv.index("--cd") + 1]
        key = os.environ.get("OPENAI_API_KEY", "")

        def post(payload):
            req = urllib.request.Request(
                base_url + "/responses",
                data=json.dumps(payload).encode(),
                headers={{"Authorization": "Bearer " + key,
                          "Content-Type": "application/json"}},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=30) as resp:
                return resp.read().decode()

        if {leak_get!r}:
            urllib.request.urlopen(base_url + "/models", timeout=30)

        turn1 = post({{
            "model": re.search(r'^model = "([^"]+)"', config, re.M).group(1),
            "stream": True,
            "tools": [{{"type": "function", "name": "exec_command"}}],
            "input": [{{"type": "message", "role": "user", "content": "probe"}}],
        }})
        call = re.search(r'"call_id": "([^"]+)"', turn1).group(1)
        listing = "" if {skip_local_exec!r} else "\\n".join(os.listdir(workdir))
        post({{
            "model": "fake",
            "stream": True,
            "tools": [{{"type": "function", "name": "exec_command"}}],
            "input": [{{"type": "function_call_output", "call_id": call,
                        "output": listing}}],
        }})
        sessions = os.path.join(home, "sessions", "2026")
        os.makedirs(sessions, exist_ok=True)
        with open(os.path.join(sessions, "rollout-fake.jsonl"), "w") as fh:
            fh.write(json.dumps({{"type": "session_meta"}}) + "\\n")
        print("probe complete")
        """
    )
    script.write_text(body)
    script.chmod(script.stat().st_mode | stat.S_IEXEC)
    return str(script)


def test_probe_confirms_conforming_binary(tmp_path):
    fake = _write_fake_codex(tmp_path)
    verdict = run_probe(codex_binary=fake, work_root=tmp_path / "work")
    assert verdict["checks"] == {name: True for name in verdict["checks"]}
    assert verdict["confirmed"] is True
    assert verdict["pinned_cli_version"] == FAKE_VERSION


def test_probe_fails_when_tool_output_is_not_local(tmp_path):
    fake = _write_fake_codex(tmp_path, skip_local_exec=True)
    verdict = run_probe(codex_binary=fake, work_root=tmp_path / "work")
    assert verdict["checks"]["local_exec_observed"] is False
    assert verdict["confirmed"] is False


def test_probe_fails_on_stray_non_post_traffic(tmp_path):
    fake = _write_fake_codex(tmp_path, leak_get=True)
    verdict = run_probe(codex_binary=fake, work_root=tmp_path / "work")
    assert verdict["checks"]["no_stray_requests"] is False
    assert verdict["confirmed"] is False


@pytest.mark.skipif(
    not os.environ.get("RB_CODEX_PROBE") or shutil.which("codex") is None,
    reason="opt-in: set RB_CODEX_PROBE=1 with a codex binary on PATH "
    "(zero-billing, loopback-only)",
)
def test_probe_confirms_real_pinned_binary(tmp_path):
    verdict = run_probe(work_root=tmp_path / "work")
    assert verdict["confirmed"], json.dumps(verdict, indent=2)
