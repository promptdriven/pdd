"""
Issue #1714 — no-progress (stall) watchdog.

The reported failure mode: an interactive Claude run hangs to the full
DEFAULT_TIMEOUT_SECONDS (600 s) producing only TUI spinner escape codes — the
PTY keeps emitting bytes (so it looks "busy") while the session transcript never
grows because no real work is happening. Lowering the hard timeout (the first
round of #1714) only shrinks the wasted budget; it does not *detect* the stall.

This module covers the actual stall detector:
  * the pure decision helper `_stall_watchdog_triggered`,
  * `stall_timeout` plumbing from `run_agentic_task` down to `_run_with_provider`,
  * an end-to-end PTY test proving a spinner-only process whose transcript never
    grows is aborted by the watchdog well before the hard timeout.
"""
from __future__ import annotations

import os
import sys
import time
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_common import (
    DEFAULT_TIMEOUT_SECONDS,
    _stall_watchdog_triggered,
    run_agentic_task,
)


# ---------------------------------------------------------------------------
# Pure decision helper
# ---------------------------------------------------------------------------

class TestStallWatchdogDecision:
    def test_disabled_when_timeout_none(self):
        assert _stall_watchdog_triggered(last_progress_time=0.0, now=10_000.0,
                                         stall_timeout=None) is False

    def test_disabled_when_timeout_non_positive(self):
        assert _stall_watchdog_triggered(0.0, 10_000.0, 0.0) is False
        assert _stall_watchdog_triggered(0.0, 10_000.0, -5.0) is False

    def test_not_triggered_within_window(self):
        # 100 s of quiescence, 180 s window → still healthy.
        assert _stall_watchdog_triggered(last_progress_time=1_000.0,
                                         now=1_100.0, stall_timeout=180.0) is False

    def test_triggered_past_window(self):
        # 200 s of quiescence, 180 s window → stalled.
        assert _stall_watchdog_triggered(last_progress_time=1_000.0,
                                         now=1_200.0, stall_timeout=180.0) is True


# ---------------------------------------------------------------------------
# Plumbing: run_agentic_task -> _run_with_provider
# ---------------------------------------------------------------------------

class TestStallTimeoutPlumbing:
    def test_run_agentic_task_forwards_stall_timeout_to_provider(self, tmp_path):
        """A caller-supplied stall_timeout must reach _run_with_provider so the
        interactive runner can enforce the no-progress watchdog."""
        sentinel = 123.0
        with patch("pdd.agentic_common.get_available_agents", return_value=["anthropic"]), \
             patch("pdd.agentic_common.get_agent_provider_preference",
                   return_value=["anthropic"]), \
             patch("pdd.agentic_common._run_with_provider") as mock_provider, \
             patch("pdd.agentic_common._log_agentic_interaction", return_value=None), \
             patch("pdd.agentic_common._record_pdd_owned_log_signature"):
            mock_provider.return_value = (True, "Done", 0.05, None)

            run_agentic_task(
                instruction="Identify modules",
                cwd=tmp_path,
                label="agentic_sync_identify_modules",
                timeout=400.0,
                stall_timeout=sentinel,
                quiet=True,
            )

        mock_provider.assert_called()
        assert mock_provider.call_args.kwargs.get("stall_timeout") == sentinel, (
            "run_agentic_task must forward stall_timeout= to _run_with_provider "
            f"(issue #1714 no-progress watchdog). Got kwargs={mock_provider.call_args.kwargs}"
        )

    def test_stall_timeout_defaults_to_none(self, tmp_path):
        """Default behaviour is unchanged: no stall_timeout => watchdog off."""
        with patch("pdd.agentic_common.get_available_agents", return_value=["anthropic"]), \
             patch("pdd.agentic_common.get_agent_provider_preference",
                   return_value=["anthropic"]), \
             patch("pdd.agentic_common._run_with_provider") as mock_provider, \
             patch("pdd.agentic_common._log_agentic_interaction", return_value=None), \
             patch("pdd.agentic_common._record_pdd_owned_log_signature"):
            mock_provider.return_value = (True, "Done", 0.05, None)

            run_agentic_task(instruction="x", cwd=tmp_path, label="t",
                             timeout=400.0, quiet=True)

        assert mock_provider.call_args.kwargs.get("stall_timeout") is None


# ---------------------------------------------------------------------------
# End-to-end PTY watchdog
# ---------------------------------------------------------------------------

@pytest.mark.skipif(os.name != "posix", reason="interactive watchdog needs POSIX PTY")
class TestInteractivePtyStallAbort:
    @pytest.fixture(autouse=True)
    def _fast_auth_poll(self, monkeypatch):
        """Shrink the transcript-poll grace/interval so these real-PTY tests run
        in well under a second instead of waiting on the 2 s production grace —
        keeps the issue suite deterministic and fast."""
        monkeypatch.setattr(
            "pdd.agentic_common.INTERACTIVE_AUTH_FASTFAIL_GRACE_SECONDS", 0.1
        )
        monkeypatch.setattr(
            "pdd.agentic_common.INTERACTIVE_AUTH_FASTFAIL_INTERVAL_SECONDS", 0.1
        )

    def test_spinner_only_process_is_aborted_before_hard_timeout(self, tmp_path):
        """A process that floods the PTY with spinner bytes but whose transcript
        never grows must be killed by the no-progress watchdog well before the
        hard `timeout` — proving PTY busy-ness is not mistaken for progress."""
        from pdd.agentic_common import _run_interactive_pty_until_reply

        # A "spinner": writes bytes to the PTY forever, never finishes, never
        # produces a reply file. Models the parked TUI from #1714.
        spinner = [
            sys.executable,
            "-c",
            "import sys, time\n"
            "while True:\n"
            "    sys.stdout.write('\\x1b[2K\\r-'); sys.stdout.flush(); time.sleep(0.02)\n",
        ]
        # A transcript file that exists but never grows (no real progress).
        transcript = tmp_path / "session.jsonl"
        transcript.write_text("", encoding="utf-8")
        reply_path = tmp_path / "reply.json"  # never created

        hard_timeout = 8.0
        stall_timeout = 0.5

        start = time.time()
        with patch("pdd.agentic_common._find_claude_interactive_session_file",
                   return_value=transcript):
            success, message, cost, model = _run_interactive_pty_until_reply(
                spinner,
                cwd=tmp_path,
                env=dict(os.environ),
                timeout=hard_timeout,
                reply_path=reply_path,
                job_id="job",
                session_id="sess",
                stall_timeout=stall_timeout,
            )
        elapsed = time.time() - start

        assert success is False
        assert "stall" in message.lower() or "no transcript progress" in message.lower(), (
            f"expected a no-progress stall message, got: {message!r}"
        )
        # Must abort far sooner than the hard timeout (proves early detection).
        assert elapsed < hard_timeout / 2, (
            f"watchdog took {elapsed:.1f}s; expected abort shortly after "
            f"stall_timeout={stall_timeout}s, well under hard timeout={hard_timeout}s"
        )

    def test_no_stall_timeout_does_not_abort_early(self, tmp_path):
        """With stall_timeout=None the watchdog is off: a short-lived process
        that exits on its own is NOT killed by any no-progress logic."""
        from pdd.agentic_common import _run_interactive_pty_until_reply

        # Exits cleanly after a brief moment without producing a reply.
        quick = [sys.executable, "-c", "import time; time.sleep(0.3)"]
        transcript = tmp_path / "session.jsonl"
        transcript.write_text("", encoding="utf-8")
        reply_path = tmp_path / "reply.json"

        with patch("pdd.agentic_common._find_claude_interactive_session_file",
                   return_value=transcript):
            success, message, _cost, _model = _run_interactive_pty_until_reply(
                quick,
                cwd=tmp_path,
                env=dict(os.environ),
                timeout=10.0,
                reply_path=reply_path,
                job_id="job",
                session_id="sess",
                stall_timeout=None,
            )

        # No reply file → not a success, but the failure must NOT be a stall abort.
        assert success is False
        assert "stall" not in message.lower()

    def test_watchdog_aborts_when_transcript_never_located(self, tmp_path):
        """If an opted-in run cannot locate the session transcript, abort before
        the hard timeout.

        Hosted checkup Step 2 can park in Claude interactive mode before a
        transcript becomes locatable. A caller-supplied ``stall_timeout`` must
        bound that path too; otherwise the watchdog never arms and the job burns
        the full hard step timeout.
        """
        from pdd.agentic_common import _run_interactive_pty_until_reply

        # Spinner-style process: floods the PTY forever, never exits on its own.
        spinner = [
            sys.executable,
            "-c",
            "import sys, time\n"
            "while True:\n"
            "    sys.stdout.write('\\x1b[2K\\r-'); sys.stdout.flush(); time.sleep(0.02)\n",
        ]
        reply_path = tmp_path / "reply.json"  # never created

        hard_timeout = 1.5
        stall_timeout = 0.3

        start = time.time()
        # Session file can NEVER be located -> opted-in watchdog must abort.
        with patch("pdd.agentic_common._find_claude_interactive_session_file",
                   return_value=None):
            success, message, _cost, _model = _run_interactive_pty_until_reply(
                spinner,
                cwd=tmp_path,
                env=dict(os.environ),
                timeout=hard_timeout,
                reply_path=reply_path,
                job_id="job",
                session_id="sess",
                stall_timeout=stall_timeout,
            )
        elapsed = time.time() - start

        assert success is False
        assert "transcript was not located" in message.lower()
        # Must abort far sooner than the hard timeout (proves early detection).
        assert elapsed < hard_timeout / 2, (
            f"watchdog took {elapsed:.1f}s; expected abort shortly after "
            f"stall_timeout={stall_timeout}s, well under hard timeout={hard_timeout}s"
        )

    def test_first_run_theme_then_unsent_positional_task_reaches_mcp_reply(
        self, tmp_path
    ):
        """A current Claude TUI may consume the positional task during its
        first-run theme picker, then leave it in the composer rather than send
        it.  PDD owns this interactive launch, so it must advance the known
        first-run screen and submit the pre-supplied task exactly once.

        This is the hosted failure from staging execution ``pdd-executor-job-
        tccrs`` in miniature: before the task is submitted Claude creates no
        JSONL transcript and cannot call ``pdd_reply``.  A timeout/watchdog
        merely limits waste; it does not make the final-gate reviewer usable.
        """
        from pdd.agentic_common import _run_interactive_pty_until_reply

        reply_path = tmp_path / "reply.json"
        job_id = "theme-positional-job"
        # The fixture intentionally behaves like a new Claude TUI: the first
        # Enter accepts the theme, the second sends the positional task that is
        # visibly sitting in the composer, and only then can it call pdd_reply.
        # It never creates a transcript, matching the affected hosted launch.
        first_run_tui = [
            sys.executable,
            "-u",
            "-c",
            "import json, os, sys, time\n"
            "sys.stdout.write('Text style\\n1. Dark mode\\n2. Light mode\\nEnter to confirm\\n'); sys.stdout.flush()\n"
            "if not sys.stdin.buffer.read(1): raise SystemExit(2)\n"
            f"sys.stdout.write(\"Read the file at prompt.txt and execute it. When finished, call the MCP tool pdd_reply with job_id='{job_id}', success=true or false. Do not stop until pdd_reply has been called successfully. Press Enter to send\\\\n\"); sys.stdout.flush()\n"
            "if not sys.stdin.buffer.read(1): raise SystemExit(3)\n"
            "open(os.environ['PDD_TEST_REPLY_PATH'], 'w').write(json.dumps({'job_id': os.environ['PDD_TEST_JOB_ID'], 'success': True, 'text': 'submitted', 'cost_usd': 0, 'model': 'claude-test'}))\n"
            "time.sleep(10)\n",
        ]

        success, message, cost, model = _run_interactive_pty_until_reply(
            first_run_tui,
            cwd=tmp_path,
            env={
                **os.environ,
                "PDD_TEST_REPLY_PATH": str(reply_path),
                "PDD_TEST_JOB_ID": job_id,
            },
            timeout=1.0,
            reply_path=reply_path,
            job_id=job_id,
            # The exact staging symptom is no transcript at all; this test
            # asserts that PDD unblocks it rather than merely classifying it as
            # a watchdog timeout.
            stall_timeout=None,
        )

        assert success is True, message
        assert message == "submitted"
        assert cost == 0.0
        assert model == "claude-test"

    def test_unstable_composer_gets_bounded_startup_enter(
        self, tmp_path, monkeypatch
    ):
        """Claude's alternate-screen composer can expose only repaint frames.

        Because PDD launched this TUI with its own positional task, a small
        bounded startup Enter retry is safe and necessary even when prompt text
        is not stably recoverable from the PTY stream.
        """
        from pdd import agentic_common

        monkeypatch.setattr(
            agentic_common, "_INTERACTIVE_STARTUP_ENTER_SECONDS", 0.1, raising=False
        )
        monkeypatch.setattr(
            agentic_common, "_INTERACTIVE_STARTUP_ENTER_RETRY_SECONDS", 0.1, raising=False
        )
        monkeypatch.setattr(
            agentic_common, "_INTERACTIVE_STARTUP_ENTER_MAX", 2, raising=False
        )

        reply_path = tmp_path / "reply.json"
        job_id = "unstable-composer-job"
        unstable_tui = [
            sys.executable,
            "-u",
            "-c",
            "import json, os, sys, time\n"
            "sys.stdout.write('\\x1b[2K\\r-'); sys.stdout.flush()\n"
            "if not sys.stdin.buffer.read(1): raise SystemExit(2)\n"
            "open(os.environ['PDD_TEST_REPLY_PATH'], 'w').write(json.dumps({'job_id': os.environ['PDD_TEST_JOB_ID'], 'success': True, 'text': 'submitted', 'cost_usd': 0, 'model': 'claude-test'}))\n"
            "time.sleep(10)\n",
        ]

        success, message, _cost, _model = (
            agentic_common._run_interactive_pty_until_reply(
                unstable_tui,
                cwd=tmp_path,
                env={
                    **os.environ,
                    "PDD_TEST_REPLY_PATH": str(reply_path),
                    "PDD_TEST_JOB_ID": job_id,
                },
                timeout=0.8,
                reply_path=reply_path,
                job_id=job_id,
                stall_timeout=None,
            )
        )

        assert success is True, message
        assert message == "submitted"
