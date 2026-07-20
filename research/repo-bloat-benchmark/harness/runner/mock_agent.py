"""Scripted mock agent + mock model server for no-token pipeline validation.

The design's calibration principle (§6.6): validate every instrumentation and
scoring path end-to-end **without spending model tokens**. The mock agent
drives realistic traffic through the real ``RecordingProxy`` — reading real
files from the materialized variant and surfacing their contents into request
payloads — and then edits the repo according to a scripted *behavior*:

- ``oracle``     — applies the scenario's oracle edit (hidden verifier passes)
- ``wrong_file`` — edits a distractor file instead (wrong-file edit)
- ``noop``       — reads but never edits (hidden verifier keeps failing)

The mock model server plays the provider: scripted tool-call responses with
size-derived ``usage`` so the iteration analyzer sees a realistic growth curve.
"""

from __future__ import annotations

import json
import threading
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path


class MockModelServer:
    """Fake provider: read-tool responses until the agent asks to edit."""

    def __init__(self, host: str = "127.0.0.1", port: int = 0) -> None:
        self.host = host
        self.port = port
        self._server: ThreadingHTTPServer | None = None
        self._thread: threading.Thread | None = None
        self.request_count = 0

    def start(self) -> str:
        server_ref = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, *args):  # noqa: D102
                pass

            def do_POST(self):  # noqa: N802
                length = int(self.headers.get("Content-Length") or 0)
                body = self.rfile.read(length)
                server_ref.request_count += 1
                try:
                    payload = json.loads(body)
                except json.JSONDecodeError:
                    payload = {}
                # The mock agent states its intent in the last message.
                messages = payload.get("messages") or []
                last = str(messages[-1].get("content", "")) if messages else ""
                if "INTENT: edit" in last:
                    tool = {"function": {"name": "apply_patch"}}
                elif "INTENT: done" in last:
                    tool = None
                else:
                    tool = {"function": {"name": "read_file"}}
                message: dict = {"role": "assistant", "content": "ok"}
                if tool:
                    message["tool_calls"] = [tool]
                response = {
                    "id": f"mock-{server_ref.request_count}",
                    "model": payload.get("model", "mock-model"),
                    "choices": [{"message": message}],
                    "usage": {
                        # Size-derived so context growth mirrors payload growth.
                        "prompt_tokens": max(1, len(body) // 4),
                        "completion_tokens": 20,
                        "total_tokens": max(1, len(body) // 4) + 20,
                    },
                }
                out = json.dumps(response).encode()
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(out)))
                self.end_headers()
                self.wfile.write(out)

        self._server = ThreadingHTTPServer((self.host, self.port), Handler)
        self.port = self._server.server_address[1]
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()
        return f"http://{self.host}:{self.port}"

    def stop(self) -> None:
        if self._server:
            self._server.shutdown()
            self._server.server_close()
            self._server = None
        if self._thread:
            self._thread.join(timeout=5)
            self._thread = None


class MockAgent:
    """Scripted client that behaves like a (very predictable) coding agent."""

    def __init__(
        self,
        proxy_base_url: str,
        workdir: str | Path,
        behavior: str = "oracle",
        files_to_read: list[str] | None = None,
        oracle_edit: dict | None = None,
        wrong_file: str | None = None,
        model: str = "mock-model",
    ) -> None:
        self.proxy_base_url = proxy_base_url.rstrip("/")
        self.workdir = Path(workdir)
        self.behavior = behavior
        self.files_to_read = files_to_read or []
        self.oracle_edit = oracle_edit or {}
        self.wrong_file = wrong_file
        self.model = model
        self._messages: list[dict] = [
            {"role": "system", "content": "You are a code-patching agent."},
        ]

    def _post(self, content: str) -> dict:
        self._messages.append({"role": "user", "content": content})
        body = json.dumps({"model": self.model, "messages": self._messages}).encode()
        request = urllib.request.Request(
            f"{self.proxy_base_url}/v1/chat/completions",
            data=body,
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(request, timeout=30) as resp:
            return json.loads(resp.read())

    def run(self, task_brief: str = "fix the bug") -> None:
        self._post(f"TASK: {task_brief}")
        # Localization phase: surface real file contents into the context.
        for rel in self.files_to_read:
            path = self.workdir / rel
            content = path.read_text(encoding="utf-8", errors="replace")
            self._messages.append(
                {"role": "tool", "content": f"read_file({rel}):\n{content}"}
            )
            self._post(f"I read {rel}; continuing localization.")
        # Edit phase.
        if self.behavior == "oracle":
            self._post("INTENT: edit — applying the fix to the target file.")
            self._apply_oracle_edit()
        elif self.behavior == "wrong_file":
            self._post("INTENT: edit — applying a fix.")
            self._apply_wrong_file_edit()
        # noop: never edits.
        self._post("INTENT: done")

    def _apply_oracle_edit(self) -> None:
        target = self.workdir / self.oracle_edit["file"]
        source = target.read_text(encoding="utf-8")
        old, new = self.oracle_edit["old"], self.oracle_edit["new"]
        if old not in source:
            raise AssertionError(f"oracle edit anchor not found in {target}")
        target.write_text(source.replace(old, new), encoding="utf-8")

    def _apply_wrong_file_edit(self) -> None:
        if not self.wrong_file:
            raise AssertionError("wrong_file behavior needs a wrong_file path")
        path = self.workdir / self.wrong_file
        path.write_text(
            path.read_text(encoding="utf-8") + "\n# hotfix: adjusted rounding\n",
            encoding="utf-8",
        )
