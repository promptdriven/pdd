"""Standalone pre-run gates (design §4.1.2 + §6.6) — no model tokens.

The design's pilot checklist requires two gates to pass *before* any model
run, as runnable pre-flights rather than test-suite behavior:

**Oracle-equivalence sweep (§4.1.2).** For every ``(scenario, size)`` on the
ladder: verify the manifest against ``manifests.lock``, materialize the
variant, and assert

1. the hidden tree never entered the variant;
2. the variant's core files are byte-identical to the 1x core (distractor
   placement must not perturb the core — import shadowing / file collision
   guard);
3. baseline invariant: visible tests PASS and the hidden verifier FAILS on
   the seeded bug;
4. oracle invariant: after applying ``oracle_edit``, visible tests PASS and
   the hidden verifier PASSES.

Each cell records the dependency/runtime fingerprint (interpreter version +
platform) used for both verifications, per §4.1.2.

**Instrumentation calibration (§6.6).** Exercises the recording proxy
in-process against fixture upstreams in both provider wire shapes
(Responses SSE — the pinned build's only wire — and plain chat-completions
JSON) and asserts byte-exact payload archival, sha256 fidelity, provider
``usage`` extraction, and tool-call/edit-boundary detection. FS-tap
assertions are N/A while that tier is disabled (``fs_tap_enabled`` false).

Run::

    python3 -m harness.runner.preflight --config experiment.json --json out.json

Exit code 0 iff every gate passes. This is a required gate for pilot runs;
it spends zero model tokens.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import shutil
import subprocess
import sys
import tempfile
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from harness.context_snapshots.proxy import RecordingProxy
from harness.distractors.manifest import load_manifest, verify_lockfile
from harness.runner.cli import load_experiment_config
from harness.runner.variant_builder import materialize_variant


def _runtime_fingerprint() -> dict:
    return {
        "python": sys.version.split()[0],
        "executable": sys.executable,
        "platform": platform.platform(),
    }


def _core_shas(root: Path) -> dict[str, str]:
    return {
        p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(root.rglob("*"))
        if p.is_file()
    }


class _Verifier:
    """Visible/hidden verification against a materialized variant."""

    def __init__(self, scenario_dir: Path, scenario: dict) -> None:
        self.scenario_dir = scenario_dir
        self.scenario = scenario

    def _expand(self, command: list[str], workdir: Path) -> list[str]:
        return [
            part.replace("{workdir}", str(workdir)).replace("{python}", sys.executable)
            for part in command
        ]

    def _run(self, command: list[str], cwd: Path, workdir: Path) -> bool:
        import os

        env = dict(os.environ)
        env["PYTHONPATH"] = str(workdir / "src")
        result = subprocess.run(
            self._expand(command, workdir),
            cwd=str(cwd),
            env=env,
            capture_output=True,
            text=True,
        )
        return result.returncode == 0

    def visible_pass(self, workdir: Path) -> bool:
        return self._run(self.scenario["visible_tests"]["command"], workdir, workdir)

    def hidden_pass(self, workdir: Path) -> bool:
        hidden_dir = self.scenario_dir / self.scenario["hidden_verifier"]["path"]
        return self._run(self.scenario["hidden_verifier"]["command"], hidden_dir, workdir)


def apply_oracle_edit(workdir: Path, oracle_edit: dict) -> None:
    """Apply the registered oracle fix; the target text must occur exactly once."""
    target = workdir / oracle_edit["file"]
    text = target.read_text(encoding="utf-8")
    occurrences = text.count(oracle_edit["old"])
    if occurrences != 1:
        raise RuntimeError(
            f"oracle_edit.old occurs {occurrences}x in {oracle_edit['file']} "
            "(must be exactly 1) — scenario descriptor is stale"
        )
    target.write_text(
        text.replace(oracle_edit["old"], oracle_edit["new"]), encoding="utf-8"
    )


def oracle_equivalence_sweep(
    *,
    scenario_dir: Path,
    distractors_dir: Path,
    sizes: list[int],
    work_root: Path,
) -> dict:
    """Run the §4.1.2 gate over every ladder step; returns a JSON-ready result."""
    scenario = json.loads((scenario_dir / "scenario.json").read_text(encoding="utf-8"))
    scenario_id = scenario["scenario_id"]
    verifier = _Verifier(scenario_dir, scenario)
    hidden_rel = scenario["hidden_verifier"]["path"]
    lock_path = distractors_dir / "manifests.lock"

    cells: list[dict] = []
    reference_core: dict[str, str] | None = None
    core_root = scenario_dir / scenario["core_path"]
    core_names = set(_core_shas(core_root))

    for size in sizes:
        label = f"{size}x"
        cell: dict = {
            "scenario_id": scenario_id,
            "size": label,
            "runtime_fingerprint": _runtime_fingerprint(),
        }
        workdir = work_root / f"preflight-{scenario_id}-{label}"
        if workdir.exists():
            shutil.rmtree(workdir)
        try:
            manifest_path = distractors_dir / "manifests" / f"{scenario_id}.{label}.json"
            cell["manifest_locked"] = verify_lockfile(manifest_path, lock_path)
            if not cell["manifest_locked"]:
                raise RuntimeError(f"{manifest_path.name} not verified by manifests.lock")
            manifest = load_manifest(manifest_path)

            materialize_variant(
                core_root=core_root,
                manifest=manifest,
                destination=workdir,
                pool_root=(
                    scenario_dir / scenario["pool_path"]
                    if scenario.get("pool_path")
                    else None
                ),
                distractors_dir=distractors_dir,
            )

            cell["hidden_tree_absent"] = not (workdir / hidden_rel).exists()
            variant_core = {
                path: sha
                for path, sha in _core_shas(workdir).items()
                if path in core_names
            }
            if reference_core is None:
                reference_core = variant_core
            cell["core_identical_to_1x"] = variant_core == reference_core

            cell["baseline_visible_pass"] = verifier.visible_pass(workdir)
            cell["baseline_hidden_pass"] = verifier.hidden_pass(workdir)

            apply_oracle_edit(workdir, scenario["oracle_edit"])
            cell["oracle_visible_pass"] = verifier.visible_pass(workdir)
            cell["oracle_hidden_pass"] = verifier.hidden_pass(workdir)

            cell["pass"] = (
                cell["hidden_tree_absent"]
                and cell["core_identical_to_1x"]
                and cell["baseline_visible_pass"]
                and not cell["baseline_hidden_pass"]
                and cell["oracle_visible_pass"]
                and cell["oracle_hidden_pass"]
            )
        except Exception as exc:  # a gate failure must be reported, not raised
            cell["error"] = str(exc)
            cell["pass"] = False
        finally:
            if workdir.exists():
                shutil.rmtree(workdir)
        cells.append(cell)

    return {
        "gate": "oracle_equivalence (design §4.1.2)",
        "scenario_id": scenario_id,
        "sizes": [f"{s}x" for s in sizes],
        "cells": cells,
        "pass": bool(cells) and all(c["pass"] for c in cells),
    }


# -- §6.6 instrumentation calibration ----------------------------------------

_RESPONSES_SSE = (
    'event: response.output_item.done\n'
    'data: {"type": "response.output_item.done", "output_index": 0, "item": '
    '{"type": "function_call", "name": "apply_patch", "call_id": "c1", '
    '"arguments": "{}", "status": "completed"}}\n\n'
    'event: response.completed\n'
    'data: {"type": "response.completed", "response": {"id": "r1", '
    '"object": "response", "status": "completed", "output": [], '
    '"usage": {"input_tokens": 321, "output_tokens": 7, "total_tokens": 328}}}\n\n'
).encode()

_CHAT_JSON = json.dumps(
    {
        "id": "c1",
        "object": "chat.completion",
        "choices": [
            {
                "index": 0,
                "message": {
                    "role": "assistant",
                    "content": None,
                    "tool_calls": [
                        {"id": "t1", "type": "function",
                         "function": {"name": "edit_file", "arguments": "{}"}}
                    ],
                },
                "finish_reason": "tool_calls",
            }
        ],
        "usage": {"prompt_tokens": 123, "completion_tokens": 5, "total_tokens": 128},
    }
).encode()


def calibration_gate(work_root: Path) -> dict:
    """§6.6: assert proxy fidelity against fixed fixtures in both wire shapes."""

    class _FixtureUpstream(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, *args) -> None:
            pass

        def do_POST(self) -> None:  # noqa: N802
            self.rfile.read(int(self.headers.get("Content-Length") or 0))
            if self.path.endswith("/responses"):
                body, ctype = _RESPONSES_SSE, "text/event-stream"
            else:
                body, ctype = _CHAT_JSON, "application/json"
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Connection", "close")
            self.end_headers()
            self.wfile.write(body)

    archive = work_root / "calibration"
    if archive.exists():
        shutil.rmtree(archive)
    server = ThreadingHTTPServer(("127.0.0.1", 0), _FixtureUpstream)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    upstream = f"http://127.0.0.1:{server.server_address[1]}"
    proxy = RecordingProxy(
        upstream_base_url=upstream, archive_dir=archive, run_id="calibration"
    )
    proxy_url = proxy.start()

    import urllib.request

    payloads = [
        ("/v1/responses", b'{"model": "calib", "input": [{"role": "user"}]}'),
        ("/v1/chat/completions", b'{"model": "calib", "messages": [{"role": "user"}]}'),
    ]
    try:
        for path, body in payloads:
            request = urllib.request.Request(
                proxy_url + path, data=body,
                headers={"Content-Type": "application/json"}, method="POST",
            )
            with urllib.request.urlopen(request, timeout=30) as resp:
                resp.read()
    finally:
        proxy.stop()
        server.shutdown()
        server.server_close()

    records = sorted(proxy.records, key=lambda r: r.ordinal)
    checks = {
        "one_record_per_request": len(records) == len(payloads),
        "byte_exact_archive": all(
            (archive / r.payload_path).read_bytes() == payloads[i][1]
            for i, r in enumerate(records)
        ),
        "sha256_fidelity": all(
            hashlib.sha256(payloads[i][1]).hexdigest() == r.request_sha256
            for i, r in enumerate(records)
        ),
        "usage_extracted_responses_sse": bool(records) and records[0].input_tokens == 321,
        "usage_extracted_chat_json": len(records) > 1 and records[1].input_tokens == 123,
        "edit_tool_call_detected": all(r.edit_tool_call for r in records),
        "fs_tap_assertions": "n/a (fs_tap_enabled false — tier disabled)",
    }
    return {
        "gate": "instrumentation_calibration (design §6.6)",
        "checks": checks,
        "pass": all(v is True for k, v in checks.items() if isinstance(v, bool)),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, type=Path,
                        help="the experiment config the pilot will run with")
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args(argv)

    run_config, sizes, _trials = load_experiment_config(args.config)
    work_root = Path(tempfile.mkdtemp(prefix="rb-preflight-"))
    try:
        sweep = oracle_equivalence_sweep(
            scenario_dir=run_config.scenario_dir,
            distractors_dir=run_config.distractors_dir,
            sizes=sizes,
            work_root=work_root,
        )
        calibration = calibration_gate(work_root)
    finally:
        shutil.rmtree(work_root, ignore_errors=True)

    result = {
        "gates": [sweep, calibration],
        "pass": sweep["pass"] and calibration["pass"],
    }
    if args.json:
        args.json.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    for gate in result["gates"]:
        print(f"{'PASS' if gate['pass'] else 'FAIL'}  {gate['gate']}")
        for cell in gate.get("cells", []):
            status = "pass" if cell["pass"] else f"FAIL ({cell.get('error', 'invariant')})"
            print(f"       {cell['size']}: {status}")
    print("PREFLIGHT " + ("PASS" if result["pass"] else "FAIL"))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
