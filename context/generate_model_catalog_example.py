#!/usr/bin/env python3
"""Example usage for pdd.generate_model_catalog.

The catalog refresh is intentionally manifest-driven:

1. A PDD agent reviews current public Arena sources and records scores,
   source policy, aliases, and provenance in ``pdd/data/arena_elo_manifest.json``.
2. This Python module deterministically validates that manifest, combines it
   with local ``litellm.model_cost`` metadata, and writes ``llm_model.csv``.
3. If the manifest is missing or malformed, generation still succeeds via
   ``STATIC_ELO_FALLBACK`` for known/local models.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

from pdd.generate_model_catalog import (
    AGENTIC_ELO_MANIFEST_PATH,
    AGENTIC_ELO_MANIFEST_SCHEMA_VERSION,
    build_rows,
    _fetch_arena_elo,
    _get_elo,
)


print("1) Load the checked-in agentic score manifest")
index = _fetch_arena_elo()
print(f"   manifest: {AGENTIC_ELO_MANIFEST_PATH}")
print(f"   reviewed aliases: {len(index)}")
print()


print("2) Resolve a reviewed score")
elo, source = _get_elo("gpt-5.2-codex", index)
print(f"   gpt-5.2-codex -> {elo} ({source})")
print()


print("3) Build catalog rows deterministically")
rows = build_rows()
print(f"   rows: {len(rows)}")
print(f"   first row: {rows[0]['provider']} / {rows[0]['model']} / {rows[0]['coding_arena_elo']}")
print()


print("4) Fallback still works with a missing manifest")
missing_index = _fetch_arena_elo(manifest_path=Path("/tmp/does-not-exist.json"))
fallback_elo, fallback_source = _get_elo("gpt-4.1", missing_index)
print(f"   gpt-4.1 -> {fallback_elo} ({fallback_source})")
print()


print("5) CLI with a custom manifest")
with tempfile.TemporaryDirectory() as tmp:
    tmp_path = Path(tmp)
    manifest = tmp_path / "arena_elo_manifest.json"
    output = tmp_path / "llm_model.csv"
    manifest.write_text(
        json.dumps(
            {
                "schema_version": AGENTIC_ELO_MANIFEST_SCHEMA_VERSION,
                "policy": {"summary": "example"},
                "scores": [
                    {
                        "model": "gpt-5",
                        "elo": 1393,
                        "source": "agent-reviewed:example",
                        "source_url": "https://example.test/lmarena",
                        "raw_model_name": "gpt-5-medium",
                        "leaderboard": "webdev",
                        "category": "overall",
                        "leaderboard_publish_date": "2026-04-28",
                        "retrieved_at": "2026-04-29",
                        "rank": 32,
                        "rating": 1393.3335026814395,
                        "rating_lower": 1380.6263607751337,
                        "rating_upper": 1406.0406445877456,
                        "vote_count": 3755,
                        "match_reason": "example reviewed alias",
                    }
                ],
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    cmd = [
        sys.executable,
        "-m",
        "pdd.generate_model_catalog",
        "--score-manifest",
        str(manifest),
        "--output",
        str(output),
    ]
    result = subprocess.run(cmd, check=True, capture_output=True, text=True)
    print("   command:", " ".join(cmd))
    print("   output exists:", output.exists())
    print("   stdout first line:", result.stdout.splitlines()[0])
