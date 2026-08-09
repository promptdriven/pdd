"""Snapshot record schema (design.md §6.2 tap 1, §6.3).

One ``SnapshotRecord`` per model request captured by the recording proxy.
Records are serialized as JSONL next to the archived request/response payloads
so a third party can re-derive every downstream metric from raw artifacts.
"""

from __future__ import annotations

import dataclasses
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator

SCHEMA_VERSION = 1


@dataclass
class SnapshotRecord:
    """Metadata for one captured model request (a *context snapshot*).

    The byte-exact request/response bodies live at ``payload_path`` /
    ``response_path``; this record carries what analysis needs without
    re-parsing the payloads.
    """

    run_id: str
    ordinal: int  # 1-based request index within the run
    timestamp: float  # epoch seconds when the proxy received the request
    endpoint: str  # request path, e.g. /v1/chat/completions or /v1/responses
    request_sha256: str
    payload_path: str  # archived request body (relative to the archive dir)
    response_path: str | None = None
    status_code: int | None = None
    model: str | None = None
    # Provider-reported usage (authoritative token source; design §6.1).
    input_tokens: int | None = None
    output_tokens: int | None = None
    total_tokens: int | None = None
    # Cheap structural facts extracted at capture time.
    message_count: int | None = None
    request_bytes: int = 0
    response_bytes: int = 0
    tool_call_names: list[str] = field(default_factory=list)
    edit_tool_call: bool = False  # response contains an edit/patch tool call
    streamed: bool = False
    schema_version: int = SCHEMA_VERSION

    def to_json(self) -> str:
        return json.dumps(dataclasses.asdict(self), sort_keys=True)

    @classmethod
    def from_json(cls, line: str) -> "SnapshotRecord":
        data = json.loads(line)
        known = {f.name for f in dataclasses.fields(cls)}
        return cls(**{k: v for k, v in data.items() if k in known})


def write_snapshots(records: Iterable[SnapshotRecord], path: str | Path) -> None:
    """Write records as JSONL (one record per line, sorted keys)."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for record in records:
            fh.write(record.to_json() + "\n")


def read_snapshots(path: str | Path) -> Iterator[SnapshotRecord]:
    """Read records back from JSONL, skipping blank lines."""
    with Path(path).open("r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                yield SnapshotRecord.from_json(line)
