"""Minimal local example for :mod:`pdd.fingerprint_transaction`."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

from pdd.fingerprint_transaction import FingerprintTransaction


def run_fingerprint_transaction_example() -> dict[str, object]:
    """Finalize a tiny unit and return its persisted fingerprint payload."""

    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        (root / ".pddrc").write_text("{}", encoding="utf-8")
        prompt = root / "prompts" / "hello_python.prompt"
        code = root / "src" / "hello.py"
        prompt.parent.mkdir(parents=True)
        code.parent.mkdir(parents=True)
        prompt.write_text("Write a hello function.\n", encoding="utf-8")
        code.write_text("def hello(): return 'hello'\n", encoding="utf-8")

        with FingerprintTransaction(
            "hello",
            "python",
            "generate",
            paths={"prompt": prompt, "code": code},
        ) as transaction:
            destination = transaction.fingerprint_path

        return json.loads(destination.read_text(encoding="utf-8"))


if __name__ == "__main__":
    payload = run_fingerprint_transaction_example()
    print(payload["command"], payload["prompt_hash"], payload["code_hash"])
