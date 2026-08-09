"""Runnable example for ``pdd.failure_classification``.

This module exposes four pure helpers (no I/O, no LLM calls) used by
``fix_error_loop`` and ``agentic_multishot`` to reason about *why* a pytest /
verification run failed:

- ``classify_failure(text: str) -> FailureKind`` — heuristically maps captured
  test output to a :class:`FailureKind`.
- ``extract_failure_signature(text: str) -> str`` — builds a stable, comparable
  signature ("error type + first file:line") so the loop can detect that the
  *same* failure repeated across fix attempts.
- ``failure_classification_hint(kind: FailureKind) -> str`` — a short,
  user-facing explanation for each :class:`FailureKind`.
- ``format_signature_hint(sig: str) -> str`` — formats / truncates a signature
  for console-safe display.

Running this file prints a short demonstration of each helper and exits 0.
"""

import os
import sys

# Make the example runnable regardless of the current working directory.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.failure_classification import (  # noqa: E402
    FailureKind,
    classify_failure,
    extract_failure_signature,
    failure_classification_hint,
    format_signature_hint,
)


def main() -> None:
    """Demonstrate every public helper with representative inputs."""
    # 1. classify_failure: heuristic mapping of captured output -> FailureKind.
    #    Each `sample` is the kind of combined stderr+stdout the fix loop captures.
    samples: dict[str, FailureKind] = {
        "SyntaxError: invalid syntax": FailureKind.SYNTAX_IMPORT,
        "ModuleNotFoundError: No module named 'foo'": FailureKind.SYNTAX_IMPORT,
        "E   AssertionError: assert 1 == 2": FailureKind.ASSERTION_LOGIC,
        "FAILED test_x - Failed: Timeout (>10.0s)": FailureKind.TIMEOUT_FLAKY,
    }

    print("classify_failure:")
    for text, expected in samples.items():
        kind = classify_failure(text)
        status = "OK" if kind is expected else "MISMATCH"
        print(f"  [{status}] {text!r} -> {kind.value}")
    print("")

    # Classification order: timeout/flaky is checked *before* syntax/import, so
    # an incidental "SyntaxError" substring does not beat a real timeout.
    ordered = classify_failure("test timed out after 5s; SyntaxError mentioned in log")
    print("classification order (timeout wins over incidental SyntaxError):")
    print(f"  -> {ordered.value}")
    print("")

    # 2. extract_failure_signature: stable "same failure as last time" key.
    traceback_text = (
        'File "src/foo.py", line 12, in bar\n'
        "    x = 1 +\n"
        "SyntaxError: invalid syntax"
    )
    signature = extract_failure_signature(traceback_text)
    print("extract_failure_signature:")
    print(f"  -> {signature!r}")
    # Empty input yields an empty signature (nothing usable to compare).
    print(f"  empty input -> {extract_failure_signature('')!r}")
    print("")

    # 3. failure_classification_hint: one short, user-facing hint per kind.
    print("failure_classification_hint (all FailureKind values):")
    for kind in FailureKind:
        print(f"  {kind.value}: {failure_classification_hint(kind)}")
    print("")

    # 4. format_signature_hint: console-safe formatting / truncation.
    print("format_signature_hint:")
    print(f"  signature -> {format_signature_hint(signature)}")
    print(f"  empty -> {format_signature_hint('')}")
    long_sig = "X" * 200
    truncated = format_signature_hint(long_sig)
    print(f"  long signature truncated to {len(truncated)} chars (ends '...': "
          f"{truncated.endswith('...')})")


if __name__ == "__main__":
    main()
