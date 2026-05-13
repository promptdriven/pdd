"""Example usage of the CI module-detection script.

The canonical implementation lives at ``scripts/ci_detect_changed_modules.py``;
this file mirrors its public surface for ``pdd.ci_detect_changed_modules`` so
the script can be imported from the installed package as well as executed
standalone from the repo. Both expose the same ``detect`` and ``main``
callables; the snippets below use the in-tree script path.

Auto-heal invokes the script with ``--diff-base origin/main...HEAD`` to compute
the basename set that needs healing on a PR. The CLI prints a single comma-
separated line so it can be consumed by ``IFS=, read -r -a`` in a shell loop:

    $ python scripts/ci_detect_changed_modules.py --diff-base origin/main...HEAD
    commands/maintenance,ci_drift_heal

Programmatic callers (other CI scripts or tests) can use ``detect`` directly:

    from importlib.util import spec_from_file_location, module_from_spec
    from pathlib import Path

    script = Path("scripts/ci_detect_changed_modules.py")
    spec = spec_from_file_location("ci_detect_changed_modules", script)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)

    basenames = module.detect("origin/main...HEAD")
    # basenames is a sorted list[str] of PDD module basenames.

Only PDD-managed prefixes (``pdd/``, ``prompts/``, ``context/``, ``tests/``)
are scanned. The detector also resolves reverse dependencies by parsing
``<include>`` and ``<include-many>`` tags in every ``.prompt`` under
``prompts/`` and ``pdd/prompts/``; when an include carries
``select="def:..."``, only changes to those specific Python ``def`` blocks
count as a match (the script AST-diffs the changed file against the
``--diff-base`` revision).

A handful of basenames are excluded so headless auto-heal cannot try to
regenerate operational helpers as if they were PDD development units:

* ``__main__`` — package execution shim.
* ``ci_detect_changed_modules`` and ``scripts/ci_detect_changed_modules`` —
  the detector itself (both the bare-name form and the path-qualified form
  produced when the prompt was located under ``pdd/prompts/scripts/``).
* ``copy_package_data_to_public`` — public-release packaging helper.
* ``generate_model_catalog`` — agent-reviewed manifest-driven module.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


def _load_detector():
    """Load the in-tree CI detector module without installing the package."""
    script_path = Path(__file__).resolve().parents[1] / "scripts" / "ci_detect_changed_modules.py"
    spec = importlib.util.spec_from_file_location(
        "ci_detect_changed_modules_example_loader", script_path
    )
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def show_basename_mapping() -> None:
    """Demonstrate how repo paths map to PDD module basenames."""
    detector = _load_detector()
    samples = [
        "pdd/commands/maintenance.py",
        "pdd/prompts/commands/maintenance_python.prompt",
        "context/commands/maintenance_example.py",
        "tests/commands/test_maintenance.py",
        "pdd/__init__.py",  # excluded: root package shim
        "pdd/ci_detect_changed_modules.py",  # excluded: detector itself
    ]
    for path in samples:
        print(f"{path:55s} -> {detector._basename_from_path(path)!r}")


def show_include_extraction() -> None:
    """Demonstrate <include> / <include-many> parsing, including selectors."""
    detector = _load_detector()
    body = (
        "<include>../api/PromptGenerationResult.ts</include>\n"
        "<include-many>\n"
        "    ./Icon/CheckIcon.tsx\n"
        "    ./Icon/SpinnerIcon.tsx\n"
        "</include-many>\n"
        '<include select="def:foo,def:bar">pdd/helpers.py</include>\n'
    )
    for path, selected_defs in detector._extract_include_refs(body):
        print(f"{path:45s} select={selected_defs}")


def detect_for_diff(diff_base: str) -> list[str]:
    """Wrapper around ``detect`` for callers that want the basename list."""
    detector = _load_detector()
    return detector.detect(diff_base)


if __name__ == "__main__":
    show_basename_mapping()
    print()
    show_include_extraction()
