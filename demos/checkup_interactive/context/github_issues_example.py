"""Example context payload for the snapshot demo prompt (06_snapshot_candidate).

This stands in for a live `<include query=...>` data source.  Because the prompt
declares nondeterministic context, `pdd checkup snapshot` requires a replayable
snapshot under `.pdd/evidence/` before the prompt is considered reproducible.
"""

EXAMPLE_ISSUES = [
    {"number": 101, "title": "Crash on empty input", "labels": ["bug"]},
    {"number": 102, "title": "Add CSV export", "labels": ["feature-request"]},
]
