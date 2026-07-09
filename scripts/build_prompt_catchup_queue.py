#!/usr/bin/env python3
"""Build the ranked *code-ahead* work queue for the prompt catch-up pass (issue A2).

A "code-ahead" unit is one whose module code (``pdd/<mod>.py``) has a more recent
commit than its prompt (``pdd/prompts/<mod>_python.prompt``): code landed without a
corresponding prompt update, so "regenerate from prompt" would resurrect stale
behavior (doctrine anti-pattern "Prompt Drift"). This script enumerates every
python unit (reusing ``stamp_fingerprints.enumerate_units`` so code/prompt paths
resolve exactly as the fingerprint oracle sees them), then for each computes:

* ``code_last`` / ``prompt_last``: most recent commit author-date (ALL history) of
  the code file and the prompt file. A unit is code-ahead when
  ``code_last > prompt_last``.
* ``days_ahead``: how many days the code leads the prompt.
* churn since ``--since`` (default 2026-04-01), split by what each commit touched:
  - ``churn_lines`` / ``churn_commits``: added+deleted lines / commit count over
    commits that touched the **code but not the prompt** (the drift-producing
    commits). This is the ranking weight.
  - ``prompt_only_commits`` / ``both_commits``: commits touching only the prompt /
    both — surfaced so a reviewer can spot units whose prompt was ALSO edited
    independently (``conflict_risk``: ``pdd update`` there could clobber a
    deliberate prompt change; do not auto-update).
* ``code_loc``: current line count of the code file (pilot-size filter).

Ranked by (churn_lines, days_ahead, churn_commits) descending. Output JSON is the
committed work-queue artifact (``scripts/prompt_catchup_queue.json``). Stdlib only,
no ``pdd`` import, no LLM.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
sys.path.insert(0, str(SCRIPTS_DIR))

import stamp_fingerprints as sf  # noqa: E402  (stdlib-only, no side effects)

DEFAULT_SINCE = "2026-04-01"


def _git(args: List[str]) -> str:
    """Run a read-only git command in the repo, returning stdout."""
    out = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        capture_output=True,
        text=True,
        check=False,
    )
    return out.stdout or ""


def _rel(path: Path) -> str:
    """Repo-relative POSIX path for a file under the repo root."""
    return path.resolve().relative_to(REPO_ROOT).as_posix()


def _normalize_numstat_path(field: str) -> str:
    """Normalize a --numstat path field, resolving git rename syntax to the new path.

    Handles both ``old => new`` and ``dir/{old => new}/leaf`` forms so churn lands
    on the current path. Binary files show ``-`` counts and are handled by callers.
    """
    field = field.strip()
    if "=>" not in field:
        return field
    if "{" in field and "}" in field:
        pre = field[: field.index("{")]
        inner = field[field.index("{") + 1 : field.index("}")]
        post = field[field.index("}") + 1 :]
        new = inner.split("=>")[-1].strip()
        return (pre + new + post).replace("//", "/")
    return field.split("=>")[-1].strip()


def load_window_commits(since: str) -> Tuple[Dict[str, List[dict]], Dict[str, set]]:
    """Parse one ``git log --numstat`` pass over the window.

    Returns ``(by_file, commit_files)`` where ``by_file[path]`` is a list of
    ``{sha, date, added, deleted}`` for every commit in ``[since, now]`` that
    touched ``path``, and ``commit_files[sha]`` is the set of paths that commit
    touched. Author date (``%aI``) is used throughout.
    """
    raw = _git(
        [
            "log",
            f"--since={since}T00:00:00",
            "--no-merges",
            "--numstat",
            "--date=iso-strict",
            "--format=@@C@@%H|%aI",
        ]
    )
    by_file: Dict[str, List[dict]] = {}
    commit_files: Dict[str, set] = {}
    sha = ""
    date = ""
    for line in raw.splitlines():
        if line.startswith("@@C@@"):
            sha, date = line[len("@@C@@") :].split("|", 1)
            commit_files.setdefault(sha, set())
            continue
        if not line.strip() or not sha:
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        added_s, deleted_s, path_field = parts
        path = _normalize_numstat_path(path_field)
        added = 0 if added_s == "-" else int(added_s)
        deleted = 0 if deleted_s == "-" else int(deleted_s)
        by_file.setdefault(path, []).append(
            {"sha": sha, "date": date, "added": added, "deleted": deleted}
        )
        commit_files[sha].add(path)
    return by_file, commit_files


def load_last_commit_dates(targets: set) -> Dict[str, str]:
    """Most-recent commit author-date (ALL history) for each path in ``targets``.

    One reverse-chronological ``git log --name-only`` pass; the first time a path
    appears is its most recent commit. Stops early once every target is found.
    """
    raw = _git(["log", "--name-status", "--date=iso-strict", "--format=@@C@@%aI"])
    last: Dict[str, str] = {}
    remaining = set(targets)
    date = ""
    for line in raw.splitlines():
        if line.startswith("@@C@@"):
            date = line[len("@@C@@") :].strip()
            continue
        if not line.strip() or not remaining:
            continue
        # name-status rows: "M\tpath" or "R100\told\tnew"; take the last field.
        parts = line.split("\t")
        path = _normalize_numstat_path(parts[-1])
        if path in remaining:
            last[path] = date
            remaining.discard(path)
            if not remaining:
                break
    return last


def _iso_date(s: Optional[str]) -> Optional[datetime]:
    if not s:
        return None
    try:
        return datetime.fromisoformat(s)
    except ValueError:
        return None


def prompt_last_is_standalone(
    prompt_commits: List[dict], code_rel: str, commit_files: Dict[str, set]
) -> bool:
    """True when the prompt's most recent (non-merge, in-window) commit did NOT touch code.

    For a code-ahead unit this is the precise conflict signal: the current prompt
    state came from a standalone prompt edit never reconciled with code via a joint
    commit, so ``pdd update`` (code -> prompt) could clobber deliberate prompt
    intent. If the prompt's last commit also touched the code (a proper joint sync)
    the divergence is pure staleness and safe to back-propagate.

    Uses the pathspec-free ``commit_files`` map (full file set per commit) built by
    ``load_window_commits`` -- a per-unit ``git log -- <prompt>`` cannot be used
    because the pathspec filters ``--name-only`` down to just the prompt, hiding the
    code file. Returns False when the prompt has no in-window commits (pure
    staleness: the prompt has not been touched since the window start).
    """
    if not prompt_commits:
        return False
    latest = max(prompt_commits, key=lambda c: c["date"])
    return code_rel not in commit_files.get(latest["sha"], set())


def _code_loc(path: Path) -> Optional[int]:
    try:
        return sum(1 for _ in path.open("r", encoding="utf-8", errors="ignore"))
    except OSError:
        return None


def build_queue(since: str) -> dict:
    units = sf.enumerate_units()
    by_file, commit_files = load_window_commits(since)

    targets: set = set()
    resolved: List[Tuple[sf.Unit, str, str]] = []
    for unit in units:
        if not unit.prompt.exists() or not unit.code.exists():
            continue
        code_rel = _rel(unit.code)
        prompt_rel = _rel(unit.prompt)
        targets.add(code_rel)
        targets.add(prompt_rel)
        resolved.append((unit, code_rel, prompt_rel))

    last_dates = load_last_commit_dates(targets)

    rows: List[dict] = []
    for unit, code_rel, prompt_rel in resolved:
        code_last = last_dates.get(code_rel)
        prompt_last = last_dates.get(prompt_rel)
        cd = _iso_date(code_last)
        pd = _iso_date(prompt_last)
        code_ahead = bool(cd and (pd is None or cd > pd))
        days_ahead = round((cd - pd).total_seconds() / 86400.0, 2) if (cd and pd) else None

        code_commits = by_file.get(code_rel, [])
        churn_lines = 0
        churn_commits = 0
        both_commits = 0
        last_code_only_date: Optional[str] = None
        for c in code_commits:
            touched_prompt = prompt_rel in commit_files.get(c["sha"], set())
            if touched_prompt:
                both_commits += 1
            else:
                churn_commits += 1
                churn_lines += c["added"] + c["deleted"]
                if last_code_only_date is None or c["date"] > last_code_only_date:
                    last_code_only_date = c["date"]

        prompt_commits = by_file.get(prompt_rel, [])
        prompt_only_commits = sum(
            1 for c in prompt_commits if code_rel not in commit_files.get(c["sha"], set())
        )
        last_prompt_only_date: Optional[str] = None
        for c in prompt_commits:
            if code_rel not in commit_files.get(c["sha"], set()):
                if last_prompt_only_date is None or c["date"] > last_prompt_only_date:
                    last_prompt_only_date = c["date"]

        # Conflict risk: the prompt's most recent commit was a standalone prompt
        # edit (touched prompt, not code) never reconciled with code by a joint
        # commit -- a deliberate prompt change `pdd update` could overwrite.
        # Reviewer must inspect before running update; flagged, never auto-updated.
        # Only computed for code-ahead units (the update candidates).
        conflict_risk = code_ahead and prompt_last_is_standalone(
            prompt_commits, code_rel, commit_files
        )

        rows.append(
            {
                "basename": unit.basename,
                "code": code_rel,
                "prompt": prompt_rel,
                "meta": _rel(unit.meta) if unit.meta.exists() else None,
                "code_last": code_last,
                "prompt_last": prompt_last,
                "code_ahead": code_ahead,
                "days_ahead": days_ahead,
                "churn_lines": churn_lines,
                "churn_commits": churn_commits,
                "both_commits": both_commits,
                "prompt_only_commits": prompt_only_commits,
                "last_code_only_date": last_code_only_date,
                "last_prompt_only_date": last_prompt_only_date,
                "conflict_risk": conflict_risk,
                "code_loc": _code_loc(unit.code),
            }
        )

    ahead = [r for r in rows if r["code_ahead"]]
    ahead.sort(
        key=lambda r: (r["churn_lines"], r["days_ahead"] or 0, r["churn_commits"]),
        reverse=True,
    )
    for i, r in enumerate(ahead, 1):
        r["rank"] = i

    total_units = len(rows)
    ahead_with_churn = [r for r in ahead if r["churn_lines"] > 0]
    return {
        "generated_at": datetime.now().astimezone().isoformat(),
        "since": since,
        "generator": "scripts/build_prompt_catchup_queue.py",
        "definition": (
            "code_ahead = code_last commit newer than prompt_last commit (all "
            "history). churn_lines = added+deleted on the code file over commits "
            "since `since` that touched code but NOT the prompt (drift commits). "
            "Ranked by (churn_lines, days_ahead, churn_commits) desc."
        ),
        "stats": {
            "total_python_units": total_units,
            "code_ahead_units": len(ahead),
            "code_ahead_with_window_churn": len(ahead_with_churn),
            "conflict_risk_units": sum(1 for r in ahead if r["conflict_risk"]),
        },
        "queue": ahead,
    }


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--since", default=DEFAULT_SINCE, help="Churn window start (YYYY-MM-DD).")
    parser.add_argument(
        "--output",
        default=str(SCRIPTS_DIR / "prompt_catchup_queue.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args(argv)
    data = build_queue(args.since)
    Path(args.output).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    s = data["stats"]
    print(
        f"wrote {args.output}: {s['code_ahead_units']} code-ahead / "
        f"{s['total_python_units']} units "
        f"({s['code_ahead_with_window_churn']} with window churn, "
        f"{s['conflict_risk_units']} conflict-risk)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
