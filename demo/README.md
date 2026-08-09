# Interactive Checkup Demo — issue #1423

Human-verifiable test scenarios for the interactive checkup stack added in
`change/issue-1423`. Exercises `--interactive`, `--apply`, `--dry-run`, and
`--explain` across three diverse prompts.

## Prerequisites

```bash
pip install -e .          # install pdd in editable mode
cd <repo-root>            # run all commands from the repo root
```

## Quick start (CI-safe, no TTY needed)

```bash
bash demo/run_scenarios.sh
```

Expected output:
```
=== Interactive Checkup Demo Scenarios (non-TTY) ===
--- Scenario A: prompt_lint_python ---
[PASS] A1 exit code (exit 2)
[PASS] A1 error message (matched: requires --interactive)
[PASS] A2 exit code (exit 2)
[PASS] A2 TTY guard message (matched: requires a TTY)
[PASS] A3 exit code (exit 0)
[PASS] A3 no findings (matched: No findings)

--- Scenario B: fix_main_python ---
[PASS] B1 exit code (exit 2)
[PASS] B1 TTY guard message (matched: requires a TTY)

--- Scenario C: agentic_change_python ---
[PASS] C1 requires_clarification field present (matched: requires_clarification)
[PASS] C1 findings array present (matched: "findings")
[PASS] C1 snapshot finding detected (matched: snapshot_policy)

=== Results: 9 passed, 0 failed ===
```

---

## Scenario A — `prompt_lint` (flag validation + clean explain)

**Prompt:** `demo/prompts/prompt_lint_python.prompt`  
**Purpose:** verify error paths and the "no findings" clean path.

### A1 — `--apply` without `--interactive` is rejected

```bash
pdd checkup demo/prompts/prompt_lint_python.prompt --apply
```

**Expected (exit 2):**
```
Error: --apply requires --interactive.
```

### A2 — `--interactive` without a TTY fires the TTY guard

```bash
pdd checkup demo/prompts/prompt_lint_python.prompt --interactive < /dev/null
```

**Expected (exit 2):**
```
Error: --interactive requires a TTY (stdin and stdout must be a terminal).
```

### A3 — `--explain` on a clean prompt exits 0 with no findings

```bash
pdd checkup demo/prompts/prompt_lint_python.prompt --explain
```

**Expected (exit 0):**
```
Prompt: .../prompt_lint_python.prompt
Status: PASS
Findings: 0 error(s), 0 warning(s)
No findings.
```

---

## Scenario B — `fix_main` (non-TTY guard + manual interactive preview)

**Prompt:** `demo/prompts/fix_main_python.prompt`  
**Purpose:** confirm the TTY guard fires on a second prompt, then (manually) walk the full preview interactive path.

### B1 — TTY guard on `fix_main` (CI-safe)

```bash
pdd checkup demo/prompts/fix_main_python.prompt --interactive < /dev/null
```

**Expected (exit 2):**
```
Error: --interactive requires a TTY (stdin and stdout must be a terminal).
```

### B2 — Full preview interactive session (manual, requires TTY)

Run this from a real terminal (not a pipe or CI shell):

```bash
pdd checkup demo/prompts/fix_main_python.prompt --interactive --apply --dry-run
```

**What to verify:**
- A numbered menu appears for each finding (or "No findings to present" if clean)
- Selecting **[1] Primary action** or **[2] Alternative** shows a patch preview
- Selecting **[3] Write custom** prompts for free-form text input
- Selecting **[4] Skip** moves to the next finding without recording a patch
- After all menus: a preview summary is printed and **no files are written**
- No `.pdd/backups/` directory is created

---

## Scenario C — `agentic_change` (findings with `requires_clarification`)

**Prompt:** `demo/prompts/agentic_change_python.prompt`  
**Purpose:** show a prompt with real findings and confirm the `requires_clarification` field is present in JSON output.

### C1 — `--explain --json` includes `requires_clarification` in every finding

```bash
pdd checkup demo/prompts/agentic_change_python.prompt --explain --json 2>/dev/null \
  | python -m json.tool
```

**Expected (exit non-zero — snapshot finding present):**
```json
{
    "findings": [
        {
            "code": "snapshot_policy",
            "id": "snapshot:agentic_change_python:0:snapshot_policy",
            "message": "Prompt declares nondeterministic context ...",
            "requires_clarification": false,
            "severity": "error",
            ...
        }
    ]
}
```

Pass criteria: `requires_clarification` key is present on every finding object.

### C2 — Interactive mode surfaces `requires_clarification` findings first (manual, requires TTY)

```bash
pdd checkup demo/prompts/agentic_change_python.prompt --interactive --apply --dry-run
```

**What to verify:**
- Any finding with `"requires_clarification": true` appears at the **top** of the
  menu list before regular findings
- Findings are labelled with their `id` and `message`
- The `--dry-run` flag prevents any file writes even if repairs are approved

---

## Pass/fail criteria summary

| Check | Method | Criteria |
|-------|--------|----------|
| A1 | automated | exit 2, stderr contains "requires --interactive" |
| A2 | automated | exit 2, stderr contains "requires a TTY" |
| A3 | automated | exit 0, stdout contains "No findings" |
| B1 | automated | exit 2, stderr contains "requires a TTY" |
| B2 | manual TTY | menus appear, no files written after --dry-run |
| C1 | automated | JSON contains `requires_clarification` key in findings |
| C2 | manual TTY | clarification findings ordered first; no files written |
