Below is a consolidated **remediation plan** that turns the weaknesses we identified in the `sync_determine_operation` prototype into a production‑grade design.  The items are grouped in the same rough order of risk and impact as the earlier critique, so you can decide where to start if you cannot implement everything at once.

---

## 1  Robust, Re‑entrant Locking Layer

| Goal                                      | Design                                                                                                                                                                                                                                                                                |                                                              |
| ----------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------ |
| **Single writer, but allow nested calls** | Use **file‑descriptor locks** (`fcntl`/`msvcrt`/`flock`) instead of ad‑hoc PID files.  Create the lock file with \`O\_CREAT                                                                                                                                                           |  O\_EXCL\` to guarantee atomicity, then lock the descriptor. |
| **Avoid PID‑reuse hazards**               | The lock payload is a JSON blob: `{ "pid": 1234, "started": "2025‑06‑11T15:01:22Z", "ppid": 263 }` plus a SHA‑256 of the `sync` executable.  On acquisition, verify that (a) the PID is still running **and** (b) its executable hash matches—if either test fails the lock is stale. |                                                              |
| **Re‑entrancy**                           | Permit a process that already owns the lock to acquire it again (nesting).  Maintain a **reference count** in an in‑memory table keyed by `(basename, language)`.                                                                                                                     |                                                              |
| **Timeout / keep‑alive**                  | Update a `heartbeat` timestamp in the lock file every 30 s.  A second process may steal the lock if `now() – heartbeat > max(idle, 5 min)`.                                                                                                                                           |                                                              |
| **Automatic cleanup**                     | Use `atexit` + signal handlers (`SIGINT, SIGTERM`) to release locks on normal exit and most crashes.                                                                                                                                                                                  |                                                              |

---

## 2  Authoritative “Last‑Generated” Fingerprint

### Why

Without a frozen baseline of *exactly* what the generator produced, the decision engine cannot distinguish a legitimate manual edit from an uncommitted regeneration, leading to false “update” or “generate” cycles.

### How

1. **Commit adjunct** – Every successful `generate`, `fix`, or `update` writes a side‑car file
   `.pdd/meta/<basename>_<lang>.json`:

   ```json
   {
     "pdd_version": "0.0.40",
     "timestamp": "2025‑06‑11T15:04:00Z",
     "prompt_hash": "e6de…",
     "code_hash":   "87b1…",
     "example_hash":"90ce…",
     "test_hash":   "faba…",
     "command": "generate --incremental"
   }
   ```
2. **Store in git** – Add the meta file to the same commit as the generated artefacts.  Now `HEAD` always contains the last *machine* output even if the user regenerated locally and forgot to commit.
3. **Hash instead of mtime** – The sync detector now computes current file hashes and does a **direct set comparison** with the meta file.  This removes all reliance on timestamps, eliminating problems with rebases, check‑outs, and ZIP uploads.

---

## 3  Deterministic Conflict‑Resolution Strategy

| Problem                      | Solution                                                                                                                                                                                                                                                   |
| ---------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| *LLM nondeterminism*         | 1) Freeze model (`provider/model@sha256`), 2) Set `temperature=0`, 3) Hash the **formatted prompt** to create a **cache key**; cache the JSON response in `.pdd/cache/analysis/<hash>.json`.  Anyone re‑running the same analysis obtains the same result. |
| *Expensive on trivial edits* | Add a cheap “syntactic diff” pass; invoke the LLM only if ≥2 files change **and** the change magnitude is above a threshold (e.g. 50 symbol additions/removals).                                                                                           |
| *Low confidence*             | Require `confidence ≥ 0.8` **and** the JSON schema to validate against a local `jsonschema` spec before executing the plan; otherwise drop to **manual‑merge mode** (see § 7).                                                                             |

---

## 4  Runtime & Test Signals Folded into Decision Engine

1. After each `crash`, `verify`, or `pytest` invocation, write a **run report** to `.pdd/meta/<basename>_<lang>_run.json`:

   ```json
   {
     "timestamp": "2025‑06‑11T15:33:10Z",
     "exit_code": 0,
     "tests_passed": 57,
     "tests_failed": 0,
     "coverage": 91.3
   }
   ```
2. The next `sync` reads this file first.
   \* If `exit_code ≠ 0` → recommend `crash`.
   \* If `tests_failed > 0` → recommend `fix`.
   \* If `coverage < target` → recommend `test`.

This closes the loop between *observed executable health* and the high‑level workflow.

---

## 5  Safety Nets for Destructive Operations

| Measure                                        | Details                                                                                                                                                                                                                       |
| ---------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Safety branch**                              | Before any operation that may overwrite user‑modified code (`generate`, `update`, `fix`), create `pdd/safety/<timestamp>` branch and commit current files.  A single `git reset --hard pdd/safety/*` fully restores the repo. |
| **3‑way merge instead of wholesale overwrite** | Ask the generator to produce a patch **against** the last‑generated baseline (see § 2).  Apply with `git apply --3way`; if the patch does not apply cleanly, drop to manual merge.                                            |
| **Protected zones in code**                    | Support `# <pdd-keep>` … `# </pdd-keep>` blocks that the generator must not overwrite.  During code synthesis, insert the previous block verbatim.                                                                            |

---

## 6  Cross‑Unit Dependency Awareness

1. Maintain a lightweight DAG in `.pdd/meta/dependency_graph.json` mapping *prompt → prompts imported in its example* (populated by `auto‑deps`).
2. When a prompt regenerates and its **public interface** (example) hash changes, enqueue downstream prompts for re‑sync.
3. Provide `pdd sync --all-affected BASENAME` to recursively walk the DAG and update dependants in topological order, **re‑using the same file lock** to avoid dead‑locks.

---

## 7  Fallback Manual‑Merge Wizard

If automatic analysis fails (`confidence < 0.8`, JSON invalid, or 3‑way merge conflict):

```
pdd sync BASENAME --interactive
```

1. Presents a TUI (Textual, rich) diff of prompt / code / test.
2. User can accept, reject, or edit each hunk.
3. On save, wizard writes the merged artefacts and **updates the fingerprint** (§ 2) so future syncs resume normally.

This avoids losing developer intent while still keeping “prompt as source‑of‑truth”.

---

## 8  Git Integration Hardening

* Use `git status --porcelain=2 -z` and rigorous parsing to separate **staged**, **unstaged**, **untracked**.
* Follow renames with `git diff --name-status --find-renames`.
* Detect **sparse‑checkout** by checking `.git/info/sparse-checkout` and fall back to work‑tree only if file not in index.
* In non‑git directories, deliberately **degrade** to “hash‑only” mode and emit a warning banner.

---

## 9  Observability & House‑Keeping

| Feature                                     | Rationale                                                                                                 |
| ------------------------------------------- | --------------------------------------------------------------------------------------------------------- |
| **`pdd sync --log` pagination & filtering** | Show last N sync sessions, human‑readable summary (`rich.table`) first, with `--json` to dump raw detail. |
| **Log retention**                           | Keep 30 days by default or `PDD_LOG_TTL`; older files pruned by background thread.                        |
| **Secret redaction**                        | Apply regex filter before writing any prompt/code into logs (`API_KEY`, `PASSWORD`, etc.).                |

---

## 10  Platform‑Portability Fixes

* Use `psutil.pid_exists(pid)` instead of `/proc`.
* Lock‑file directory is `%LOCALAPPDATA%\pdd\locks` on Windows, `$XDG_RUNTIME_DIR/pdd/locks` on POSIX.
* File‑extension maps live in `languages.yaml`; add `cpp,hpp,ts,tsx,rs,...` so the detector handles multi‑file units.

---

## Putting It All Together – Revised Decision Algorithm

```text
Acquire FD lock  ─┐
                  │
Read meta file    │──┐  (baseline fingerprints)
Hash current files│  │
Compare           │  │
                  │  ├─► If fingerprints equal and last run OK → DONE
                  │  │
Analyse deltas    │  │
  ├─ Single file?─┘  │──► simple heuristic
  └─ ≥2 files?  ─────┘
          │
          ├─ change magnitude < T?  → heuristic
          └─ otherwise → LLM analysis (deterministic, cached)
Apply plan
            ├─ needs code write? → create safety branch + 3‑way merge
            ├─ needs execution? → run crash/pytest; write run-report
            └─ needs downstream? → push to dependency queue
Update meta fingerprints
Release lock
```

This pipeline **never relies on timestamps**, is safe against concurrent executions, preserves manual edits, and remains deterministic & auditable—while still falling back gracefully when an edge case escapes automation.

---

### Incremental Adoption Path

| Phase                                     | What you get                                      | Effort            |
| ----------------------------------------- | ------------------------------------------------- | ----------------- |
| **1. Fingerprint + FD lock**              | Eliminates most false positives & race conditions | Medium (1‑2 days) |
| **2. Safety branch + 3‑way merge**        | Stops destructive overwrites                      | Medium            |
| **3. Runtime/test telemetry integration** | “fix” recommendations become accurate             | Medium            |
| **4. Deterministic LLM cache**            | Stable CI runs, cost drop                         | Low               |
| **5. Dependency DAG & downstream sync**   | True multi‑prompt coherence                       | High              |
| **6. Interactive merge wizard**           | Human‑friendly fallback                           | Low               |

Rolling out in this order gives you the highest risk‑reduction early while deferring the heavier graph & TUI work until the basics are rock solid.

---

## Conclusion

The current heuristic‑only implementation will work on day‑one demos but is fragile in production.  Anchoring sync decisions on **persistent fingerprints**, using **atomic, re‑entrant locks**, and folding **real execution signals** into the decision tree eliminates most mis‑classifications.  Layering deterministic LLM assistance and strong safety nets on top completes a workflow that is both **hands‑off for the happy path** and **recoverable when reality intervenes**—delivering the promise of Prompt‑Driven Development without the foot‑guns.

