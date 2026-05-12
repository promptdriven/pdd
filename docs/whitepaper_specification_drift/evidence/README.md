# Evidence bundle for "Why AI Code Falls Apart: A Case Study in Specification Drift"

**Serhan Asad — May 2026**

This bundle is the developer-facing record of the work analyzed in the paper. It accompanies `whitepaper_final.md` and exists so a reader can spot-check the quotes, timestamps, and conduct described there.

---

## What this is (and what it isn't)

**This is:** the developer's own typed prompts to Claude Code during the case study window, plus surviving subagent transcripts, filtered to the autonomous GitHub issue solver feature.

**This is not:** the full Claude Code session logs. Those `.jsonl` files were auto-cleaned by Claude Code's normal retention process some time after the work was completed and before the paper was assembled. **Zero original main-session JSONLs from this window survive on disk.** What you see here is recovered from two adjacent sources:

| Source | What it contains | What it doesn't |
|---|---|---|
| `~/.claude/history.jsonl` | Every prompt the developer typed into Claude Code, with timestamps, session IDs, and project paths | Claude's responses, tool calls, tool results, system reminders, any pasted content beyond the typed text |
| Surviving subagent JSONLs under `~/.claude/projects/<sid>/subagents/` | Full transcripts of subagent invocations spawned during sessions (mostly small-model research/exploration calls) | Only ~32 of 196 feature-relevant sessions have any surviving subagent files; none of the PDD-period subagent directories survive |

The paper's main quoted lines are developer prompts, so the bundle preserves them faithfully. The paper's quantitative claims about *Claude's* behavior (tool calls, message volumes, multi-turn reasoning) cannot be re-verified from this bundle because the assistant-side of the conversations is gone.

---

## What's in this directory

```
evidence/
├── README.md                                       # This file
├── prompts_vibe.md                                 # All vibe-period feature prompts, grouped by vibe day
├── prompts_vibe.jsonl                              # Same data, machine-readable
├── prompts_pdd.md                                  # All PDD-period feature prompts, grouped by PDD day
├── prompts_pdd.jsonl                               # Same data, machine-readable
├── quote_map.md                                    # Every Appendix C quote → exact history.jsonl entry
├── _session_classification.tsv                     # Per-session classification audit trail
└── _subagents_REVIEW_BEFORE_PUBLISHING/            # Quarantined: scrub incomplete (see folder README)
```

The four `prompts_*` files plus `quote_map.md` are the publishable evidence. **The subagent folder is quarantined** because the auto-scrub left residual test passwords and infrastructure identifiers; review or delete it before linking publicly. See the folder's own `README_DO_NOT_PUBLISH_YET.md` for details.

---

## How the feature filter works

The paper's scope is one feature: an autonomous GitHub issue solver for PDD Cloud. The developer was concurrently doing other work during the same calendar window (unrelated repo triage, hackathon work on other projects, etc.). To match the paper's "feature-relevant" framing in Appendix B, this bundle includes only sessions that touched the issue solver.

**Inclusion rule:** a session is included if any of its prompts contains at least one feature keyword (e.g. `pdd-issue`, `issue solver`, `github_pdd_app`, `change-issue-523`, `#659`, `hackathon`, `agentic`, `verifier`, `orchestrator`, `zombie recovery`, `credential rotation`, `secret redaction`, `stop condition`) **or** the working directory points into the feature's worktree.

**Within an included session,** prompts that are clearly off-topic (volunteer portal, admin dashboard, leaderboard, etc.) are dropped at the prompt level.

The full classification — every session ID, score, and the first prompt that led to its classification — is in `_session_classification.tsv` for audit.

---

## How the numbers compare to Table 1 of the paper

| Quantity | Paper | This bundle | Comment |
|---|---:|---:|---|
| Vibe coding window | Mar 4 – Mar 18 | Mar 4 – Mar 18 | Same calendar window |
| PDD window | Mar 19 – Mar 27 | Mar 19 – Mar 27 | Same calendar window |
| Feature-relevant session-log days (vibe) | 9 | 12 days have ≥1 prompt | Paper's "9" used a stricter feature filter |
| Feature-relevant session-log days (PDD) | 9 | 9 | Matches |
| Developer messages (vibe) | 5,553 | 3,048 typed prompts | The paper's count came from the original session JSONLs (now deleted) and likely included pasted contents, command outputs, and tool results that aren't preserved in `history.jsonl`. The direction (vibe > PDD) is preserved. |
| Developer messages (PDD) | 1,504 | 1,237 typed prompts | Same caveat |
| TDD requests (vibe) | 38 | 45 by keyword match | The 7-prompt gap likely comes from the paper counting only one TDD instruction per task window, or applying a stricter feature filter. The day-1 cluster of three TDD requests is exactly preserved. |

The paper-quoted lines in §4.3, §5.1, and Appendix C are all preserved verbatim in `prompts_vibe.md`. Every one maps to a real timestamped entry in `history.jsonl`; see `quote_map.md`.

---

## Privacy and redaction

Before this bundle was written, the source data was scanned for:

- OpenAI API keys (`sk-proj-…`, `sk-…`)
- Anthropic keys (`sk-ant-…`)
- AWS keys (`AKIA…`)
- GitHub personal access tokens (`ghp_…`, `github_pat_…`)
- Google API keys (`AIzaSy…`)

All matches are replaced with `[REDACTED-…-KEY]` placeholders. The replacement count is recorded in the build script. No personal information beyond the developer's own typed prompts is included.

If you spot a secret or other sensitive content that should be redacted, please open an issue or contact the author directly.

---

## What still needs an independent verifier

The bundle supports verification of:
- **The paper's quoted log lines:** every one maps to a real, timestamped `history.jsonl` entry.
- **The developer's prompt cadence and topic flow** during the vibe coding and PDD windows.
- **The shape of the failure mode** as it was experienced from the developer's side.

The bundle does *not* support verification of:
- The exact 5,553 / 1,504 message counts (those came from now-deleted JSONLs).
- The 38 TDD instruction count (filter logic isn't fully reconstructable from this bundle alone).
- Claude's responses, tool calls, or reasoning traces.

For audit of those, the durable record is the public artifacts that don't depend on local files: the merged PR's full commit history, the GitHub issues and comments, and the CI run results. The paper cites those directly.

---

## License and reuse

This bundle is released under the same terms as the paper. The developer's typed prompts are released by the author; subagent transcripts are derivative outputs of the same author's sessions and are released under the same terms.
