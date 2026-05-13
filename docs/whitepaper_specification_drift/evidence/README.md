# Publication-Safe Evidence Logs

This folder contains the publication-safe evidence bundle for the specification drift whitepaper.

The prompt files preserve the developer's original typed wording from the `Context:` field of an intermediate export. Generated instruction scaffolding added during that export has been removed so the prompts read as the original user prompts rather than rewritten task templates.

This bundle supports inspection of the prompt history, quoted process signals, and session classification used by the paper. It does not contain the raw private Claude Code JSONLs, assistant-side tool traces, private branch metadata, or private cloud CI logs, so it should not be treated as a complete reproduction package for every local quantitative observation in the narrative.

## Included

- `prompts_vibe.md` and `prompts_vibe.jsonl`: 2,435 vibe-coding prompt records.
- `prompts_pdd.md` and `prompts_pdd.jsonl`: 1,003 PDD prompt records.
- `quote_map.md`: paper quote mapping to timestamped prompt-history entries.
- `_session_classification.tsv`: session-level classification audit table.
- `SHA256SUMS.txt`: checksums for the evidence files.

## Excluded

- Raw subagent transcripts and assistant-side tool traces.
- Old whitepaper drafts.
- Local private logs and operational material not needed to inspect the case study.
- `.DS_Store` and other local machine metadata.

## Redactions Applied

- Email addresses.
- API-key, token, JWT, and private-key patterns.
- Local machine paths.
- GCP project identifiers, cloud-console URLs, Firebase web-app URLs, and Firestore user document paths.

This copy preserves timestamps, session IDs, prompt ordering, GitHub issue/PR URLs, and the distinction between the vibe-coding and PDD periods.
