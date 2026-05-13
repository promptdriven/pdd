# Publication-Safe Evidence Logs

This folder is a reviewed copy of the local whitepaper evidence logs, prepared for external inspection and replication review.

## Included

- `prompts_vibe.md` and `prompts_vibe.jsonl`: recovered developer-typed prompt history from the vibe-coding period.
- `prompts_pdd.md` and `prompts_pdd.jsonl`: recovered developer-typed prompt history from the PDD period.
- `quote_map.md`: Appendix quote mapping to timestamped prompt-history entries.
- `_session_classification.tsv`: session-level classification audit trail.

## Excluded

- Surviving subagent transcripts from `_subagents_REVIEW_BEFORE_PUBLISHING/`; they contained residual credentials, emails, infrastructure identifiers, and unrelated assistant-side research traces.
- Old whitepaper drafts with raw prompt quotes; they are not needed to inspect the study evidence and can create version confusion.
- Original main-session Claude Code JSONL logs; they no longer survived when the evidence bundle was assembled.

## Redactions Applied

- Email addresses.
- API-key, token, JWT, and private-key patterns.
- Local machine paths.
- GCP project identifiers, cloud-console URLs, Firebase web-app URLs, and Firestore user document paths.

This copy still preserves timestamps, session IDs, prompt ordering, GitHub issue/PR URLs, and the distinction between the vibe-coding and PDD periods.

## Integrity Check

`SHA256SUMS.txt` records checksums for the files in this bundle.
