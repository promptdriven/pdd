# Reporter-environment verification

This is a design note for discussion of [issue #3013](https://github.com/promptdriven/pdd/issues/3013). The scope and access are pending agreement;
pdd does not implement this proposal. It does not authorize a worker, connection,
invitation or prototype. Participation by a reporter is optional.

## The problem

Some reports depend on an environment that a maintainer cannot reproduce locally.
A candidate fix may pass local checks while its effect in that environment remains
unknown. A reporter might be away while an online agent is authorized to act, or
the environment might be offline. Those are different states: neither availability
nor authorization should be inferred from the other.

## Proposed handoff

1. A maintainer reviews the issue and identifies the exact reproduction action,
   expected result and minimal environment details needed. The reporter chooses
   whether to participate and what evidence can be shared.
2. Before any access, the reporter explicitly grants a narrow, revocable scope for
   a named actor and environment. It names permitted actions and data, duration,
   and how to stop and revoke access. Separate consent is needed for actions or
   data outside that scope. The connection initiator and controller remain open
   decisions for the Link owner.
3. If an authorized agent is online, the agreed actor performs only the agreed
   reproduction action and records the observed result. A reporter being away
   does not itself grant authority. If the environment is offline, unavailable,
   or consent is absent or revoked, stop remote work and record that status.
4. Prepare a candidate in an isolated checkout or preview that protects the
   reporter's active work. Agree how it is selected, identified, started and
   removed before use. Do not alter the active checkout or working data as an
   incidental part of verification.
5. With applicable consent still in force, repeat the exact agreed action on the
   identified candidate and record the result. The reporter or authorized agent
   reviews evidence for secrets, personal information and unrelated material
   before any issue update; share only approved, sanitized references.
6. Maintainers can run local checks and prepare a PR when access is absent.
   Report local results and PR readiness separately from reporter-environment
   validation, which remains pending or unavailable until actually performed.

Link's ability to provide reverse control has not been established. This note
does not assume a connection method, availability or security guarantee. Runtime
repairs remain with Ishaan; this proposal concerns evidence for a candidate.

## Candidate evidence record

The following is illustrative, not a schema or an implementation decision. A
record should make the reproduction and retest distinguishable and reviewable:

| Item | Example content |
| --- | --- |
| Issue and phase | Issue reference; reproduction or candidate retest |
| Actor and authority | Named actor; reference to the consent scope in effect |
| Exact action | Steps actually performed and permitted data used |
| Build identity | Base or candidate revision and how the running build was identified |
| Environment | Relevant, approved environment details and availability |
| Result | Expected and actual observations, including failures or uncertainty |
| Time and status | Timestamps and completed, pending, unavailable or revoked status |
| Artifacts | Reviewed, sanitized references and who approved their sharing |

Avoid placing credentials, private working data or unreviewed output in the
issue. Revocation stops further actions; retention and removal of previously
approved evidence need agreement.

## Decisions for discussion

| Participant | Decisions to agree |
| --- | --- |
| Link owner | Whether the needed control exists; who initiates and controls a connection; how scope, expiry and revocation are enforced and verified |
| PDD maintainers | How a candidate is isolated and identified; who performs actions; how results, evidence review, retention and offline status are recorded |
| Reporters | Whether to participate; which environment, actions and data are permitted; who may act while they are away; what evidence may be shared and how to revoke |

These are questions for the participants, not decisions already made.
[Build identity work #2743](https://github.com/promptdriven/pdd/issues/2743) and
[repo-local repeatable verification proposal #3012](https://github.com/promptdriven/pdd/issues/3012)
are related discussions; neither is assumed to implement this proposal.

## Acceptance for a later prototype

Only after scope and access are agreed, a prototype could be evaluated with two
explicitly consenting environments. For each environment:

- Record who grants and exercises the agreed scope and which build is used.
- Perform and record the exact reproduction action and its expected and actual
  result, then retest the identified candidate with the same action and evidence.
- Revoke consent and demonstrate that a subsequent action is denied; record the
  attempt and outcome without exposing private data.
- Exercise an offline case and record it as unavailable, without claiming remote
  validation. Keep local checks and PR readiness distinct from that status.

Agree the procedure and evidence review with the participants before any such
prototype. This note does not start or authorize one.
