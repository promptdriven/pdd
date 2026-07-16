# Verification Requirement Transition Rotation

Requirement-transition authority in
`.pdd/verification-profile-rotations.json` must be installed and consumed in two
separate protected changes. This separation prevents a candidate from granting
itself authority for prompt or verification-profile bytes introduced by the
same change.

## Phase A: install dormant rows

Phase A may change only `requirement_rotations`. The prompt named by each new
row and `.pdd/verification-profiles.json` must remain byte-for-byte identical to
the protected base. The rest of the policy envelope, including `schema_version`
and `rotations`, must remain valid and preserve the protected authority exactly.

Each row records the SHA-256 identities of the current prompt/profile bytes and
the prepared Phase B prompt/profile bytes. Review those exact prepared bytes
before landing Phase A. Phase A must merge and become part of the protected base
before Phase B begins. A change that installs a row and consumes it in the same
pull request is forbidden.

The one-time legacy bootstrap is narrower: an exact in-code bootstrap row may
install the first schema-2 envelope over an absent or schema-1 protected source.
A schema-1 source's active `rotations` authority must be preserved exactly; an
absent source has no active rotations to add. After schema 2 is protected, the
normal Phase A rules above apply.

## Phase B: consume protected authority

Phase B may update only the prompt and verification-profile bytes authorized by
the now-protected row. They must match the row's prepared
`head_prompt_sha256` and `head_policy_sha256` exactly, including formatting and
line endings. Any byte drift after Phase A was prepared invalidates the
transition: do not edit the digests in Phase B or combine replacement authority
with consumption. Prepare and protect a new dormant row in a new Phase A
instead.

Run the deterministic verification-profile and rollout-policy suites for both
phases:

```bash
pytest -q tests/test_sync_core_verification_profiles.py
pytest -q tests/test_sync_core_pdd_rollout_policy.py
```

Do not use a staging registry item to prepare or validate either phase.
