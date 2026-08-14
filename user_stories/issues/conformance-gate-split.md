# Generation safety checks must survive PDD's own internal reorganisation

## Background

When PDD generates or regenerates a file, it runs a set of safety checks before
anything is written to disk. Together these are the reason a user can re-run
generation on a mature module without fear:

- If the model returns planning text, an apology, or nothing at all instead of
  code, the user is told the output was not code — not that their symbols went
  missing.
- If the generated code drops or reshapes a function the module publicly
  provides, the user is told which symbol regressed and what its shape should
  have been.
- If regeneration would rewrite most of an existing test file, the write is
  refused, because accumulated regression coverage is worth more than a
  reformatted test suite.
- If the generated code does not export what the module promised to export, the
  user is told which promised symbol is missing.

In every one of these cases the user's file on disk is left exactly as it was,
and the message names the failing check clearly enough to act on.

## The problem

These checks are currently defined in one very large place inside PDD. That
makes them hard to change safely, and PDD's maintainers periodically reorganise
where its own internals live.

A user does not care where the checks live. They care that the checks keep
behaving identically across PDD versions. Today nothing guarantees that: an
internal reorganisation could weaken or silently drop one of these checks, and
the user would only find out when a regeneration quietly destroyed work.

The failure is especially bad because it is *silent*. A safety check that stops
firing does not produce an error — it produces a successful-looking run.

## Requested capability

Reorganising PDD's internals must never change what a user observes from these
checks. Specifically:

1. A run whose model output is not code must be reported as an output-shape
   problem, and must be distinguishable from a run whose code is missing a
   promised symbol.
2. A run that would remove or reshape a symbol the module publicly provides must
   be refused, and the report must name the symbol and its expected shape.
3. A run that would rewrite more of an existing test file than the configured
   limit must be refused.
4. A run that fails any of these checks must leave the target file on disk
   unchanged.
5. Every documented way of deliberately overriding a check must keep working,
   and must keep requiring the same deliberate opt-in as before. Reorganisation
   must not make an override easier to trigger by accident.

## MUST NOT

- A check MUST NOT become a no-op. Silently passing is worse than failing.
- A failing check MUST NOT overwrite, truncate, or partially write the target
  file.
- An override MUST NOT begin applying to checks it did not previously cover.
- The user-facing distinction between the different failure kinds MUST NOT
  collapse into one generic error.

## Out of scope

- Adding new safety checks, or changing the thresholds and defaults of the
  existing ones.
- Changing how a user opts out of a check.
- Performance of the checks.
