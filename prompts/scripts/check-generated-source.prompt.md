# Generated source verification

Own `scripts/check-generated-source.mjs`. Give a PR reviewer a local and public
check that detects stale generated-source prompt digests for affected modules,
including after integration with alpha, before reporting a PR ready.

## Check contract

Run `node scripts/check-generated-source.mjs --base REF` inside the checkout to
check. REF is a required Git commit or revision. Compare that commit directly
with the current working tree (including staged edits and untracked, nonignored
files). Do not replace REF with a merge base: a prompt brought in by an alpha
integration must be checked too. Use NUL-delimited Git paths and disable rename
detection so both sides of a rename count as changed.

Use the shared owner lookup and its header hash rules. A surviving Git-visible
file is affected when its path changed or any prompt named in its headers
changed. Inspect every header of an affected file, including unchanged source
files whose prompt changed. Deleted source files need no check. Ignore unrelated
stale headers so this gate can be used in a checkout with existing debt.

A header with a digest passes only when its state is `current`. A stale digest
or an unavailable named prompt fails. Report every failure in deterministic
file/header order, one line on stderr with the source path, prompt path,
`expected=HEX` (or `unavailable`), `current=HEX` and `state=STATE`. Exit 1 if
there are failures. JSON-quote a source path containing control characters so
each diagnostic remains one line. Otherwise print `Generated-source digests: N checked; 0
mismatches.` and a newline to stdout and exit 0; N counts headers with digests
on affected files. Hashless ownership headers do not claim a version and are
outside this check. Preserve the shared reader's accepted header syntax, window,
deduplication and temporary whole-file hash compatibility.

Missing/extra arguments, an invalid revision, a Git failure or an unreadable
affected source file fail closed with exit 2 and an actionable stderr diagnostic;
never report success for an unavailable comparison. Do not change files or
refresh headers. Every output line ends with a newline. The check uses no
network, credentials or interpreter. A matching digest is a writer's provenance
claim; it does not prove code correctness. Runtime prompt approval hashes and
generated-code full-file hashes remain separate checks.

## Public integration

The public `tests` CI job runs this command before the offline suite, on the
checkout containing the proposed integration. Fetch history and use the PR's
base SHA, or the push's previous SHA for main/alpha. A manual dispatch compares
with the first parent. Document the same local command and require rerunning it
with the target revision after integrating alpha and before calling a PR ready.

## Dependencies

- [File owner lookup](../cli/file-owner.prompt.md): required generation and
  verification context for `findOwners`, header selection and digest states.
- [Runtime preflight](../cli/runtime-preflight.prompt.md): required generation
  context for the Git-visible file inventory `gitFiles(root)`.
