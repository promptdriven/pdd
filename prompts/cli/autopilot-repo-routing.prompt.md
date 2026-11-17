# Explicit repository routing

Own `src/autopilot-repo-routing.mjs`. Identify an unambiguous foreign owner for
the work requested in an issue, without treating a dependency as the work target.

## Domain decisions

- A repository target is an `OWNER/REPO` slug or a GitHub repository URL. In
  `promptdriven/pdd` only, the bare names `pdd`, `prompt-runtime`, `runtime-client`
  and `pdd_cloud` also mean the corresponding `promptdriven` repositories. Match
  case-insensitively and return the lowercase slug. Slug components contain only
  ASCII letters, digits, `_`, `-` and `.`, and are not `.` or `..`.
- Read the title's leading `[REPOSITORY]` or `REPOSITORY:` as a target if it
  resolves to a repository. Read standalone body lines `Repository:`, `Service:`,
  `File:` or `Files:` as target fields, with or without a `Target ` prefix.
  A repository or service field accepts one repository target. A file field
  accepts one repository-qualified path: a GitHub `blob` or `tree` URL with a
  ref and a path, or a known bare name or its full slug followed by a path.
  Accept surrounding whitespace and single backticks around a field value.
- Ignore quoted lines, fenced Markdown code blocks and HTML comments in the body.
  Ordinary mentions and links in prose, issue links, and unqualified local file
  paths do not establish ownership. An unresolved target field, multiple distinct
  targets, or a target equal to the current repository leaves the issue in scope.

## Public contract

`planIssueRouting({repository, title, body})` takes three strings (current
`OWNER/REPO` slug, issue title, issue body). It is pure. If the evidence identifies
one repository other than `repository`, return `{targetRepository, label}` with
the lowercase slug and `label: "pdd:elsewhere"`. Otherwise return
`{targetRepository: null, label: null}`. The caller owns eligibility checks,
GitHub writes and claim suppression.

## Dependencies

None.
