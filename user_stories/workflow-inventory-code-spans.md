# Read source text safely in the code PR report

I can read test names and source lines in the report without GitHub turning them into mentions, issue links or closing instructions.

## Acceptance criteria

1. Removed names containing "@octocat", "#17", "Closes #17", spaces and backticks appear as quoted JSON literals in Markdown code spans, with their raw identity and source order preserved.
2. Kept test names and complete changed assertion lines containing Markdown, HTML, mentions, issue references and backticks use code spans longer than every interior backtick run, without HTML entity substitution.
3. New suite and test skip entries use the same code-span format, preserve leading and trailing spaces, and show carriage returns, controls and bidirectional formatting characters as JSON escapes.
4. Names and source lines containing "pdd-workflow:" show every matching prefix colon as "\u003a" inside their code spans, so the exact text can be recovered without becoming a workflow marker; later colons and different capitalization stay unchanged.

## Rules to check

Use the [inventory owner's report format](../prompts/cli/workflow-inventory.prompt.md#report-format) for every removed or kept test name, suite name, assertion line and skip marker line. Keep the complete raw content visible as a quoted JSON literal inside a code span, including edge spaces and backticks. Do not substitute HTML entities in those values or let a backtick run end a span. Carriage returns, controls and bidirectional formatting remain visible as JSON escapes. Paths, reasons, identity matching, source order, sentinels and all other report behavior retain their existing rules.

## Review status

The person approved the first three criteria and nine exact expectations before their earlier attempts. Those Runtime checks were NOT RUN: lint passed, but #2579 prevented Story requests; the checks remain unjudged, with no AI calls. Root reviewed the marker-preservation clause, fourth criterion and three exact expectations before implementation, then approved the owner at the terminal; those new checks were not attempted. The current source's four criteria and 12 checks remain unjudged. Expectations come from the required format, never implementation output. Code acceptance requires all 12 native checks, real default Git/process and marker-safe publisher proof, and a final report rendered through the read-only GitHub Markdown API with no user-mention or issue anchors. Approval is not a Runtime pass and does not authorize publication.
