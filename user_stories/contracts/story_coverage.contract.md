<!-- pdd-story-contract derived-from-story="../story__story_coverage.md" story-hash="e02aa4797cf4a505" issue-ref="https://github.com/promptdriven/pdd/issues/1704" -->

# Contract: Story regression metrics + machine-readable evidence (coverage % and trend)

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__story_coverage.md`), not this contract.

## Covers
- AC1: Running the story lane produces a JSON evidence file with story count, story-backed test count, story coverage %, and pass-rate.
- AC2: The numbers are derivable deterministically from the marker/traceability API and gate statuses — no LLM calls.
- AC3: A short human-readable summary line is printed in CI with the format `story regression: <N> tests across <M>/<T> stories (<P>% covered), <N> passing`.

## Context
- A project with documented user stories and a test suite that includes story-backed regression tests (tests marked with `-m story` or equivalent traceability markers).
- The marker/traceability API (from sub-issue 1) is available and returns deterministic counts of total stories and story-backed tests.
- Gate statuses (from sub-issue 4) are available and provide pass/fail results for each story-backed test.
- An evidence directory exists at `.pdd/evidence/` (or the path used by EPIC #833) and is writable.
- The computation runs in a CI environment where stdout is captured for the summary line.

## Acceptance Criteria
1. Given a project with 110 total documented stories and 96 of them backed by passing story regression tests totaling 142 tests, when the story lane executes, then a JSON evidence file is written to `.pdd/evidence/` containing keys `story_count` (110), `story_backed_test_count` (142), `story_coverage_pct` (87.27…), and `pass_rate` (1.0).
2. Given the same project state, when the story lane executes, then a single summary line is printed to stdout matching the pattern `story regression: 142 tests across 96/110 stories (87% covered), 142 passing`.
3. Given any project state, when the story lane computes its metrics, then no LLM call is made during the computation of story count, test count, coverage percentage, or pass rate.
4. Given the same project state and no changes to stories or tests, when the story lane executes twice, then the JSON evidence file contains identical numeric values both times.

## Oracle
These details matter for pass/fail:
- The JSON evidence file exists at a path under `.pdd/evidence/` after execution.
- The JSON file contains the keys `story_count`, `story_backed_test_count`, `stories_covered`, `story_coverage_pct`, and `pass_rate`.
- **When gate/pass-fail verdicts are available** (`status: "ok"`), the numeric fields are populated and `story_coverage_pct` equals `stories_covered / story_count` expressed as a percentage (0–100), while `pass_rate` equals `passing_test_count / story_backed_test_count` (0.0–1.0).
- **When those verdicts are unavailable** (the shipped steady state — the executable story suite and gate statuses are not yet wired, tracked by #1909), the emitter honestly returns `status: "not_applicable"` with `story_coverage_pct: null` and `pass_rate: null` rather than fabricating numbers. This degraded, honest output is a passing state, not a contract violation.
- The summary line is printed to stdout; when a real measurement is available it contains the four numeric values in the specified order and format, and in the `not_applicable` state it prints the degraded summary (`story regression: not_applicable (...)`) instead.
- No LLM or generative model is invoked during metric computation.

## Non-Oracle
These details should not matter:
- The exact filename of the JSON evidence file (as long as it is under `.pdd/evidence/` and is valid JSON).
- The number of decimal places in `story_coverage_pct` (as long as it is a valid float).
- The exact wording of the summary line beyond the numeric values and the structure `story regression: … tests across …/… stories (…% covered), … passing`.
- The order of keys in the JSON object.
- Whether the summary line is printed before or after the JSON file is written.
- The internal implementation (e.g., whether counts come from a cache, a direct filesystem scan, or an API call to the marker system) as long as it is deterministic and LLM-free.

## Negative Cases
- The JSON evidence file is missing any of the required keys.
- When a real measurement is available (`status: "ok"`), the JSON evidence file contains non-numeric values for the numeric keys. (In the honest `not_applicable` state, `story_coverage_pct: null` and `pass_rate: null` are expected, not a failure.)
- `story_coverage_pct` exceeds 100 or is negative.
- `pass_rate` exceeds 1.0 or is negative.
- The summary line is absent from stdout; or, when a real measurement is available, it omits any of the four numeric values.
- An LLM call is made during metric computation (e.g., to summarize, estimate, or fill in missing data).
- Running twice on identical inputs produces different numeric values in the JSON file.

## Non-Goals
- Building the dashboard UI itself (that lives in pdd_cloud); this story provides only the data contract and the emitter.
- Computing or emitting trend-over-time data in the JSON evidence file (the summary line and JSON are point-in-time snapshots).
- Displaying the summary in any format other than a single stdout line and a JSON file.

## Candidate Prompts
- `story_coverage_python.prompt` — Primary prompt that implements the story coverage metrics computation and evidence emission. (primary)
- `checkup_report_python.prompt` — May consume the JSON evidence file for grouping and risk classification in checkup sessions. (related)
- `ci_validation_python.prompt` — May invoke or depend on the story lane output as part of CI validation loops. (possible)

## Notes
- The summary line format in the issue uses `142 passing` as the final segment; this matches `pass_rate = 1.0` when all story-backed tests pass. When some fail, the summary should reflect the actual passing count (e.g., `140 passing`).
- The evidence path is tied to EPIC #833; the contract asserts existence under `.pdd/evidence/` but does not pin an exact filename to avoid coupling to naming conventions that may evolve.
- The deterministic requirement (no LLM calls) is a hard constraint from the issue’s acceptance criteria and must be enforceable — any invocation of a generative model during metric computation is a failure.
