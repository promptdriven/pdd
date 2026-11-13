# Keep the supplied proof command exact

As a person checking a regression, I want my supplied command to reach both test runs unchanged, so I can trust the comparison.

## Acceptance criteria

1. A proof command containing quotes, backslashes, CR, LF, TAB, NUL, DEL, U+0085, U+2028, U+2029 and "pdd-workflow:" reaches both old and new test runs unchanged. The saved command and expectation stay exact, and the successful report shows visible control escapes.
2. The ordinary command "node --test test/new.test.mjs" still reaches both test runs unchanged. An old exit of 1 with "defect-x" and a new exit of 0 produce exit 0, a successful proof report, the same saved facts, and cleanup of both test snapshots.

## Rules to check

The special-character command is the existing `literal-command-controls` case. Its exact input and expected report stay unchanged. Visible escapes belong in the report. Replacing the actual command with escape text or adding characters is forbidden. The fixed process replies describe old failure and new success; they do not execute a real shell command.

## What must not change

Keep the existing phase limits, snapshot selection, cleanup, saved proof format, literal expectation matching and safe report formatting. This change grants no approval, publication or workflow authority. The current suite-cost measurement rules remain in force.
