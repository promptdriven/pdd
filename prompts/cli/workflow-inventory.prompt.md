# Workflow test inventory

Own `src/workflow-inventory.mjs`: a bounded static report of committed test changes for human review. It never runs tests, judges coverage, approves deletions or blocks publication. Preserve the caller's existing publication and approval contracts, public operation names, exact case identity, source-order matching and existing report lines except for the explicitly expanded escaping, skip and partial-availability rules below. The report labels are informational even when comparison is unavailable.

## Public operations and outside boundary

Module function `analyzeTestChanges({files})` is the pure analyzer used by module function `collectTestInventory({cwd,baseSha,headSha}, ports)`. Both return `{available,reason,text,details}`. Files contain `{oldPath,newPath,before,after}`; an empty path means that side is absent and its content is empty. A rename supplies both exact paths in one record. The analyzer recognizes candidate files, compares cases and formats the report below. Apply the same file/byte limits to directly supplied snapshots as to the default Git adapter.

The collector calls injected `ports.readSnapshot({cwd,baseSha,headSha})` once. Runtime resource `snapshot.read` is that same boundary; the test binding records the request and supplies a snapshot. A reply has `{available,reason,files}`. False availability or a rejected callback yields an unavailable report, never a thrown publication error. A missing/invalid commit identity yields unavailable without reading: require full 40- or 64-character hexadecimal SHAs. Never substitute a branch or moving HEAD.

The default snapshot callback is module function `readGitTestSnapshot(input, ports)`, with injected `ports.execFile(program,argv,{cwd})` and a real subprocess default. It reads only Git objects for the two supplied commits. Enumerate changed paths/statuses with `git diff --no-ext-diff --no-textconv --name-status -z --find-renames BASE HEAD --`; parse NUL records including both rename paths without trimming. Read committed blobs through argv-based Git object reads, never ambient worktree files, shell interpolation, newline path splitting or Git's quoted display names. Preserve spaces, tabs, line breaks, Unicode and leading hyphens as path data. Honor thrown commands and structured nonzero exits. Missing commits, an unreadable whole snapshot, failed Git commands or malformed NUL records make the whole comparison unavailable; never turn them into an empty successful selection.

### Candidate limits and partial availability

Ignore changed noncandidate files before counting limits. At most 1,000 candidate path records are allowed; a rename pair counts once when either side is a candidate. More than 1,000 candidate records makes the whole comparison unavailable with `inventory limit exceeded`; any number of documentation-only records does not consume that allowance. Each candidate blob may contain at most 1 MiB (1,048,576 bytes), and the aggregate candidate analysis budget is 16 MiB (16,777,216 bytes). Do not load an unbounded blob merely to discover that it exceeds the limit.

An over-1-MiB, binary or non-UTF-8 candidate blob makes only its file pair unavailable, with respective stable reason `candidate blob exceeds 1 MiB`, `binary candidate blob`, or `non-UTF-8 candidate blob`. Do not assert zero counts, no removals, unchanged assertions or no skips for that pair. Preserve the healthy pairs' counts, removals, changed assertions and skips. Whole-comparison availability remains true with empty reason when enumeration succeeded and every omitted pair is explicitly disclosed. The same rules apply to supplied snapshots; raw strings can represent size and NUL-binary failures, while native invalid UTF-8 requires adapter metadata.

A file record may supply optional `unavailableReason` with exactly one of those three stable blob reasons. A marked pair has no usable content on either side; ignore its supplied content and report all three categories unavailable for that pair. Apply byte limits to directly supplied unmarked snapshots as well. The optional field represents native unreadable bytes without pretending that a JSON string can contain invalid UTF-8.

The 16 MiB aggregate limit retains whole-comparison behavior: sum both candidate sides of all otherwise usable pairs before analysis; if the sum exceeds the limit, return the whole-comparison `inventory limit exceeded` result. Exclude already-disclosed invalid/oversized pairs from that sum; noncandidate content never counts. This remaining aggregate limit can still make a report unavailable, and must not be described as complete healthy-file preservation at arbitrary total sizes.

These native Git operations and byte-decoding failures require real-repository tests; a supplied runtime snapshot does not execute Git.

## Recognized cases (bounded static convention)

Candidate JS/TS extensions are `.js`, `.mjs`, `.cjs`, `.jsx`, `.ts`, `.mts`, `.cts`, `.tsx`: a basename contains `.test.` or `.spec.`, or a path component is `test`, `tests`, or `__tests__`. Python basenames are `test_*.py` or `*_test.py`; Go basenames end `_test.go`. Classify both rename sides independently. Each record reports recognized cases on each candidate side; a noncandidate side has zero cases.

Recognize line-leading JS `test(` or `it(`, optionally with `.only`, `.skip` or `.todo`, and `xit(` as a skipped test, whose first argument is a complete static single/double quoted name or a template name without interpolation on that line. Python recognizes `def test_NAME(` and `async def test_NAME(`; Go recognizes `func TestNAME(`. Ignore comment-only lines. This convention does not resolve aliases, computed names, parameterized/generated cases or declarations split across lines. It is an inventory of recognized declarations, not a semantic parser.

A conventional JS body may be inline on its declaration line, otherwise it ends at the first `});` line with the declaration's indentation; Python ends on the next nonblank, noncomment line at equal/lower indentation, and Go on the first unindented `}`. Nested recognized declarations belong to their own case; assertion lines belong to the innermost enclosing recognized body. Declarations with no body (such as a todo) have none. Unrecognized/multiline constructs can be missed; never describe this as complete coverage.

Kept identity is static name plus its occurrence number in source order within the corresponding file pair. Nested suite names do not change this identity. Match renamed files using Git's supplied rename pair. A case name change is removal plus addition. A file deletion removes all its recognized cases. Duplicate names remain separate occurrences; later occurrences display ` [N]` after the rendered name.

## Assertion and skip changes

Within each kept case collect complete source lines containing the word `assert` or `expect` (including `assert.equal` and `expect(...)`), excluding comment-only lines. Include an assertion on the declaration line when it occurs in that case's inline body, for example `test("name", () => assert.equal(actual, expected));`; it must not disappear merely because the declaration shares its line. Match identical lines with a longest common subsequence, choosing the earliest old then earliest new match in a tie. Within each unmatched gap, pair old/new lines in source order; unmatched old lines have destination `(removed)`, unmatched new lines have source `(added)`. Report both changes and deletions even when test counts stay equal. Assertions belonging to removed cases are represented only by the removed-case list. For a kept case with B old and H new assertion lines, if B × H exceeds 1,000,000, skip only that case's assertion comparison and emit `Changed assertions in kept tests: PATH NAME unavailable ("too many assertion lines to compare").` Preserve its test counts, removals, skips and all other cases' evidence. The threshold is strict: a product of exactly 1,000,000 is compared. Use bounded quadratic matching work at or below the cap, without rebuilding a complete comparison table after each mismatch; retain the established tie and source-order results. This line comparison does not claim to parse complete multiline expressions or determine whether an assertion is weaker.

Skip markers are JS declaration `.skip`/`.todo`, `xit`, literal declaration options `skip: true`/`todo: true` and nonempty static string `skip` values (single/double quoted or uninterpolated template), body calls `t.skip(`/`t.todo(`, Python body calls `pytest.skip(`, and contiguous decorators `@pytest.mark.skip`, `skipif`, or `xfail` immediately preceding a recognized Python declaration. Report new marker lines by exact-line multiset difference per kept identity; every marker on an added case is new. Unchanged markers are not new. Include xfail under `New skips:`. Dynamic skip conditions, Go `t.Skip` and other frameworks remain outside this convention.

Also recognize line-leading `describe(` / `describe.skip(` with a complete static name on the declaration line. A suite is a marker owner, never an extra test or assertion owner. Its identity is the suite kind, exact static name and occurrence among suites of that name in the file pair, independent of test identities and nesting. Compare suite `.skip` marker lines by the same exact-line multiset rule; display `New skips: PATH suite NAME LINE.` (with duplicate suffix `[N]` by the existing occurrence convention). Normal `describe` contributes no marker. Test declarations inside a suite retain their existing test identities and counts; do not invent one skipped test for a suite or propagate its marker into each child.

## Report format

Order files lexically by new path, or old path for deletion, using JavaScript string order; preserve declaration and changed-line source order inside each file. Display a rename as `OLD → NEW`; other files use their existing path. Keep exact raw path/name/line identity internally; no trim or whitespace collapse.

Every source-derived test or suite name, assertion line and skip marker line is a JSON string literal, including its opening and closing double quotes, inside a Markdown code span wherever it appears in the report. First apply standard JSON string escaping: short escapes `\t`, `\n`, `\r`, `\b` and `\f` for tab, newline, carriage return, backspace and form feed, and JSON Unicode escapes for other control characters; retain explicit JSON Unicode escaping for bidirectional formatting characters. Preserve a line-ending carriage return as `\r`. After JSON/control/bidirectional escaping and before fence selection, replace the colon U+003A in every exact, case-sensitive `pdd-workflow:` prefix inside these literals with the lowercase JSON escape `\u003a`; leave subsequent colons unchanged so JSON parsing recovers the exact raw value without introducing a workflow marker. Do not HTML-entity-escape any content of these literals, including `&`, `<`, `>`, backticks, pipe, colon, `@` or `#`. Surround the complete literal with matching backtick runs of length one greater than the longest consecutive backtick run inside that literal (one backtick when it contains none). The double quotes are the payload boundaries, so add no padding, trim nothing and preserve leading/trailing spaces and backticks inside the quotes. This code span prevents names and source lines from creating GitHub mentions, issue links, closing keywords, HTML or Markdown structure. Duplicate occurrence suffixes such as ` [2]` remain outside the span.

Paths and unavailable reasons retain their existing JSON-literal format: apply the same JSON/control/bidirectional escaping, then HTML numeric entities for `&`, `<`, `>`, backtick, pipe, colon, `@` and `#`. This retained entity format is not a guarantee against GitHub mentions or issue links; the code-span rule above owns that protection for names and source lines.

For each unavailable candidate file pair show `Tests vs base: PATH unavailable (REASON).`, plus `Changed assertions in kept tests: PATH unavailable (REASON).` and `New skips: PATH unavailable (REASON).`; REASON is an escaped JSON string literal. Keep these lines in the corresponding category and lexical file order; a category with any unavailable entry (including a capped assertion comparison) must not also claim `none`. For each healthy changed candidate file show `Tests vs base: PATH B → H tests. Removed: N (NAMES).` Use `Removed: none.` when zero. With no candidate files use `Tests vs base: none.` Then one `Changed assertions in kept tests: PATH NAME OLD → NEW.` per changed pair, or `Changed assertions in kept tests: none.` Finally one `New skips: PATH NAME LINE.` per introduced marker, or `New skips: none.` Use the literal unquoted `(removed)` / `(added)` for absent assertion sides. Every report ends with `Static inventory only; tests were not run.` and a newline.

`details` holds the complete formatted report. `text` is identical when it fits 12,000 Unicode code points. Otherwise retain all file count/removal-count and unavailable-file summary lines (omit names first), then as many complete detail lines as fit, ending with `Inventory details omitted: N lines; full report: test-inventory.json in the run folder.` and the static disclaimer. If even summaries exceed that budget, retain whole summaries that fit and disclose omitted file and detail-line counts. Never truncate inside a formatted value or silently omit evidence.

An unavailable report has `available:false`, a nonblank bounded reason, and identical text/details: `Tests vs base: unavailable (REASON).\nChanged assertions in kept tests: unavailable.\nNew skips: unavailable.\nStatic inventory only; tests were not run.\n`. REASON uses the same escaped JSON-literal convention; do not expose raw stderr, host paths or credentials. Use stable reasons `invalid commit identity`, `snapshot unavailable`, `snapshot read failed`, or `inventory limit exceeded` as applicable. Success has `available:true` and empty reason, even when there are removals, changed assertions or explicitly reported unavailable file pairs or per-test assertion comparisons.

## Dependencies

None. Runtime `snapshot.read` supplies the native injected snapshot callback. The default Git adapter's command port is a native boundary, not a live runtime effect.

<details><summary>Runtime interface</summary>

```json
{
  "status": "approved",
  "prose_sha256": "095af8ff266d080f3f965c6be8290c1d40bb7064c49d7c3e0a629b3f727e1e5e",
  "entries": [
    {
      "operation": "analyzeTestChanges",
      "input_schema": {
        "type": "object",
        "properties": {
          "files": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "oldPath": {
                  "type": "string"
                },
                "newPath": {
                  "type": "string"
                },
                "before": {
                  "type": "string"
                },
                "after": {
                  "type": "string"
                },
                "unavailableReason": {
                  "type": "string",
                  "enum": [
                    "candidate blob exceeds 1 MiB",
                    "binary candidate blob",
                    "non-UTF-8 candidate blob"
                  ]
                }
              },
              "required": [
                "oldPath",
                "newPath",
                "before",
                "after"
              ],
              "additionalProperties": false
            }
          }
        },
        "required": [
          "files"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "available": {
            "type": "boolean"
          },
          "reason": {
            "type": "string"
          },
          "text": {
            "type": "string"
          },
          "details": {
            "type": "string"
          }
        },
        "required": [
          "available",
          "reason",
          "text",
          "details"
        ],
        "additionalProperties": false
      },
      "errors": []
    },
    {
      "operation": "collectTestInventory",
      "input_schema": {
        "type": "object",
        "properties": {
          "cwd": {
            "type": "string"
          },
          "baseSha": {
            "type": "string"
          },
          "headSha": {
            "type": "string"
          }
        },
        "required": [
          "cwd",
          "baseSha",
          "headSha"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "available": {
            "type": "boolean"
          },
          "reason": {
            "type": "string"
          },
          "text": {
            "type": "string"
          },
          "details": {
            "type": "string"
          }
        },
        "required": [
          "available",
          "reason",
          "text",
          "details"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "snapshot",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "read",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "baseSha": {
                "type": "string"
              },
              "headSha": {
                "type": "string"
              }
            },
            "required": [
              "cwd",
              "baseSha",
              "headSha"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "available": {
                "type": "boolean"
              },
              "reason": {
                "type": "string"
              },
              "files": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "oldPath": {
                      "type": "string"
                    },
                    "newPath": {
                      "type": "string"
                    },
                    "before": {
                      "type": "string"
                    },
                    "after": {
                      "type": "string"
                    },
                    "unavailableReason": {
                      "type": "string",
                      "enum": [
                        "candidate blob exceeds 1 MiB",
                        "binary candidate blob",
                        "non-UTF-8 candidate blob"
                      ]
                    }
                  },
                  "required": [
                    "oldPath",
                    "newPath",
                    "before",
                    "after"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "available",
              "reason",
              "files"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 12,
    "max_model_calls": 6
  },
  "conventions": []
}
```
</details>
