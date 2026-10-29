# Workflow test inventory

Own `src/workflow-inventory.mjs`: a bounded static report of committed test changes for human review. It never runs tests, judges coverage, approves deletions or blocks publication. This is new behavior; preserve the caller's existing publication and approval contracts. The report labels are informational even when comparison is unavailable.

## Public operations and outside boundary

Module function `analyzeTestChanges({files})` is the pure analyzer used by module function `collectTestInventory({cwd,baseSha,headSha}, ports)`. Both return `{available,reason,text,details}`. Files contain `{oldPath,newPath,before,after}`; an empty path means that side is absent and its content is empty. A rename supplies both exact paths in one record. The analyzer recognizes candidate files, compares cases and formats the report below. Apply the same file/byte limits to directly supplied snapshots as to the default Git adapter.

The collector calls injected `ports.readSnapshot({cwd,baseSha,headSha})` once. Runtime resource `snapshot.read` is that same boundary; the test binding records the request and supplies a snapshot. A reply has `{available,reason,files}`. False availability or a rejected callback yields an unavailable report, never a thrown publication error. A missing/invalid commit identity yields unavailable without reading: require full 40- or 64-character hexadecimal SHAs. Never substitute a branch or moving HEAD.

The default snapshot callback is module function `readGitTestSnapshot(input, ports)`, with injected `ports.execFile(program,argv,{cwd})` and a real subprocess default. It reads only Git objects for the two supplied commits. Enumerate changed paths/statuses with `git diff --no-ext-diff --no-textconv --name-status -z --find-renames BASE HEAD --`; parse NUL records including both rename paths without trimming. Read committed blobs through argv-based Git object reads, never ambient worktree files, shell interpolation, newline path splitting or Git's quoted display names. Preserve spaces, tabs, line breaks, Unicode and leading hyphens as path data. Honor thrown commands and structured nonzero exits. Missing commits, missing/unreadable blobs, malformed NUL records, binary/non-UTF-8 candidate contents or limits exceeded make the entire comparison unavailable; no partial successful `none` report. Ignore changed noncandidate files. Limit to 1,000 changed path records, 1 MiB per candidate blob and 16 MiB total candidate bytes. These native Git operations require real-repository tests; a supplied runtime snapshot does not execute Git.

## Recognized cases (bounded static convention)

Candidate JS/TS extensions are `.js`, `.mjs`, `.cjs`, `.jsx`, `.ts`, `.mts`, `.cts`, `.tsx`: a basename contains `.test.` or `.spec.`, or a path component is `test`, `tests`, or `__tests__`. Python basenames are `test_*.py` or `*_test.py`; Go basenames end `_test.go`. Classify both rename sides independently. Each record reports recognized cases on each candidate side; a noncandidate side has zero cases.

Recognize line-leading JS `test(` or `it(`, optionally with `.only`, `.skip` or `.todo`, whose first argument is a complete static single/double quoted name or a template name without interpolation on that line. Python recognizes `def test_NAME(` and `async def test_NAME(`; Go recognizes `func TestNAME(`. Ignore comment-only lines. This convention does not resolve aliases, computed names, parameterized/generated cases or declarations split across lines. It is an inventory of recognized declarations, not a semantic parser.

A conventional JS body may be inline on its declaration line, otherwise it ends at the first `});` line with the declaration's indentation; Python ends on the next nonblank, noncomment line at equal/lower indentation, and Go on the first unindented `}`. Nested recognized declarations belong to their own case; assertion lines belong to the innermost enclosing recognized body. Declarations with no body (such as a todo) have none. Unrecognized/multiline constructs can be missed; never describe this as complete coverage.

Kept identity is static name plus its occurrence number in source order within the corresponding file pair. Nested suite names do not change this identity. Match renamed files using Git's supplied rename pair. A case name change is removal plus addition. A file deletion removes all its recognized cases. Duplicate names remain separate occurrences; later occurrences display ` [N]` after the quoted name.

## Assertion and skip changes

Within each kept case collect complete source lines containing the word `assert` or `expect` (including `assert.equal` and `expect(...)`), excluding comment-only lines. Include an assertion on the declaration line when it occurs in that case's inline body, for example `test("name", () => assert.equal(actual, expected));`; it must not disappear merely because the declaration shares its line. Match identical lines with a longest common subsequence, choosing the earliest old then earliest new match in a tie. Within each unmatched gap, pair old/new lines in source order; unmatched old lines have destination `(removed)`, unmatched new lines have source `(added)`. Report both changes and deletions even when test counts stay equal. Assertions belonging to removed cases are represented only by the removed-case list. This line comparison does not claim to parse complete multiline expressions or determine whether an assertion is weaker.

Skip markers are JS declaration `.skip`/`.todo`, literal declaration options `skip: true`/`todo: true`, body calls `t.skip(`/`t.todo(`, and Python contiguous decorators `@pytest.mark.skip`, `skipif`, or `xfail` immediately preceding a recognized declaration. Report new marker lines by exact-line multiset difference per kept identity; every marker on an added case is new. Unchanged markers are not new. Include xfail under `New skips:`. Dynamic skip conditions, Go `t.Skip` and other frameworks are outside this convention.

## Report format

Order files lexically by new path, or old path for deletion, using JavaScript string order; preserve declaration and changed-line source order inside each file. Display a rename as `OLD → NEW`; other files use their existing path. All source-derived paths, names and lines are JSON string literals using standard JSON string escaping: short escapes `\t`, `\n`, `\r`, `\b` and `\f` for tab, newline, carriage return, backspace and form feed, and JSON Unicode escapes for other control characters. Then escape `&`, `<`, `>`, backtick, pipe and colon as HTML numeric entities, and explicitly escape bidirectional formatting characters as JSON Unicode escapes. This prevents data from creating headings, links, HTML or workflow markers. Keep exact raw path/name/line identity internally; no trim or whitespace collapse.

For each changed candidate file show `Tests vs base: PATH B → H tests. Removed: N (NAMES).` Use `Removed: none.` when zero. With no candidate files use `Tests vs base: none.` Then one `Changed assertions in kept tests: PATH NAME OLD → NEW.` per changed pair, or `Changed assertions in kept tests: none.` Finally one `New skips: PATH NAME LINE.` per introduced marker, or `New skips: none.` Use the literal unquoted `(removed)` / `(added)` for absent assertion sides. Every report ends with `Static inventory only; tests were not run.` and a newline.

`details` holds the complete escaped report. `text` is identical when it fits 12,000 Unicode code points. Otherwise retain all file count/removal-count summary lines (omit names first), then as many complete detail lines as fit, ending with `Inventory details omitted: N lines; full report: test-inventory.json in the run folder.` and the static disclaimer. If even summaries exceed that budget, retain whole summaries that fit and disclose omitted file and detail-line counts. Never truncate inside a quoted value or silently omit evidence.

An unavailable report has `available:false`, a nonblank bounded reason, and identical text/details: `Tests vs base: unavailable (REASON).\nChanged assertions in kept tests: unavailable.\nNew skips: unavailable.\nStatic inventory only; tests were not run.\n`. REASON uses the same escaped JSON-literal convention; do not expose raw stderr, host paths or credentials. Use stable reasons `invalid commit identity`, `snapshot unavailable`, `snapshot read failed`, or `inventory limit exceeded` as applicable. Success has `available:true` and empty reason, even when there are removals or changed assertions.

## Dependencies

None. Runtime `snapshot.read` supplies the native injected snapshot callback. The default Git adapter's command port is a native boundary, not a live runtime effect.

<details><summary>Runtime interface</summary>

```json
{
  "status": "approved",
  "prose_sha256": "837946f41755e695fc0f0ea374a33fe416354909f51b0e1f1885ebb734f1560b",
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
