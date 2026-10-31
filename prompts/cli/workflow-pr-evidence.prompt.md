# Workflow PR evidence


Own `src/workflow-pr-evidence.mjs`. Export module function `preparePrEvidence({run, isCode}, ports = {}) -> {lines, approvalLines, issueReference, proofStatus}`. This is the production evidence-preparation boundary: both PR creation and updates must call it from the real body/publication path. Existing workflow-runner exports and callers stay compatible. It reads notes and machine proof through actual injected ports; it does not execute a test, publish, approve or advance a step. `run.workflow` is the saved workflow name; bug and small-change enable their named writer rules, and other workflow names do not; `run.baseBranch` is its selected base branch and saved `run.baseSha` remains immutable. `run.steps` is the workflow's known step order with each latest saved summary, including earlier areas; the caller derives it from the saved workflow/run, never arbitrary directory entries.

For each known step in workflow order, scan its latest stored summary, then the current direct `<runDir>/<step>.md` if present. Read no recursive logs, JSON, archived notes, foreign files or arbitrary summary-file paths. Missing notes contribute nothing. Edited notes replace their previous contents; replaced summaries use only the latest record. Lift only column-zero lines starting exactly with `Not fixed yet:`, `Not checked:`, `Defect:`, `Not caught because:`, `Proof (defect fixed):`, `Proof (gap closed):`, `Review:`. Only lift from the authorized writer table below. Trim payload ends, drop blanks and deduplicate within a label by payload equality ignoring one trailing period; preserve the first spelling, internal spaces and case, with distinct lines in source order. Emit `LABEL SAFE_PAYLOAD`, applying the prove owner's safe-value rule once to the raw payload. No further normalization or HTML entity escaping is permitted. Do not lift indented/case-varied labels or agent-authored `Old-code proof:`/`Tests vs base:`.

Authorized writers:

| Label | Permitted source |
|---|---|
| Not fixed yet | build or verify summary/direct note |
| Not checked | check, try, verify, formal, review or reproduce summary/direct note |
| Defect / Not caught because | reproduce summary/direct note only in bug; scope summary/direct note only in small-change |
| Proof (defect fixed) / Proof (gap closed) | verify summary/direct note |
| Review | direct review.md only, and only when review is an actual known workflow step; never a summary |

Other steps or workflow types cannot supply these labels. In particular build/verify cannot write Review, and a run with no review step publishes no Review line.

Order the top evidence block: Not fixed yet, Not checked, Defect, Not caught because, Proof (defect fixed), Proof (gap closed), machine Old-code proof (code PR only), integration-owned Tests vs base when supplied, Review. The inventory position is reserved for integration; this module does not implement #2570 or invent inventory text. Both PRs retain all applicable known-step labels across area boundaries. With a nonempty Not fixed yet line use `Refs #N` for every runner-owned issue reference on either PR; introduce no `Closes #N`. Otherwise retain `Part of #N` for PR 1 and `Closes #N` for code/small-change. `isCode` means code or single small-change publication; prompt-space uses false.

For code publication obtain current committed head through `ports.currentHead({root,baseBranch})`, never from summary text or a passed head claim. Its native adapter fetches the selected base branch and returns current computed merge-base `baseSha` together with `headSha`; a failure supplies no usable identity. Read only `<runDir>/old-code-proof.json` via `ports.readOldCodeProof({runDir})`. Accept a result only with the exact complete schema from the prove owner, with v2/origin v2, matching runId, freshly computed baseSha and Git-observed headSha (never compare with saved run.baseSha), and an outcome consistent with saved interruptSignal/phase facts/expectedFound/setupError/cleanupError, including parent-interrupt precedence and the separate native-exit mapping owned by prove. Missing records produce `Old-code proof: not run.` / proofStatus `not-run`; valid older-head or older-computed-base records produce `Old-code proof: stale (base or head changed; rerun pdd workflow prove).` / `stale`. Legacy v1, malformed, foreign-run, inconsistent or unreadable records and unavailable current head produce `Old-code proof: unavailable.` / `unavailable`. Accepted current records use the prove owner's exact outcome message and outcome as proofStatus. Summary text cannot replace or upgrade it. No missing/stale/failed proof blocks publication. Local file provenance is a trust boundary; this is not tamper-proof attestation or behavioral equivalence.

`lines` contains the ordered evidence lines (with no inventory line until integration supplies it); `issueReference` is the issue line; `proofStatus` is `not-applicable` on prompt-space PRs, which do not read head/proof. `readStepNotes({runDir,steps})` returns only existing regular direct known-step files, preserving their text; unknown reply steps are ignored. `currentHead` uses Git and the selected base-branch fetch and returns an empty error on success. `readOldCodeProof` returns original JSON text plus empty error, `missing` for no file, or a finite read error. Defaults perform real local reads. These callbacks map directly to resource publication operations below.

Insert every lifted/machine line above every replay status block, including PASS, BLOCKED, NOT REPLAYED and publication-pending, and above ordinary verdict/runtime/step prose. Preserve vector failure warnings and pending-before-push lifecycle safeguards; the replay block follows the complete top evidence block. Every lifted/machine line goes through existing marker rejection, Try-link removal, local-path redaction, report-reference retention and 60000-code-point body budget; never truncate into a false success. If lifted evidence itself exceeds available body room, retain whole lines in contract order and explicitly count omitted labels, failures and report references under the existing bounded-description policy. Compute Refs safety from all accepted labels before shortening; never restore Closes because a warning line did not fit. An overlong machine line may be replaced only by an explicit unavailable/omitted-result notice, never a shortened success claim. A failed old-code proof remains visible and publishable. Existing opted-in PRs still receive the replay publication-pending description before pushing source and retain pending on final-description failure. For non-opted code PRs, replace the old proof line with publication-pending before pushing changed source, then replace it with newly prepared current evidence; if either edit fails, report it, and never push source while an old success remains. Relevant PR 1 updates refresh labels too. The final body keeps exactly one canonical ownership marker and existing approval/stacking semantics. Native lifecycle tests must establish these effects; helper Runtime checks alone do not prove them.

## Approval evidence in PRs

Return approval lines separately as `approvalLines`; never prepend them to `lines`. The runner places them after the complete ordinary header, preserving the verdict, Runtime check/report lines, their blank separator and the `Part of #N` issue-reference line in their literal #18 positions. Approval lines follow that header and precede step prose; this publisher never inserts them into its top evidence `lines`. Emit one short line per saved approval in chronological order. The optional `run.decisions` and `run.promptApprovals` input fields carry saved gate decisions and standalone journal entries whose path/hash match currently published prompts. A new decision's `evidence` is authoritative; legacy records remain readable but never acquire invented actor/time/words. Deduplicate copies with the same evidence event `id` across gate history/journal. Different ids produce separate lines even when route, actor, time, words and prompts are identical. For id-less legacy evidence only, retain content-based deduplication; do not collapse an identified event into an id-less one. Event/gate identities need not be displayed. `said` lines begin `Approved in chat:`, terminal lines `Approved in terminal:`, native chat lines `Approved in area chat:`. Include the invoking actor kind/id, ISO-8601 UTC time derived from the stored epoch milliseconds, route, verbatim words when present, and every approved prompt path/hash; never silently omit approval records from a successful body. A body budget omission must say approval evidence was omitted, not imply complete evidence.

Every dynamic value, including actor, timestamp, route, path/hash and words, is a quoted JSON literal in a Markdown code span longer than all interior backtick runs. Preserve recoverable raw text: JSON escapes newlines, carriage returns, controls and bidi characters. Escape each exact `pdd-workflow:` prefix colon as `\u003a` inside the JSON literal, preventing an ownership marker. Do not HTML-escape raw identity or allow mentions, issue references, closing instructions, HTML or backticks to escape the span. These approval values use this rule instead of the ordinary lifted-label formatter. Keep exactly one real ownership marker and preserve existing redaction/budget/publication safeguards. A full render through the read-only GitHub Markdown API must show no user-mention/issue anchors or extra workflow markers from supplied evidence.

## Dependencies

- [Run records](workflow-runs.prompt.md): required authoring/generation/native-production/verification/testing context for saved approval decisions, including optional legacy-compatible gateAt and gateId; this renderer accepts supplied facts and never duplicates run storage policy.

- [Approval policy and journal](approval-policy.prompt.md): required authoring/generation/native-production/verification/testing context for supplied evidence values. No filesystem journal read is invented inside this renderer.

- [Committed proof](workflow-prove.prompt.md): required authoring/generation/runtime/verification/testing context for the complete saved machine-result schema, classification and exact messages. No execution port from prove is invoked here.
- The actual injected `currentHead`, `readStepNotes` and `readOldCodeProof` callback contracts are declared in this prompt and Runtime resources. Native defaults use existing project Git/file APIs and the selected saved run supplied by the runner. Callback replies supply all outside facts used by this module; no runner lifecycle, GitHub, Herdr, guide or publication side effects are needed to decide these lines.

<details>
<summary>Runtime interface</summary>

```json
{
  "status": "approved",
  "prose_sha256": "08d77bbc6fb8417cd2e9c46f75aebeaa52b02f521dfb1673638b91e889075684",
  "entries": [
    {
      "operation": "preparePrEvidence",
      "input_schema": {
        "type": "object",
        "properties": {
          "run": {
            "type": "object",
            "properties": {
              "runId": {
                "type": "string"
              },
              "runDir": {
                "type": "string"
              },
              "root": {
                "type": "string"
              },
              "baseSha": {
                "type": "string"
              },
              "number": {
                "type": "integer"
              },
              "steps": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "step": {
                      "type": "string"
                    },
                    "summary": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "step",
                    "summary"
                  ],
                  "additionalProperties": false
                }
              },
              "baseBranch": {
                "type": "string"
              },
              "workflow": {
                "type": "string"
              },
              "decisions": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "stage": {
                      "type": "string"
                    },
                    "decision": {
                      "type": "string"
                    },
                    "via": {
                      "type": "string"
                    },
                    "at": {
                      "type": "integer"
                    },
                    "text": {
                      "type": "string"
                    },
                    "evidence": {
                      "type": "object",
                      "properties": {
                        "route": {
                          "type": "string",
                          "enum": [
                            "said",
                            "terminal",
                            "chat"
                          ]
                        },
                        "actor": {
                          "type": "object",
                          "properties": {
                            "kind": {
                              "type": "string",
                              "enum": [
                                "agent",
                                "terminal"
                              ]
                            },
                            "id": {
                              "type": "string"
                            }
                          },
                          "required": [
                            "kind",
                            "id"
                          ],
                          "additionalProperties": false
                        },
                        "at": {
                          "type": "integer"
                        },
                        "words": {
                          "oneOf": [
                            {
                              "type": "string"
                            },
                            {
                              "type": "null"
                            }
                          ]
                        },
                        "prompts": {
                          "type": "array",
                          "items": {
                            "type": "object",
                            "properties": {
                              "path": {
                                "type": "string"
                              },
                              "proseSha256": {
                                "type": "string"
                              }
                            },
                            "required": [
                              "path",
                              "proseSha256"
                            ],
                            "additionalProperties": false
                          }
                        },
                        "id": {
                          "type": "string",
                          "minLength": 1
                        }
                      },
                      "required": [
                        "route",
                        "actor",
                        "at",
                        "words",
                        "prompts"
                      ],
                      "additionalProperties": false
                    },
                    "gateAt": {
                      "type": "integer"
                    },
                    "gateId": {
                      "type": "string",
                      "minLength": 1
                    }
                  },
                  "required": [
                    "stage",
                    "decision",
                    "via",
                    "at"
                  ],
                  "additionalProperties": false
                }
              },
              "promptApprovals": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "route": {
                      "type": "string",
                      "enum": [
                        "said",
                        "terminal",
                        "chat"
                      ]
                    },
                    "actor": {
                      "type": "object",
                      "properties": {
                        "kind": {
                          "type": "string",
                          "enum": [
                            "agent",
                            "terminal"
                          ]
                        },
                        "id": {
                          "type": "string"
                        }
                      },
                      "required": [
                        "kind",
                        "id"
                      ],
                      "additionalProperties": false
                    },
                    "at": {
                      "type": "integer"
                    },
                    "words": {
                      "oneOf": [
                        {
                          "type": "string"
                        },
                        {
                          "type": "null"
                        }
                      ]
                    },
                    "prompts": {
                      "type": "array",
                      "items": {
                        "type": "object",
                        "properties": {
                          "path": {
                            "type": "string"
                          },
                          "proseSha256": {
                            "type": "string"
                          }
                        },
                        "required": [
                          "path",
                          "proseSha256"
                        ],
                        "additionalProperties": false
                      }
                    },
                    "id": {
                      "type": "string",
                      "minLength": 1
                    }
                  },
                  "required": [
                    "route",
                    "actor",
                    "at",
                    "words",
                    "prompts"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "runId",
              "runDir",
              "root",
              "baseSha",
              "number",
              "steps",
              "baseBranch",
              "workflow"
            ],
            "additionalProperties": false
          },
          "isCode": {
            "type": "boolean"
          }
        },
        "required": [
          "run",
          "isCode"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "approvalLines": {"type": "array", "items": {"type": "string"}},
          "lines": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "issueReference": {
            "type": "string"
          },
          "proofStatus": {
            "type": "string"
          }
        },
        "required": [
          "lines",
          "approvalLines",
          "issueReference",
          "proofStatus"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [
    {
      "name": "publication",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "currentHead",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "root": {
                "type": "string"
              },
              "baseBranch": {
                "type": "string"
              }
            },
            "required": [
              "root",
              "baseBranch"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "headSha": {
                "type": "string"
              },
              "error": {
                "type": "string"
              },
              "baseSha": {
                "type": "string",
                "description": "Current merge-base of Git-observed head with the freshly fetched selected base branch, never the immutable saved run base."
              }
            },
            "required": [
              "headSha",
              "error",
              "baseSha"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "readStepNotes",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "runDir": {
                "type": "string"
              },
              "steps": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "runDir",
              "steps"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "notes": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "step": {
                      "type": "string"
                    },
                    "text": {
                      "type": "string"
                    }
                  },
                  "required": [
                    "step",
                    "text"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "notes"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "readOldCodeProof",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "runDir": {
                "type": "string"
              }
            },
            "required": [
              "runDir"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "content": {
                "type": "string"
              },
              "error": {
                "type": "string"
              }
            },
            "required": [
              "content",
              "error"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 5,
    "max_model_calls": 5
  },
  "conventions": []
}
```

</details>
