# Shared metrics calculator

`src/metrics-model.mjs` exports module function `calculateMetrics({events, repo, scope, timezone, observedAt, sources})`. It calculates one deterministic, JSON-serializable report without I/O or input mutation. It preserves the named public behavior and permits internal representation changes. Selection comes from supplied observations; this module does not analyze dependencies or schedule work.

A report names metric-definition version, repository, declared IANA timezone, selected scope, UTC observation cutoff, sources, coverage and conflicts. Every percentage carries numerator, denominator, scope, cutoff and unknown count; a zero denominator yields null. List issue identifiers and reasons behind each count. Canonical issue identity is case-folded owner/name plus issue number; attempt identity is repo plus runId, PR identity repo plus number, and event identity source plus id. Deduplicate identical event identities and facts even when their observation times differ, retaining the earliest observation; preserve conflicting payloads as uncertainty. Never sum snapshots or people as disjoint populations.

<details><summary>Required event facts and measurement rules</summary>

Each event contains `schema` = `pdd.metrics.event.v1`, stable `id`, canonical `repo`, positive `issue`, `type`, UTC `at`, UTC `observedAt`, `source`, optional `attempt`, and `data`. Data supports selection (`snapshotId`, `inScope`, `state`, `reasons`), launch/start (`origin`, `decisionId`, `status`, CLI/skill/candidate versions, `requiredOutcome`), step history (`step`, `status`, `area`), outcome, milestone (`stage`, `reason`, PR and head), checker (`verdict`, `reviewer`, `evidence`, `acceptance`, PR and head), CI, delivery (`explicit`, evidence, PR and head), report (`classification`, `humanReported`, evidence), assistance and coverage. Missing facts are unknown. Observations after the cutoff do not establish facts at the cutoff.

Queue uses the supplied snapshot's issue membership and selector state, with ready, excluded, waiting and unknown separately, including capacity separately from dependency. Activity counts actual starts, candidate completions, validation results and deliveries occurring on the local calendar date in the declared timezone, not a conversion funnel. Activity is null outside an explicit activity scope. Cohort follows the fixed snapshot membership through the cutoff, including never-started issues and later deliveries; distinguish issue counts from attempts and event counts. An attempted/failed/uncertain launch is not a confirmed start. A start states autopilot, manual or unknown without inferring source from a workflow or label. Retries do not add issues.

Prompt-only is a valid stopping outcome, not failed code. A prompt PR alone is not delivery. A single small-change PR or a code PR carrying prompt content can deliver; a shared PR requires an explicit issue mapping and relevant proof for each issue. Implementation readiness is explicitly recorded and identifies the code candidate; PR creation or internal review alone is not independent validation. Record validation, CI, Runtime and native tests separately. A checker result is fresh only for the current candidate head and the existing evidence acceptance rule; stale, missing or conflicting evidence is unknown, not pass. The calculator reports evidence and does not create an approval gate. Keep independently observed later stages even when earlier evidence is missing.

Expose issue-level in-scope selection, confirmed starts by origin, PR creation, implementation-ready, fresh validation, delivery, and failed-fix facts. Preserve independent later-stage observations. Keep existing cohort-wide stage percentages and additionally provide transitions with each numerator restricted to issues in its immediately preceding denominator: available to eligible, eligible to Autopilot start, start to PR creation, Autopilot start to implementation-ready, implementation-ready to validation, validation to delivery, and delivery to reported failed fix. Include numerator and denominator issue IDs and unknown counts; an absent fact is unknown unless evidence establishes a negative. Manual and unknown-origin starts remain visible separately. The latest explicit code PR, candidate or implementation-ready observation identifies the code PR; only head observations for that PR can supersede it. Distinct attempts with candidate observations remain unresolved while more than one is active; a later timestamp or attempt name does not establish supersession. A recorded completed cancel step or explicit cancelled/superseded outcome closes that attempt. Select the active scoped attempt independently of unscoped PR metadata; when exactly one active scoped attempt has a candidate, only its latest explicit mapping selects the PR. Unscoped code-PR and head observations can update that mapped PR but cannot select a different PR or revive a closed attempt. Readiness must belong to the selected attempt; unscoped readiness establishes readiness only when no scoped candidate attempt establishes identity. With no active scoped candidate, closed attempts cannot supply candidate or readiness, while an independently observed unscoped code PR head may remain visible with readiness unknown if scoped candidate history exists. Plain unscoped candidate and readiness records retain their legacy behavior when no scoped candidate history exists. A known code PR head remains visible without readiness; a fresh accepted external result for the current PR and head establishes validation independently of missing readiness or start evidence. It does not establish either earlier fact. An unscoped head alone does not validate a closed scoped attempt. The latest required outcome controls the current issue-level prompt-only status; each wait retains the outcome in effect for its attempt when the wait began, so a later scope change does not rewrite that wait.

For a daily-start group, membership is issues with confirmed starts on the selected local date. Queue capacity and dependency causes remain separately visible. Concurrent waits are tracked independently by attempt and stage, with multiple reasons retained; a resume clears only its matching wait. Sources can be strings or source metadata objects; compare source identities by their source field and preserve metadata, including a known or unknown export scope when supplied. An absent scope remains unknown.

Waits list elapsed duration at cutoff, stage and known reasons; planned prompt-only, observe-mode and new-product holds remain distinct from failures. Human-reported failed fixes require an explicit linked human complaint about the delivered fix. Administrative reopen, new scope, revert and unclassified reports are separate. Keep every qualifying report after a delivered fix even if another delivery follows. Count an explicit linked human complaint about the delivered issue as an issue-level known report even when no delivery identity is provided. Associate it with a delivery only when its attempt or PR identifies a matching preceding delivery; never assign an unlinked report to the latest delivery. Expose unassociated known reports separately from ambiguous or unevidenced reports; attribution and follow-up remain unknown where unassociated reports could apply. For each delivery expose its associated reports and 7- and 30-day windows measured from that delivery; later reports remain in the associated list. The existing issue followUp describes the latest delivery, while failedFixReports and failedFix cover all deliveries. Show immature windows. No report yet is not proven lasting success. Recorded recovery indicates assistance; an initial authorization is not recovery, and missing capture cannot establish an unassisted run. Missing machines and historical capture limitations are visible rather than zero.
</details>

A FAIL is negative only with accepted evidence. A split across sources remains unknown until two fresh accepted checks after the last opposing verdict agree, with distinct structured sessions and either different families or same-family mode on both checks. Compare family identities case-insensitively while preserving the original recorded identity. Opaque identities alone cannot establish that pair; retain every observation. Repeated observations of the same checker comment may refine unknown acceptance to accepted without making contradictory claims. At each cutoff, a later unknown acceptance does not erase an earlier known acceptance; differing known acceptance claims remain conflicts. Retain genuinely different claims as conflicts and preserve the earliest observation of each claim for historical cutoffs.

## Dependencies

None. Timezone conversion is deterministic and uses the supplied timezone and cutoff; no implicit system clock or repository lookup.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "dc3450fa3967e8594af884a44e1bb80ec465594ff8d58cfa5a45612b21ab06c2",
  "entries": [
    {
      "operation": "calculateMetrics",
      "input_schema": {
        "type": "object",
        "properties": {
          "events": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "schema": {
                  "type": "string"
                },
                "id": {
                  "type": "string"
                },
                "repo": {
                  "type": "string"
                },
                "issue": {
                  "type": "integer"
                },
                "type": {
                  "type": "string"
                },
                "at": {
                  "type": "string"
                },
                "observedAt": {
                  "type": "string"
                },
                "source": {
                  "type": "string"
                },
                "attempt": {
                  "type": "string"
                },
                "data": {
                  "type": "object",
                  "properties": {
                    "snapshotId": {
                      "type": "string"
                    },
                    "inScope": {
                      "type": "boolean"
                    },
                    "state": {
                      "type": "string"
                    },
                    "reasons": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    },
                    "origin": {
                      "type": "string"
                    },
                    "decisionId": {
                      "type": "string"
                    },
                    "status": {
                      "type": "string"
                    },
                    "cliVersion": {
                      "type": "string"
                    },
                    "skillVersion": {
                      "type": "string"
                    },
                    "requiredOutcome": {
                      "type": "string"
                    },
                    "stage": {
                      "type": "string"
                    },
                    "reason": {
                      "type": "string"
                    },
                    "pr": {
                      "type": "integer"
                    },
                    "head": {
                      "type": "string"
                    },
                    "verdict": {
                      "type": "string"
                    },
                    "reviewer": {
                      "type": "string"
                    },                    "checkerFamily": {
                      "type": "string"
                    },                    "checkerMode": {
                      "type": "string"
                    },
                    "evidence": {
                      "type": "string"
                    },
                    "acceptance": {
                      "type": "string"
                    },
                    "classification": {
                      "type": "string"
                    },
                    "humanReported": {
                      "type": "boolean"
                    },
                    "explicit": {
                      "type": "boolean"
                    },
                    "complete": {
                      "type": "boolean"
                    },
                    "since": {
                      "type": "string"
                    },
                    "until": {
                      "type": "string"
                    },
                    "step": {
                      "type": "string"
                    },
                    "area": {
                      "type": "string"
                    },
                    "candidateVersion": {
                      "type": "string"
                    },
                    "waitStage": {
                      "type": "string"
                    }
                  },
                  "required": [],
                  "additionalProperties": false
                }
              },
              "required": [
                "schema",
                "id",
                "repo",
                "issue",
                "type",
                "at",
                "observedAt",
                "source",
                "data"
              ],
              "additionalProperties": false
            }
          },
          "repo": {
            "type": "string"
          },
          "scope": {
            "type": "object",
            "properties": {
              "kind": {
                "type": "string"
              },
              "snapshotId": {
                "type": "string"
              },
              "date": {
                "type": "string"
              }
            },
            "required": [
              "kind"
            ],
            "additionalProperties": false
          },
          "timezone": {
            "type": "string"
          },
          "observedAt": {
            "type": "string"
          },
          "sources": {
            "type": "array",
            "items": {
              "oneOf": [
                {
                  "type": "string"
                },
                {
                  "type": "object",
                  "properties": {
                    "source": {
                      "type": "string"
                    },
                    "scope": {
                      "type": "string",
                      "enum": [
                        "all-retained-repo-events",
                        "unknown"
                      ]
                    },
                    "captureStartedAt": {
                      "type": "string"
                    },
                    "cliVersion": {
                      "type": "string"
                    },
                    "definitionVersion": {
                      "type": "string"
                    },
                    "exportedAt": {
                      "type": "string"
                    },
                    "timezone": {
                      "type": "string"
                    },
                    "coverage": {
                      "type": "object",
                      "properties": {
                        "since": {
                          "oneOf": [
                            {
                              "type": "string"
                            },
                            {
                              "type": "null"
                            }
                          ]
                        },
                        "until": {
                          "oneOf": [
                            {
                              "type": "string"
                            },
                            {
                              "type": "null"
                            }
                          ]
                        }
                      },
                      "required": [
                        "since",
                        "until"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "required": [
                    "source"
                  ],
                  "additionalProperties": false
                }
              ]
            }
          }
        },
        "required": [
          "events",
          "repo",
          "scope",
          "timezone",
          "observedAt",
          "sources"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "definitionVersion": {
            "type": "string"
          },
          "repo": {
            "type": "string"
          },
          "scope": {
            "type": "object",
            "properties": {
              "kind": {
                "type": "string"
              },
              "snapshotId": {
                "type": "string"
              },
              "date": {
                "type": "string"
              }
            },
            "required": [
              "kind"
            ],
            "additionalProperties": false
          },
          "timezone": {
            "type": "string"
          },
          "observedAt": {
            "type": "string"
          },
          "sources": {
            "type": "array",
            "items": {
              "oneOf": [
                {
                  "type": "string"
                },
                {
                  "type": "object",
                  "properties": {
                    "source": {
                      "type": "string"
                    },
                    "scope": {
                      "type": "string",
                      "enum": [
                        "all-retained-repo-events",
                        "unknown"
                      ]
                    },
                    "captureStartedAt": {
                      "type": "string"
                    },
                    "cliVersion": {
                      "type": "string"
                    },
                    "definitionVersion": {
                      "type": "string"
                    },
                    "exportedAt": {
                      "type": "string"
                    },
                    "timezone": {
                      "type": "string"
                    },
                    "coverage": {
                      "type": "object",
                      "properties": {
                        "since": {
                          "oneOf": [
                            {
                              "type": "string"
                            },
                            {
                              "type": "null"
                            }
                          ]
                        },
                        "until": {
                          "oneOf": [
                            {
                              "type": "string"
                            },
                            {
                              "type": "null"
                            }
                          ]
                        }
                      },
                      "required": [
                        "since",
                        "until"
                      ],
                      "additionalProperties": false
                    }
                  },
                  "required": [
                    "source"
                  ],
                  "additionalProperties": false
                }
              ]
            }
          },
          "coverage": {
            "type": "object",
            "properties": {
              "events": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "schema": {
                      "type": "string"
                    },
                    "id": {
                      "type": "string"
                    },
                    "repo": {
                      "type": "string"
                    },
                    "issue": {
                      "type": "integer"
                    },
                    "type": {
                      "type": "string"
                    },
                    "at": {
                      "type": "string"
                    },
                    "observedAt": {
                      "type": "string"
                    },
                    "source": {
                      "type": "string"
                    },
                    "attempt": {
                      "type": "string"
                    },
                    "data": {
                      "type": "object",
                      "properties": {
                        "snapshotId": {
                          "type": "string"
                        },
                        "inScope": {
                          "type": "boolean"
                        },
                        "state": {
                          "type": "string"
                        },
                        "reasons": {
                          "type": "array",
                          "items": {
                            "type": "string"
                          }
                        },
                        "origin": {
                          "type": "string"
                        },
                        "decisionId": {
                          "type": "string"
                        },
                        "status": {
                          "type": "string"
                        },
                        "cliVersion": {
                          "type": "string"
                        },
                        "skillVersion": {
                          "type": "string"
                        },
                        "requiredOutcome": {
                          "type": "string"
                        },
                        "stage": {
                          "type": "string"
                        },
                        "reason": {
                          "type": "string"
                        },
                        "pr": {
                          "type": "integer"
                        },
                        "head": {
                          "type": "string"
                        },
                        "verdict": {
                          "type": "string"
                        },
                        "reviewer": {
                          "type": "string"
                        },                        "checkerFamily": {
                          "type": "string"
                        },                        "checkerMode": {
                          "type": "string"
                        },
                        "evidence": {
                          "type": "string"
                        },
                        "acceptance": {
                          "type": "string"
                        },
                        "classification": {
                          "type": "string"
                        },
                        "humanReported": {
                          "type": "boolean"
                        },
                        "explicit": {
                          "type": "boolean"
                        },
                        "complete": {
                          "type": "boolean"
                        },
                        "since": {
                          "type": "string"
                        },
                        "until": {
                          "type": "string"
                        },
                        "step": {
                          "type": "string"
                        },
                        "area": {
                          "type": "string"
                        },
                        "candidateVersion": {
                          "type": "string"
                        },
                        "waitStage": {
                          "type": "string"
                        }
                      },
                      "required": [],
                      "additionalProperties": false
                    }
                  },
                  "required": [
                    "schema",
                    "id",
                    "repo",
                    "issue",
                    "type",
                    "at",
                    "observedAt",
                    "source",
                    "data"
                  ],
                  "additionalProperties": false
                }
              },
              "missingSources": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "complete": {
                "type": "boolean"
              }
            },
            "required": [
              "events",
              "missingSources",
              "complete"
            ],
            "additionalProperties": false
          },
          "conflicts": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "source": {
                  "type": "string"
                },
                "id": {
                  "type": "string"
                },
                "events": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                }
              },
              "required": [
                "source",
                "id",
                "events"
              ],
              "additionalProperties": false
            }
          },
          "issues": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "repo": {
                  "type": "string"
                },
                "issue": {
                  "type": "integer"
                },
                "selection": {
                  "type": "object",
                  "properties": {
                    "inScope": {
                      "oneOf": [
                        {
                          "type": "boolean"
                        },
                        {
                          "type": "null"
                        }
                      ]
                    },
                    "state": {
                      "type": "string"
                    },
                    "reasons": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    }
                  },
                  "required": [
                    "inScope",
                    "state",
                    "reasons"
                  ],
                  "additionalProperties": false
                },
                "started": {
                  "type": "string"
                },
                "validated": {
                  "type": "string"
                },
                "delivered": {
                  "type": "string"
                },
                "requiredOutcome": {
                  "type": "string"
                },
                "promptOnlyStop": {
                  "type": "boolean"
                },
                "origins": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "attempts": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "starts": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "candidate": {
                  "oneOf": [
                    {
                      "type": "object",
                      "properties": {
                        "schema": {
                          "type": "string"
                        },
                        "id": {
                          "type": "string"
                        },
                        "repo": {
                          "type": "string"
                        },
                        "issue": {
                          "type": "integer"
                        },
                        "type": {
                          "type": "string"
                        },
                        "at": {
                          "type": "string"
                        },
                        "observedAt": {
                          "type": "string"
                        },
                        "source": {
                          "type": "string"
                        },
                        "attempt": {
                          "type": "string"
                        },
                        "data": {
                          "type": "object",
                          "properties": {
                            "snapshotId": {
                              "type": "string"
                            },
                            "inScope": {
                              "type": "boolean"
                            },
                            "state": {
                              "type": "string"
                            },
                            "reasons": {
                              "type": "array",
                              "items": {
                                "type": "string"
                              }
                            },
                            "origin": {
                              "type": "string"
                            },
                            "decisionId": {
                              "type": "string"
                            },
                            "status": {
                              "type": "string"
                            },
                            "cliVersion": {
                              "type": "string"
                            },
                            "skillVersion": {
                              "type": "string"
                            },
                            "requiredOutcome": {
                              "type": "string"
                            },
                            "stage": {
                              "type": "string"
                            },
                            "reason": {
                              "type": "string"
                            },
                            "pr": {
                              "type": "integer"
                            },
                            "head": {
                              "type": "string"
                            },
                            "verdict": {
                              "type": "string"
                            },
                            "reviewer": {
                              "type": "string"
                            },                            "checkerFamily": {
                              "type": "string"
                            },                            "checkerMode": {
                              "type": "string"
                            },
                            "evidence": {
                              "type": "string"
                            },
                            "acceptance": {
                              "type": "string"
                            },
                            "classification": {
                              "type": "string"
                            },
                            "humanReported": {
                              "type": "boolean"
                            },
                            "explicit": {
                              "type": "boolean"
                            },
                            "complete": {
                              "type": "boolean"
                            },
                            "since": {
                              "type": "string"
                            },
                            "until": {
                              "type": "string"
                            },
                            "step": {
                              "type": "string"
                            },
                            "area": {
                              "type": "string"
                            },
                            "candidateVersion": {
                              "type": "string"
                            },
                            "waitStage": {
                              "type": "string"
                            }
                          },
                          "required": [],
                          "additionalProperties": false
                        }
                      },
                      "required": [
                        "schema",
                        "id",
                        "repo",
                        "issue",
                        "type",
                        "at",
                        "observedAt",
                        "source",
                        "data"
                      ],
                      "additionalProperties": false
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "checks": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "ci": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "steps": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "deliveries": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "reports": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "failedFixReports": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "followUp": {
                  "oneOf": [
                    {
                      "type": "object",
                      "properties": {
                        "7": {
                          "type": "object",
                          "properties": {
                            "mature": {
                              "type": "boolean"
                            },
                            "failedFixReports": {
                              "type": "array",
                              "items": {
                                "type": "object",
                                "properties": {
                                  "schema": {
                                    "type": "string"
                                  },
                                  "id": {
                                    "type": "string"
                                  },
                                  "repo": {
                                    "type": "string"
                                  },
                                  "issue": {
                                    "type": "integer"
                                  },
                                  "type": {
                                    "type": "string"
                                  },
                                  "at": {
                                    "type": "string"
                                  },
                                  "observedAt": {
                                    "type": "string"
                                  },
                                  "source": {
                                    "type": "string"
                                  },
                                  "attempt": {
                                    "type": "string"
                                  },
                                  "data": {
                                    "type": "object",
                                    "properties": {
                                      "snapshotId": {
                                        "type": "string"
                                      },
                                      "inScope": {
                                        "type": "boolean"
                                      },
                                      "state": {
                                        "type": "string"
                                      },
                                      "reasons": {
                                        "type": "array",
                                        "items": {
                                          "type": "string"
                                        }
                                      },
                                      "origin": {
                                        "type": "string"
                                      },
                                      "decisionId": {
                                        "type": "string"
                                      },
                                      "status": {
                                        "type": "string"
                                      },
                                      "cliVersion": {
                                        "type": "string"
                                      },
                                      "skillVersion": {
                                        "type": "string"
                                      },
                                      "requiredOutcome": {
                                        "type": "string"
                                      },
                                      "stage": {
                                        "type": "string"
                                      },
                                      "reason": {
                                        "type": "string"
                                      },
                                      "pr": {
                                        "type": "integer"
                                      },
                                      "head": {
                                        "type": "string"
                                      },
                                      "verdict": {
                                        "type": "string"
                                      },
                                      "reviewer": {
                                        "type": "string"
                                      },                                      "checkerFamily": {
                                        "type": "string"
                                      },                                      "checkerMode": {
                                        "type": "string"
                                      },
                                      "evidence": {
                                        "type": "string"
                                      },
                                      "acceptance": {
                                        "type": "string"
                                      },
                                      "classification": {
                                        "type": "string"
                                      },
                                      "humanReported": {
                                        "type": "boolean"
                                      },
                                      "explicit": {
                                        "type": "boolean"
                                      },
                                      "complete": {
                                        "type": "boolean"
                                      },
                                      "since": {
                                        "type": "string"
                                      },
                                      "until": {
                                        "type": "string"
                                      },
                                      "step": {
                                        "type": "string"
                                      },
                                      "area": {
                                        "type": "string"
                                      },
                                      "candidateVersion": {
                                        "type": "string"
                                      },
                                      "waitStage": {
                                        "type": "string"
                                      }
                                    },
                                    "required": [],
                                    "additionalProperties": false
                                  }
                                },
                                "required": [
                                  "schema",
                                  "id",
                                  "repo",
                                  "issue",
                                  "type",
                                  "at",
                                  "observedAt",
                                  "source",
                                  "data"
                                ],
                                "additionalProperties": false
                              }
                            },
                            "status": {
                              "type": "string"
                            }
                          },
                          "required": [
                            "mature",
                            "failedFixReports",
                            "status"
                          ],
                          "additionalProperties": false
                        },
                        "30": {
                          "type": "object",
                          "properties": {
                            "mature": {
                              "type": "boolean"
                            },
                            "failedFixReports": {
                              "type": "array",
                              "items": {
                                "type": "object",
                                "properties": {
                                  "schema": {
                                    "type": "string"
                                  },
                                  "id": {
                                    "type": "string"
                                  },
                                  "repo": {
                                    "type": "string"
                                  },
                                  "issue": {
                                    "type": "integer"
                                  },
                                  "type": {
                                    "type": "string"
                                  },
                                  "at": {
                                    "type": "string"
                                  },
                                  "observedAt": {
                                    "type": "string"
                                  },
                                  "source": {
                                    "type": "string"
                                  },
                                  "attempt": {
                                    "type": "string"
                                  },
                                  "data": {
                                    "type": "object",
                                    "properties": {
                                      "snapshotId": {
                                        "type": "string"
                                      },
                                      "inScope": {
                                        "type": "boolean"
                                      },
                                      "state": {
                                        "type": "string"
                                      },
                                      "reasons": {
                                        "type": "array",
                                        "items": {
                                          "type": "string"
                                        }
                                      },
                                      "origin": {
                                        "type": "string"
                                      },
                                      "decisionId": {
                                        "type": "string"
                                      },
                                      "status": {
                                        "type": "string"
                                      },
                                      "cliVersion": {
                                        "type": "string"
                                      },
                                      "skillVersion": {
                                        "type": "string"
                                      },
                                      "requiredOutcome": {
                                        "type": "string"
                                      },
                                      "stage": {
                                        "type": "string"
                                      },
                                      "reason": {
                                        "type": "string"
                                      },
                                      "pr": {
                                        "type": "integer"
                                      },
                                      "head": {
                                        "type": "string"
                                      },
                                      "verdict": {
                                        "type": "string"
                                      },
                                      "reviewer": {
                                        "type": "string"
                                      },                                      "checkerFamily": {
                                        "type": "string"
                                      },                                      "checkerMode": {
                                        "type": "string"
                                      },
                                      "evidence": {
                                        "type": "string"
                                      },
                                      "acceptance": {
                                        "type": "string"
                                      },
                                      "classification": {
                                        "type": "string"
                                      },
                                      "humanReported": {
                                        "type": "boolean"
                                      },
                                      "explicit": {
                                        "type": "boolean"
                                      },
                                      "complete": {
                                        "type": "boolean"
                                      },
                                      "since": {
                                        "type": "string"
                                      },
                                      "until": {
                                        "type": "string"
                                      },
                                      "step": {
                                        "type": "string"
                                      },
                                      "area": {
                                        "type": "string"
                                      },
                                      "candidateVersion": {
                                        "type": "string"
                                      },
                                      "waitStage": {
                                        "type": "string"
                                      }
                                    },
                                    "required": [],
                                    "additionalProperties": false
                                  }
                                },
                                "required": [
                                  "schema",
                                  "id",
                                  "repo",
                                  "issue",
                                  "type",
                                  "at",
                                  "observedAt",
                                  "source",
                                  "data"
                                ],
                                "additionalProperties": false
                              }
                            },
                            "status": {
                              "type": "string"
                            }
                          },
                          "required": [
                            "mature",
                            "failedFixReports",
                            "status"
                          ],
                          "additionalProperties": false
                        }
                      },
                      "required": [
                        "7",
                        "30"
                      ],
                      "additionalProperties": false
                    },
                    {
                      "type": "null"
                    }
                  ]
                },
                "waits": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "issue": {
                        "type": "integer"
                      },
                      "stage": {
                        "type": "string"
                      },
                      "reason": {
                        "type": "string"
                      },
                      "since": {
                        "type": "string"
                      },
                      "elapsedMs": {
                        "type": "integer"
                      },
                      "source": {
                        "type": "string"
                      },
                      "reasons": {
                        "type": "array",
                        "items": {
                          "type": "string"
                        }
                      },
                      "requiredOutcome": {
                        "type": "string"
                      },
                      "promptOnlyStop": {
                        "type": "boolean"
                      }
                    },
                    "required": [
                      "issue",
                      "stage",
                      "reason",
                      "since",
                      "elapsedMs",
                      "source",
                      "reasons",
                      "requiredOutcome",
                      "promptOnlyStop"
                    ],
                    "additionalProperties": false
                  }
                },
                "assistance": {
                  "type": "object",
                  "properties": {
                    "status": {
                      "type": "string"
                    },
                    "events": {
                      "type": "array",
                      "items": {
                        "type": "object",
                        "properties": {
                          "schema": {
                            "type": "string"
                          },
                          "id": {
                            "type": "string"
                          },
                          "repo": {
                            "type": "string"
                          },
                          "issue": {
                            "type": "integer"
                          },
                          "type": {
                            "type": "string"
                          },
                          "at": {
                            "type": "string"
                          },
                          "observedAt": {
                            "type": "string"
                          },
                          "source": {
                            "type": "string"
                          },
                          "attempt": {
                            "type": "string"
                          },
                          "data": {
                            "type": "object",
                            "properties": {
                              "snapshotId": {
                                "type": "string"
                              },
                              "inScope": {
                                "type": "boolean"
                              },
                              "state": {
                                "type": "string"
                              },
                              "reasons": {
                                "type": "array",
                                "items": {
                                  "type": "string"
                                }
                              },
                              "origin": {
                                "type": "string"
                              },
                              "decisionId": {
                                "type": "string"
                              },
                              "status": {
                                "type": "string"
                              },
                              "cliVersion": {
                                "type": "string"
                              },
                              "skillVersion": {
                                "type": "string"
                              },
                              "requiredOutcome": {
                                "type": "string"
                              },
                              "stage": {
                                "type": "string"
                              },
                              "reason": {
                                "type": "string"
                              },
                              "pr": {
                                "type": "integer"
                              },
                              "head": {
                                "type": "string"
                              },
                              "verdict": {
                                "type": "string"
                              },
                              "reviewer": {
                                "type": "string"
                              },                              "checkerFamily": {
                                "type": "string"
                              },                              "checkerMode": {
                                "type": "string"
                              },
                              "evidence": {
                                "type": "string"
                              },
                              "acceptance": {
                                "type": "string"
                              },
                              "classification": {
                                "type": "string"
                              },
                              "humanReported": {
                                "type": "boolean"
                              },
                              "explicit": {
                                "type": "boolean"
                              },
                              "complete": {
                                "type": "boolean"
                              },
                              "since": {
                                "type": "string"
                              },
                              "until": {
                                "type": "string"
                              },
                              "step": {
                                "type": "string"
                              },
                              "area": {
                                "type": "string"
                              },
                              "candidateVersion": {
                                "type": "string"
                              },
                              "waitStage": {
                                "type": "string"
                              }
                            },
                            "required": [],
                            "additionalProperties": false
                          }
                        },
                        "required": [
                          "schema",
                          "id",
                          "repo",
                          "issue",
                          "type",
                          "at",
                          "observedAt",
                          "source",
                          "data"
                        ],
                        "additionalProperties": false
                      }
                    }
                  },
                  "required": [
                    "status",
                    "events"
                  ],
                  "additionalProperties": false
                },
                "coverage": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "conflicts": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "source": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "source",
                      "id"
                    ],
                    "additionalProperties": false
                  }
                },
                "prCreated": {
                  "type": "string"
                },
                "implementationReady": {
                  "type": "string"
                },
                "failedFix": {
                  "type": "string"
                },
                "deliveryFollowUps": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "delivery": {
                        "type": "object",
                        "properties": {
                          "schema": {
                            "type": "string"
                          },
                          "id": {
                            "type": "string"
                          },
                          "repo": {
                            "type": "string"
                          },
                          "issue": {
                            "type": "integer"
                          },
                          "type": {
                            "type": "string"
                          },
                          "at": {
                            "type": "string"
                          },
                          "observedAt": {
                            "type": "string"
                          },
                          "source": {
                            "type": "string"
                          },
                          "attempt": {
                            "type": "string"
                          },
                          "data": {
                            "type": "object",
                            "properties": {
                              "snapshotId": {
                                "type": "string"
                              },
                              "inScope": {
                                "type": "boolean"
                              },
                              "state": {
                                "type": "string"
                              },
                              "reasons": {
                                "type": "array",
                                "items": {
                                  "type": "string"
                                }
                              },
                              "origin": {
                                "type": "string"
                              },
                              "decisionId": {
                                "type": "string"
                              },
                              "status": {
                                "type": "string"
                              },
                              "cliVersion": {
                                "type": "string"
                              },
                              "skillVersion": {
                                "type": "string"
                              },
                              "requiredOutcome": {
                                "type": "string"
                              },
                              "stage": {
                                "type": "string"
                              },
                              "reason": {
                                "type": "string"
                              },
                              "pr": {
                                "type": "integer"
                              },
                              "head": {
                                "type": "string"
                              },
                              "verdict": {
                                "type": "string"
                              },
                              "reviewer": {
                                "type": "string"
                              },                              "checkerFamily": {
                                "type": "string"
                              },                              "checkerMode": {
                                "type": "string"
                              },
                              "evidence": {
                                "type": "string"
                              },
                              "acceptance": {
                                "type": "string"
                              },
                              "classification": {
                                "type": "string"
                              },
                              "humanReported": {
                                "type": "boolean"
                              },
                              "explicit": {
                                "type": "boolean"
                              },
                              "complete": {
                                "type": "boolean"
                              },
                              "since": {
                                "type": "string"
                              },
                              "until": {
                                "type": "string"
                              },
                              "step": {
                                "type": "string"
                              },
                              "area": {
                                "type": "string"
                              },
                              "candidateVersion": {
                                "type": "string"
                              },
                              "waitStage": {
                                "type": "string"
                              }
                            },
                            "required": [],
                            "additionalProperties": false
                          }
                        },
                        "required": [
                          "schema",
                          "id",
                          "repo",
                          "issue",
                          "type",
                          "at",
                          "observedAt",
                          "source",
                          "data"
                        ],
                        "additionalProperties": false
                      },
                      "failedFixReports": {
                        "type": "array",
                        "items": {
                          "type": "object",
                          "properties": {
                            "schema": {
                              "type": "string"
                            },
                            "id": {
                              "type": "string"
                            },
                            "repo": {
                              "type": "string"
                            },
                            "issue": {
                              "type": "integer"
                            },
                            "type": {
                              "type": "string"
                            },
                            "at": {
                              "type": "string"
                            },
                            "observedAt": {
                              "type": "string"
                            },
                            "source": {
                              "type": "string"
                            },
                            "attempt": {
                              "type": "string"
                            },
                            "data": {
                              "type": "object",
                              "properties": {
                                "snapshotId": {
                                  "type": "string"
                                },
                                "inScope": {
                                  "type": "boolean"
                                },
                                "state": {
                                  "type": "string"
                                },
                                "reasons": {
                                  "type": "array",
                                  "items": {
                                    "type": "string"
                                  }
                                },
                                "origin": {
                                  "type": "string"
                                },
                                "decisionId": {
                                  "type": "string"
                                },
                                "status": {
                                  "type": "string"
                                },
                                "cliVersion": {
                                  "type": "string"
                                },
                                "skillVersion": {
                                  "type": "string"
                                },
                                "requiredOutcome": {
                                  "type": "string"
                                },
                                "stage": {
                                  "type": "string"
                                },
                                "reason": {
                                  "type": "string"
                                },
                                "pr": {
                                  "type": "integer"
                                },
                                "head": {
                                  "type": "string"
                                },
                                "verdict": {
                                  "type": "string"
                                },
                                "reviewer": {
                                  "type": "string"
                                },                                "checkerFamily": {
                                  "type": "string"
                                },                                "checkerMode": {
                                  "type": "string"
                                },
                                "evidence": {
                                  "type": "string"
                                },
                                "acceptance": {
                                  "type": "string"
                                },
                                "classification": {
                                  "type": "string"
                                },
                                "humanReported": {
                                  "type": "boolean"
                                },
                                "explicit": {
                                  "type": "boolean"
                                },
                                "complete": {
                                  "type": "boolean"
                                },
                                "since": {
                                  "type": "string"
                                },
                                "until": {
                                  "type": "string"
                                },
                                "step": {
                                  "type": "string"
                                },
                                "area": {
                                  "type": "string"
                                },
                                "candidateVersion": {
                                  "type": "string"
                                },
                                "waitStage": {
                                  "type": "string"
                                }
                              },
                              "required": [],
                              "additionalProperties": false
                            }
                          },
                          "required": [
                            "schema",
                            "id",
                            "repo",
                            "issue",
                            "type",
                            "at",
                            "observedAt",
                            "source",
                            "data"
                          ],
                          "additionalProperties": false
                        }
                      },
                      "followUp": {
                        "type": "object",
                        "properties": {
                          "7": {
                            "type": "object",
                            "properties": {
                              "mature": {
                                "type": "boolean"
                              },
                              "failedFixReports": {
                                "type": "array",
                                "items": {
                                  "type": "object",
                                  "properties": {
                                    "schema": {
                                      "type": "string"
                                    },
                                    "id": {
                                      "type": "string"
                                    },
                                    "repo": {
                                      "type": "string"
                                    },
                                    "issue": {
                                      "type": "integer"
                                    },
                                    "type": {
                                      "type": "string"
                                    },
                                    "at": {
                                      "type": "string"
                                    },
                                    "observedAt": {
                                      "type": "string"
                                    },
                                    "source": {
                                      "type": "string"
                                    },
                                    "attempt": {
                                      "type": "string"
                                    },
                                    "data": {
                                      "type": "object",
                                      "properties": {
                                        "snapshotId": {
                                          "type": "string"
                                        },
                                        "inScope": {
                                          "type": "boolean"
                                        },
                                        "state": {
                                          "type": "string"
                                        },
                                        "reasons": {
                                          "type": "array",
                                          "items": {
                                            "type": "string"
                                          }
                                        },
                                        "origin": {
                                          "type": "string"
                                        },
                                        "decisionId": {
                                          "type": "string"
                                        },
                                        "status": {
                                          "type": "string"
                                        },
                                        "cliVersion": {
                                          "type": "string"
                                        },
                                        "skillVersion": {
                                          "type": "string"
                                        },
                                        "requiredOutcome": {
                                          "type": "string"
                                        },
                                        "stage": {
                                          "type": "string"
                                        },
                                        "reason": {
                                          "type": "string"
                                        },
                                        "pr": {
                                          "type": "integer"
                                        },
                                        "head": {
                                          "type": "string"
                                        },
                                        "verdict": {
                                          "type": "string"
                                        },
                                        "reviewer": {
                                          "type": "string"
                                        },                                        "checkerFamily": {
                                          "type": "string"
                                        },                                        "checkerMode": {
                                          "type": "string"
                                        },
                                        "evidence": {
                                          "type": "string"
                                        },
                                        "acceptance": {
                                          "type": "string"
                                        },
                                        "classification": {
                                          "type": "string"
                                        },
                                        "humanReported": {
                                          "type": "boolean"
                                        },
                                        "explicit": {
                                          "type": "boolean"
                                        },
                                        "complete": {
                                          "type": "boolean"
                                        },
                                        "since": {
                                          "type": "string"
                                        },
                                        "until": {
                                          "type": "string"
                                        },
                                        "step": {
                                          "type": "string"
                                        },
                                        "area": {
                                          "type": "string"
                                        },
                                        "candidateVersion": {
                                          "type": "string"
                                        },
                                        "waitStage": {
                                          "type": "string"
                                        }
                                      },
                                      "required": [],
                                      "additionalProperties": false
                                    }
                                  },
                                  "required": [
                                    "schema",
                                    "id",
                                    "repo",
                                    "issue",
                                    "type",
                                    "at",
                                    "observedAt",
                                    "source",
                                    "data"
                                  ],
                                  "additionalProperties": false
                                }
                              },
                              "status": {
                                "type": "string"
                              }
                            },
                            "required": [
                              "mature",
                              "failedFixReports",
                              "status"
                            ],
                            "additionalProperties": false
                          },
                          "30": {
                            "type": "object",
                            "properties": {
                              "mature": {
                                "type": "boolean"
                              },
                              "failedFixReports": {
                                "type": "array",
                                "items": {
                                  "type": "object",
                                  "properties": {
                                    "schema": {
                                      "type": "string"
                                    },
                                    "id": {
                                      "type": "string"
                                    },
                                    "repo": {
                                      "type": "string"
                                    },
                                    "issue": {
                                      "type": "integer"
                                    },
                                    "type": {
                                      "type": "string"
                                    },
                                    "at": {
                                      "type": "string"
                                    },
                                    "observedAt": {
                                      "type": "string"
                                    },
                                    "source": {
                                      "type": "string"
                                    },
                                    "attempt": {
                                      "type": "string"
                                    },
                                    "data": {
                                      "type": "object",
                                      "properties": {
                                        "snapshotId": {
                                          "type": "string"
                                        },
                                        "inScope": {
                                          "type": "boolean"
                                        },
                                        "state": {
                                          "type": "string"
                                        },
                                        "reasons": {
                                          "type": "array",
                                          "items": {
                                            "type": "string"
                                          }
                                        },
                                        "origin": {
                                          "type": "string"
                                        },
                                        "decisionId": {
                                          "type": "string"
                                        },
                                        "status": {
                                          "type": "string"
                                        },
                                        "cliVersion": {
                                          "type": "string"
                                        },
                                        "skillVersion": {
                                          "type": "string"
                                        },
                                        "requiredOutcome": {
                                          "type": "string"
                                        },
                                        "stage": {
                                          "type": "string"
                                        },
                                        "reason": {
                                          "type": "string"
                                        },
                                        "pr": {
                                          "type": "integer"
                                        },
                                        "head": {
                                          "type": "string"
                                        },
                                        "verdict": {
                                          "type": "string"
                                        },
                                        "reviewer": {
                                          "type": "string"
                                        },                                        "checkerFamily": {
                                          "type": "string"
                                        },                                        "checkerMode": {
                                          "type": "string"
                                        },
                                        "evidence": {
                                          "type": "string"
                                        },
                                        "acceptance": {
                                          "type": "string"
                                        },
                                        "classification": {
                                          "type": "string"
                                        },
                                        "humanReported": {
                                          "type": "boolean"
                                        },
                                        "explicit": {
                                          "type": "boolean"
                                        },
                                        "complete": {
                                          "type": "boolean"
                                        },
                                        "since": {
                                          "type": "string"
                                        },
                                        "until": {
                                          "type": "string"
                                        },
                                        "step": {
                                          "type": "string"
                                        },
                                        "area": {
                                          "type": "string"
                                        },
                                        "candidateVersion": {
                                          "type": "string"
                                        },
                                        "waitStage": {
                                          "type": "string"
                                        }
                                      },
                                      "required": [],
                                      "additionalProperties": false
                                    }
                                  },
                                  "required": [
                                    "schema",
                                    "id",
                                    "repo",
                                    "issue",
                                    "type",
                                    "at",
                                    "observedAt",
                                    "source",
                                    "data"
                                  ],
                                  "additionalProperties": false
                                }
                              },
                              "status": {
                                "type": "string"
                              }
                            },
                            "required": [
                              "mature",
                              "failedFixReports",
                              "status"
                            ],
                            "additionalProperties": false
                          }
                        },
                        "required": [
                          "7",
                          "30"
                        ],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "delivery",
                      "failedFixReports",
                      "followUp"
                    ],
                    "additionalProperties": false
                  }
                },
                "unassociatedFailedFixReports": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                },
                "unclassifiedReports": {
                  "type": "array",
                  "items": {
                    "type": "object",
                    "properties": {
                      "schema": {
                        "type": "string"
                      },
                      "id": {
                        "type": "string"
                      },
                      "repo": {
                        "type": "string"
                      },
                      "issue": {
                        "type": "integer"
                      },
                      "type": {
                        "type": "string"
                      },
                      "at": {
                        "type": "string"
                      },
                      "observedAt": {
                        "type": "string"
                      },
                      "source": {
                        "type": "string"
                      },
                      "attempt": {
                        "type": "string"
                      },
                      "data": {
                        "type": "object",
                        "properties": {
                          "snapshotId": {
                            "type": "string"
                          },
                          "inScope": {
                            "type": "boolean"
                          },
                          "state": {
                            "type": "string"
                          },
                          "reasons": {
                            "type": "array",
                            "items": {
                              "type": "string"
                            }
                          },
                          "origin": {
                            "type": "string"
                          },
                          "decisionId": {
                            "type": "string"
                          },
                          "status": {
                            "type": "string"
                          },
                          "cliVersion": {
                            "type": "string"
                          },
                          "skillVersion": {
                            "type": "string"
                          },
                          "requiredOutcome": {
                            "type": "string"
                          },
                          "stage": {
                            "type": "string"
                          },
                          "reason": {
                            "type": "string"
                          },
                          "pr": {
                            "type": "integer"
                          },
                          "head": {
                            "type": "string"
                          },
                          "verdict": {
                            "type": "string"
                          },
                          "reviewer": {
                            "type": "string"
                          },                          "checkerFamily": {
                            "type": "string"
                          },                          "checkerMode": {
                            "type": "string"
                          },
                          "evidence": {
                            "type": "string"
                          },
                          "acceptance": {
                            "type": "string"
                          },
                          "classification": {
                            "type": "string"
                          },
                          "humanReported": {
                            "type": "boolean"
                          },
                          "explicit": {
                            "type": "boolean"
                          },
                          "complete": {
                            "type": "boolean"
                          },
                          "since": {
                            "type": "string"
                          },
                          "until": {
                            "type": "string"
                          },
                          "step": {
                            "type": "string"
                          },
                          "area": {
                            "type": "string"
                          },
                          "candidateVersion": {
                            "type": "string"
                          },
                          "waitStage": {
                            "type": "string"
                          }
                        },
                        "required": [],
                        "additionalProperties": false
                      }
                    },
                    "required": [
                      "schema",
                      "id",
                      "repo",
                      "issue",
                      "type",
                      "at",
                      "observedAt",
                      "source",
                      "data"
                    ],
                    "additionalProperties": false
                  }
                }
              },
              "required": [
                "repo",
                "issue",
                "selection",
                "started",
                "validated",
                "delivered",
                "requiredOutcome",
                "promptOnlyStop",
                "origins",
                "attempts",
                "starts",
                "candidate",
                "checks",
                "ci",
                "steps",
                "deliveries",
                "reports",
                "failedFixReports",
                "followUp",
                "waits",
                "assistance",
                "coverage",
                "conflicts",
                "prCreated",
                "implementationReady",
                "failedFix",
                "deliveryFollowUps",
                "unassociatedFailedFixReports",
                "unclassifiedReports"
              ],
              "additionalProperties": false
            }
          },
          "queue": {
            "type": "object",
            "properties": {
              "ready": {
                "type": "object",
                "properties": {
                  "count": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "issue": {
                          "type": "integer"
                        },
                        "reasons": {
                          "type": "array",
                          "items": {
                            "type": "string"
                          }
                        }
                      },
                      "required": [
                        "issue",
                        "reasons"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "count",
                  "issues"
                ],
                "additionalProperties": false
              },
              "excluded": {
                "type": "object",
                "properties": {
                  "count": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "issue": {
                          "type": "integer"
                        },
                        "reasons": {
                          "type": "array",
                          "items": {
                            "type": "string"
                          }
                        }
                      },
                      "required": [
                        "issue",
                        "reasons"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "count",
                  "issues"
                ],
                "additionalProperties": false
              },
              "waiting": {
                "type": "object",
                "properties": {
                  "count": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "issue": {
                          "type": "integer"
                        },
                        "reasons": {
                          "type": "array",
                          "items": {
                            "type": "string"
                          }
                        }
                      },
                      "required": [
                        "issue",
                        "reasons"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "count",
                  "issues"
                ],
                "additionalProperties": false
              },
              "unknown": {
                "type": "object",
                "properties": {
                  "count": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "issue": {
                          "type": "integer"
                        },
                        "reasons": {
                          "type": "array",
                          "items": {
                            "type": "string"
                          }
                        }
                      },
                      "required": [
                        "issue",
                        "reasons"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "count",
                  "issues"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "ready",
              "excluded",
              "waiting",
              "unknown"
            ],
            "additionalProperties": false
          },
          "activity": {"oneOf": [{
            "type": "object",
            "properties": {
              "starts": {
                "type": "object",
                "properties": {
                  "count": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "events": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "schema": {
                          "type": "string"
                        },
                        "id": {
                          "type": "string"
                        },
                        "repo": {
                          "type": "string"
                        },
                        "issue": {
                          "type": "integer"
                        },
                        "type": {
                          "type": "string"
                        },
                        "at": {
                          "type": "string"
                        },
                        "observedAt": {
                          "type": "string"
                        },
                        "source": {
                          "type": "string"
                        },
                        "attempt": {
                          "type": "string"
                        },
                        "data": {
                          "type": "object",
                          "properties": {
                            "snapshotId": {
                              "type": "string"
                            },
                            "inScope": {
                              "type": "boolean"
                            },
                            "state": {
                              "type": "string"
                            },
                            "reasons": {
                              "type": "array",
                              "items": {
                                "type": "string"
                              }
                            },
                            "origin": {
                              "type": "string"
                            },
                            "decisionId": {
                              "type": "string"
                            },
                            "status": {
                              "type": "string"
                            },
                            "cliVersion": {
                              "type": "string"
                            },
                            "skillVersion": {
                              "type": "string"
                            },
                            "requiredOutcome": {
                              "type": "string"
                            },
                            "stage": {
                              "type": "string"
                            },
                            "reason": {
                              "type": "string"
                            },
                            "pr": {
                              "type": "integer"
                            },
                            "head": {
                              "type": "string"
                            },
                            "verdict": {
                              "type": "string"
                            },
                            "reviewer": {
                              "type": "string"
                            },                            "checkerFamily": {
                              "type": "string"
                            },                            "checkerMode": {
                              "type": "string"
                            },
                            "evidence": {
                              "type": "string"
                            },
                            "acceptance": {
                              "type": "string"
                            },
                            "classification": {
                              "type": "string"
                            },
                            "humanReported": {
                              "type": "boolean"
                            },
                            "explicit": {
                              "type": "boolean"
                            },
                            "complete": {
                              "type": "boolean"
                            },
                            "since": {
                              "type": "string"
                            },
                            "until": {
                              "type": "string"
                            },
                            "step": {
                              "type": "string"
                            },
                            "area": {
                              "type": "string"
                            },
                            "candidateVersion": {
                              "type": "string"
                            },
                            "waitStage": {
                              "type": "string"
                            }
                          },
                          "required": [],
                          "additionalProperties": false
                        }
                      },
                      "required": [
                        "schema",
                        "id",
                        "repo",
                        "issue",
                        "type",
                        "at",
                        "observedAt",
                        "source",
                        "data"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "count",
                  "issues",
                  "events"
                ],
                "additionalProperties": false
              },
              "candidateCompletions": {
                "type": "object",
                "properties": {
                  "count": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "events": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "schema": {
                          "type": "string"
                        },
                        "id": {
                          "type": "string"
                        },
                        "repo": {
                          "type": "string"
                        },
                        "issue": {
                          "type": "integer"
                        },
                        "type": {
                          "type": "string"
                        },
                        "at": {
                          "type": "string"
                        },
                        "observedAt": {
                          "type": "string"
                        },
                        "source": {
                          "type": "string"
                        },
                        "attempt": {
                          "type": "string"
                        },
                        "data": {
                          "type": "object",
                          "properties": {
                            "snapshotId": {
                              "type": "string"
                            },
                            "inScope": {
                              "type": "boolean"
                            },
                            "state": {
                              "type": "string"
                            },
                            "reasons": {
                              "type": "array",
                              "items": {
                                "type": "string"
                              }
                            },
                            "origin": {
                              "type": "string"
                            },
                            "decisionId": {
                              "type": "string"
                            },
                            "status": {
                              "type": "string"
                            },
                            "cliVersion": {
                              "type": "string"
                            },
                            "skillVersion": {
                              "type": "string"
                            },
                            "requiredOutcome": {
                              "type": "string"
                            },
                            "stage": {
                              "type": "string"
                            },
                            "reason": {
                              "type": "string"
                            },
                            "pr": {
                              "type": "integer"
                            },
                            "head": {
                              "type": "string"
                            },
                            "verdict": {
                              "type": "string"
                            },
                            "reviewer": {
                              "type": "string"
                            },                            "checkerFamily": {
                              "type": "string"
                            },                            "checkerMode": {
                              "type": "string"
                            },
                            "evidence": {
                              "type": "string"
                            },
                            "acceptance": {
                              "type": "string"
                            },
                            "classification": {
                              "type": "string"
                            },
                            "humanReported": {
                              "type": "boolean"
                            },
                            "explicit": {
                              "type": "boolean"
                            },
                            "complete": {
                              "type": "boolean"
                            },
                            "since": {
                              "type": "string"
                            },
                            "until": {
                              "type": "string"
                            },
                            "step": {
                              "type": "string"
                            },
                            "area": {
                              "type": "string"
                            },
                            "candidateVersion": {
                              "type": "string"
                            },
                            "waitStage": {
                              "type": "string"
                            }
                          },
                          "required": [],
                          "additionalProperties": false
                        }
                      },
                      "required": [
                        "schema",
                        "id",
                        "repo",
                        "issue",
                        "type",
                        "at",
                        "observedAt",
                        "source",
                        "data"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "count",
                  "issues",
                  "events"
                ],
                "additionalProperties": false
              },
              "validationResults": {
                "type": "object",
                "properties": {
                  "count": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "events": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "schema": {
                          "type": "string"
                        },
                        "id": {
                          "type": "string"
                        },
                        "repo": {
                          "type": "string"
                        },
                        "issue": {
                          "type": "integer"
                        },
                        "type": {
                          "type": "string"
                        },
                        "at": {
                          "type": "string"
                        },
                        "observedAt": {
                          "type": "string"
                        },
                        "source": {
                          "type": "string"
                        },
                        "attempt": {
                          "type": "string"
                        },
                        "data": {
                          "type": "object",
                          "properties": {
                            "snapshotId": {
                              "type": "string"
                            },
                            "inScope": {
                              "type": "boolean"
                            },
                            "state": {
                              "type": "string"
                            },
                            "reasons": {
                              "type": "array",
                              "items": {
                                "type": "string"
                              }
                            },
                            "origin": {
                              "type": "string"
                            },
                            "decisionId": {
                              "type": "string"
                            },
                            "status": {
                              "type": "string"
                            },
                            "cliVersion": {
                              "type": "string"
                            },
                            "skillVersion": {
                              "type": "string"
                            },
                            "requiredOutcome": {
                              "type": "string"
                            },
                            "stage": {
                              "type": "string"
                            },
                            "reason": {
                              "type": "string"
                            },
                            "pr": {
                              "type": "integer"
                            },
                            "head": {
                              "type": "string"
                            },
                            "verdict": {
                              "type": "string"
                            },
                            "reviewer": {
                              "type": "string"
                            },                            "checkerFamily": {
                              "type": "string"
                            },                            "checkerMode": {
                              "type": "string"
                            },
                            "evidence": {
                              "type": "string"
                            },
                            "acceptance": {
                              "type": "string"
                            },
                            "classification": {
                              "type": "string"
                            },
                            "humanReported": {
                              "type": "boolean"
                            },
                            "explicit": {
                              "type": "boolean"
                            },
                            "complete": {
                              "type": "boolean"
                            },
                            "since": {
                              "type": "string"
                            },
                            "until": {
                              "type": "string"
                            },
                            "step": {
                              "type": "string"
                            },
                            "area": {
                              "type": "string"
                            },
                            "candidateVersion": {
                              "type": "string"
                            },
                            "waitStage": {
                              "type": "string"
                            }
                          },
                          "required": [],
                          "additionalProperties": false
                        }
                      },
                      "required": [
                        "schema",
                        "id",
                        "repo",
                        "issue",
                        "type",
                        "at",
                        "observedAt",
                        "source",
                        "data"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "count",
                  "issues",
                  "events"
                ],
                "additionalProperties": false
              },
              "deliveries": {
                "type": "object",
                "properties": {
                  "count": {
                    "type": "integer"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "events": {
                    "type": "array",
                    "items": {
                      "type": "object",
                      "properties": {
                        "schema": {
                          "type": "string"
                        },
                        "id": {
                          "type": "string"
                        },
                        "repo": {
                          "type": "string"
                        },
                        "issue": {
                          "type": "integer"
                        },
                        "type": {
                          "type": "string"
                        },
                        "at": {
                          "type": "string"
                        },
                        "observedAt": {
                          "type": "string"
                        },
                        "source": {
                          "type": "string"
                        },
                        "attempt": {
                          "type": "string"
                        },
                        "data": {
                          "type": "object",
                          "properties": {
                            "snapshotId": {
                              "type": "string"
                            },
                            "inScope": {
                              "type": "boolean"
                            },
                            "state": {
                              "type": "string"
                            },
                            "reasons": {
                              "type": "array",
                              "items": {
                                "type": "string"
                              }
                            },
                            "origin": {
                              "type": "string"
                            },
                            "decisionId": {
                              "type": "string"
                            },
                            "status": {
                              "type": "string"
                            },
                            "cliVersion": {
                              "type": "string"
                            },
                            "skillVersion": {
                              "type": "string"
                            },
                            "requiredOutcome": {
                              "type": "string"
                            },
                            "stage": {
                              "type": "string"
                            },
                            "reason": {
                              "type": "string"
                            },
                            "pr": {
                              "type": "integer"
                            },
                            "head": {
                              "type": "string"
                            },
                            "verdict": {
                              "type": "string"
                            },
                            "reviewer": {
                              "type": "string"
                            },                            "checkerFamily": {
                              "type": "string"
                            },                            "checkerMode": {
                              "type": "string"
                            },
                            "evidence": {
                              "type": "string"
                            },
                            "acceptance": {
                              "type": "string"
                            },
                            "classification": {
                              "type": "string"
                            },
                            "humanReported": {
                              "type": "boolean"
                            },
                            "explicit": {
                              "type": "boolean"
                            },
                            "complete": {
                              "type": "boolean"
                            },
                            "since": {
                              "type": "string"
                            },
                            "until": {
                              "type": "string"
                            },
                            "step": {
                              "type": "string"
                            },
                            "area": {
                              "type": "string"
                            },
                            "candidateVersion": {
                              "type": "string"
                            },
                            "waitStage": {
                              "type": "string"
                            }
                          },
                          "required": [],
                          "additionalProperties": false
                        }
                      },
                      "required": [
                        "schema",
                        "id",
                        "repo",
                        "issue",
                        "type",
                        "at",
                        "observedAt",
                        "source",
                        "data"
                      ],
                      "additionalProperties": false
                    }
                  }
                },
                "required": [
                  "count",
                  "issues",
                  "events"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "starts",
              "candidateCompletions",
              "validationResults",
              "deliveries"
            ],
            "additionalProperties": false
          }, {"type": "null"}]},
          "stages": {
            "type": "object",
            "properties": {
              "started": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues"
                ],
                "additionalProperties": false
              },
              "validated": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues"
                ],
                "additionalProperties": false
              },
              "delivered": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "started",
              "validated",
              "delivered"
            ],
            "additionalProperties": false
          },
          "waits": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "issue": {
                  "type": "integer"
                },
                "stage": {
                  "type": "string"
                },
                "reason": {
                  "type": "string"
                },
                "since": {
                  "type": "string"
                },
                "elapsedMs": {
                  "type": "integer"
                },
                "source": {
                  "type": "string"
                },
                "reasons": {
                  "type": "array",
                  "items": {
                    "type": "string"
                  }
                },
                "requiredOutcome": {
                  "type": "string"
                },
                "promptOnlyStop": {
                  "type": "boolean"
                }
              },
              "required": [
                "issue",
                "stage",
                "reason",
                "since",
                "elapsedMs",
                "source",
                "reasons",
                "requiredOutcome",
                "promptOnlyStop"
              ],
              "additionalProperties": false
            }
          },
          "transitions": {
            "type": "object",
            "properties": {
              "autopilotStarts": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorIssues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorUnknown": {
                    "type": "integer"
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues",
                  "denominatorIssues",
                  "denominatorUnknown"
                ],
                "additionalProperties": false
              },
              "prCreation": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorIssues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorUnknown": {
                    "type": "integer"
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues",
                  "denominatorIssues",
                  "denominatorUnknown"
                ],
                "additionalProperties": false
              },
              "implementationReady": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorIssues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorUnknown": {
                    "type": "integer"
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues",
                  "denominatorIssues",
                  "denominatorUnknown"
                ],
                "additionalProperties": false
              },
              "validation": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorIssues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorUnknown": {
                    "type": "integer"
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues",
                  "denominatorIssues",
                  "denominatorUnknown"
                ],
                "additionalProperties": false
              },
              "delivery": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorIssues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorUnknown": {
                    "type": "integer"
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues",
                  "denominatorIssues",
                  "denominatorUnknown"
                ],
                "additionalProperties": false
              },
              "failedFix": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorIssues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorUnknown": {
                    "type": "integer"
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues",
                  "denominatorIssues",
                  "denominatorUnknown"
                ],
                "additionalProperties": false
              },
              "eligibility": {
                "type": "object",
                "properties": {
                  "numerator": {
                    "type": "integer"
                  },
                  "denominator": {
                    "type": "integer"
                  },
                  "unknown": {
                    "type": "integer"
                  },
                  "percentage": {
                    "oneOf": [
                      {
                        "type": "number"
                      },
                      {
                        "type": "null"
                      }
                    ]
                  },
                  "scope": {
                    "type": "object",
                    "properties": {
                      "kind": {
                        "type": "string"
                      },
                      "snapshotId": {
                        "type": "string"
                      },
                      "date": {
                        "type": "string"
                      }
                    },
                    "required": [
                      "kind"
                    ],
                    "additionalProperties": false
                  },
                  "observedAt": {
                    "type": "string"
                  },
                  "issues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorIssues": {
                    "type": "array",
                    "items": {
                      "type": "integer"
                    }
                  },
                  "denominatorUnknown": {
                    "type": "integer"
                  }
                },
                "required": [
                  "numerator",
                  "denominator",
                  "unknown",
                  "percentage",
                  "scope",
                  "observedAt",
                  "issues",
                  "denominatorIssues",
                  "denominatorUnknown"
                ],
                "additionalProperties": false
              }
            },
            "required": [
              "autopilotStarts",
              "prCreation",
              "implementationReady",
              "validation",
              "delivery",
              "failedFix",
              "eligibility"
            ],
            "additionalProperties": false
          }
        },
        "required": [
          "definitionVersion",
          "repo",
          "scope",
          "timezone",
          "observedAt",
          "sources",
          "coverage",
          "conflicts",
          "issues",
          "queue",
          "activity",
          "stages",
          "waits",
          "transitions"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [],
  "resources": [],
  "limits": {
    "max_steps": 12,
    "max_model_calls": 6
  },
  "conventions": []
}
```
</details>
