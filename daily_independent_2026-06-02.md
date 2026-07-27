## Daily Issue Report — 2026-06-02 (SF time) — manual run

> Window: 2026-06-02T07:00:00Z → 2026-06-03T06:59:59Z (America/Los_Angeles 00:00–23:59 on 2026-06-02).
> Generated manually (claude.ai daily routine still down — account can't reach the triggers API). Scoring: **PR ×10 + open issue ×3**. Karim13014 collapsed → gltanaka.

### Per-repo activity (raw, all states)
| Repo | Open (current) | Opened | Closed | Net Change |
|---|---|---|---|---|
| gltanaka/pdd | 2 | 0 | 0 | 0 |
| promptdriven/pdd_cloud | 257 | 18 | 12 | +6 |
| promptdriven/pdd | 162 | 10 | 12 | −2 |
| promptdriven/Generative-Video-Studio | 51 | 12 | 3 | +9 |
| **TOTAL** | **472** | **40** | **27** | **+13** |

### Leaderboard (Karim collapsed → gltanaka)
| Rank | Contributor | Score | PRs Merged | Issues Opened (open) |
|---|---|---|---|---|
| 1 | gltanaka | 168 | 15 | 6 |
| 2 | Serhan-Asad | 68 | 5 | 6 |
| 3 | RyanTanuki | 66 | 3 | 12 |
| 4 | DianaTao | 39 | 3 | 3 |
| 5 | sohni-tagirisa | 23 | 2 | 1 |
| 6 | aihuynh-pdd | 6 | 0 | 2 |

*Score = PR merged ×10 + open issue opened ×3. Closed issues excluded from scoring. PR true-author traced via commits / linked-issue assignee. Karim13014 → gltanaka. Bots receive no credit.*

### Per-contributor breakdown
- **gltanaka — 15 PRs, 6 open issues.** PRs: pdd_cloud #1903 #1902 #1897, pdd #1352 (release-video→Discord); GVS (as Karim13014) #621 #620 #619 #618 #616 #615 #614 #612 #608 #606 #584. Issues: GVS #625 #624 #623 #622 #617 #609 (staging infra/terraform/device-login).
- **Serhan-Asad — 5 PRs, 6 open issues.** PRs: pdd_cloud #1875 (OAuth preflight rotation) #1830 (#1822 breadcrumb) #1802 (Part of #1800, GH-App fingerprints), pdd #1369 (#1365) #1367 (#1364). Issues: pdd_cloud #1900 #1899 #1888 #1877 (hackathon-feature eng/security) #1892 (Codex Cloud Run), pdd #1363 (gemini-3.5-flash fallback).
- **RyanTanuki — 3 PRs, 12 open issues.** PRs: pdd_cloud #1809 (#1804), GVS #599 (#597) #542 (#526). Issues: pdd_cloud #1896 #1895 #1894 #1893 #1891 #1885 #1882 #1878 (pdd-issue/direct-agent harness + E2E), GVS #605 #604 #603 #602.
- **DianaTao — 3 PRs, 3 open issues.** PRs: pdd #1349 (pytest/contract slicing) #1345 (prompt snapshot/replay) #1336 (mid-run steering). Issues: pdd_cloud #1884, pdd #1371 #1370 (cross-language capability policy).
- **sohni-tagirisa — 2 PRs, 1 open issue.** PRs: pdd #1339 (#1338) #1309 (#1303, bot-opened→traced). Issue: pdd #1356.
- **aihuynh-pdd — 2 open issues.** pdd_cloud #1898 (SJSU marketing) #1879 (move project board to App).

### Exclusions applied
- **Sub-issues (Rule 1):** none (all candidates returned empty `sub_issues`).
- **Bots (no credit):** PRs #1809 #1802 #1309 #542 opened by bots → traced to human authors (Ryan/Serhan/sohni/Ryan). Issues pdd #1357 #1358 #1359 (prompt-driven-github[bot]) dropped.
- **Closed-issue exclusion (Rule 7):** created+closed in window → no credit: pdd_cloud #1901 ("test", Serhan) #1881 ("test:…", aihuynh); pdd #1365 #1364 #1353 (Serhan).
- **Hackathon (Rule 5) — JUDGMENT CALL:** kept #1900 #1899 #1888 #1877 as **engineering** (PII/auth security, race-condition fixes, registration bug) rather than event/marketing noise. ⚠️ Strict Rule 5 (drop any "hackathon" title) would remove these 4 from Serhan → Serhan 5 PR/2 iss = **56**, putting **RyanTanuki #2 (66)** and Serhan #3. Flagging so the rule can be codified.
- **Identity collapse:** Karim13014 → gltanaka.
- **Duplicates (Rule 2/3):** none affecting the leaderboard (closed dups #1281/#1148 excluded by Rule 7 anyway).

### Unresolved PR authorship
- **GVS#601** (light mode / theme toggle): commits authored by `claude` / `noreply@anthropic.com`, no linked issue → human author unattributable. Not credited. (Would collapse to gltanaka if attributed; does not change rank #1.)

### Summary
Very heavy day: 29 PRs merged. gltanaka dominant (168) on the GVS theme/editor/infra push; Serhan #2 (68) on OAuth/hackathon-hardening/GH-App work, edging Ryan (66) who filed 12 issues (pdd-issue harness + GVS bugs). 40 issues opened / 27 closed across the repos.
