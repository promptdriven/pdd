## Daily Issue Report — 2026-06-01 (SF time) — INDEPENDENT (routine did not post)

> Window: 2026-06-01T07:00:00Z → 2026-06-02T06:59:59Z (America/Los_Angeles 00:00–23:59 on 2026-06-01).
> Generated manually by Claude. The claude.ai daily routine (`trig_01TcRZqPCfgzy7xPDctPSkyL`) has NOT posted for 2026-06-01 or 2026-06-02 (last #1694 comment 2026-05-31); the RemoteTrigger API returns HTTP 401 (expired OAuth token), so it could not be inspected or fired programmatically.
> `Karim13014` collapsed into `gltanaka` (alt account, GVS work via Claude Code). The automated routine does NOT do this collapse.

### Per-repo activity (raw, all states)
| Repo | Open (current) | Opened | Closed | Net Change |
|---|---|---|---|---|
| gltanaka/pdd | 2 | 0 | 0 | 0 |
| promptdriven/pdd_cloud | 249 | 23 | 3 | +20 |
| promptdriven/pdd | 160 | 13 | 16 | −3 |
| promptdriven/Generative-Video-Studio | 43 | 3 | 4 | −1 |
| **TOTAL** | **454** | **39** | **23** | **+16** |

### Leaderboard (Karim collapsed → gltanaka)
| Rank | Contributor | Score | PRs Merged | Issues Opened (open) |
|---|---|---|---|---|
| 1 | gltanaka | 47 | 15 | 2 |
| 2 | Serhan-Asad | 28 | 8 | 4 |
| 3 | DianaTao | 18 | 5 | 3 |
| 4 | sohni-tagirisa | 15 | 4 | 3 |
| 5 | RyanTanuki | 13 | 3 | 4 |
| 6 | aihuynh-pdd | 2 | 0 | 2 |

*Score = PR merged ×3 + open issue opened ×1. Closed issues excluded from scoring. PR true-author traced via commits / linked-issue assignee; bots receive no credit.*
*"Issues Opened (open)" counts only still-open issues, so it can be lower than the per-repo "Opened" total.*

> gltanaka's 15 PRs = 5 authored directly in promptdriven/pdd (#1351 #1332 #1326 #1319 #1314) + 10 GVS PRs commit-authored by Karim13014 (#600 #592 #591 #590 #589 #588 #587 #586 #585 #579). If Karim is kept separate (as the routine does), it's Karim 30 (#1) / gltanaka 17.

### Per-contributor breakdown
- **gltanaka — 15 PRs, 2 open issues.** pdd: #1351 (cloud-fix marker restore) #1332 #1326 (release video) #1319 (auto-heal metadata) #1314 (ANSI). GVS (as Karim13014): #600 #592 #591 #590 #589 #588 #587 #586 #585 #579 (subtitle/distribution/waitlist pipeline). Issues: pdd_cloud#1876 (Codex smoke test), pdd#1347 (token estimate).
- **Serhan-Asad — 8 PRs, 4 open issues.** PRs: pdd_cloud#1871 #1838(→#1832) #1875, pdd#1342 (revert #1329) #1329 #1325(→#1315) #1320(→#1305) #1310. Issues: pdd_cloud#1873 #1859, pdd#1341 #1318. (#1875 merged 00:15 SF on 06-02, 16 min past the day boundary — included per author.)
- **DianaTao — 5 PRs, 3 open issues.** PRs: pdd#1331 #1328 #1291 #1286 #1260 (waiver/contracts/grounding/steer/gate). Issues: pdd#1324 #1323 #1316.
- **sohni-tagirisa — 4 PRs, 3 open issues.** PRs (bot-opened, traced to sohni commits): pdd#1301 #1285 #1245 #1238. Issues: pdd#1338 #1335 #1330.
- **RyanTanuki — 3 PRs, 4 open issues.** GVS PRs: #548 #535(→#529) #532. Issues: pdd_cloud#1861 #1858, GVS#597 #593.
- **aihuynh-pdd — 2 open issues.** pdd_cloud#1863 #1862 (marketing outreach — not engineering; no rule excludes them).

### Exclusions applied
- **Claire's tickets (Rule 4):** pdd_cloud #1870 #1869 #1867 #1866 #1865 #1857 #1856 #1855 #1854 #1853 #1852 #1851 #1850 (claireevans101).
- **Sub-issues (Rule 1):** none (all candidates returned empty `sub_issues`).
- **Duplicates (Rule 2/3):** none found (titles distinct; not exhaustively query-verified).
- **Closed-issue exclusion (Rule 7, leaderboard scoring):** pdd_cloud#1874 #1849 #1848, pdd#1348 #1334 #1317 #1315 — opened in window but closed at report time, so no leaderboard credit (still counted in per-repo "Opened").
- **Identity collapse:** Karim13014 → gltanaka.

### Unresolved PR authorship
- **GVS#595** (brand-compliant dark retheme): all commits authored by login `claude` / `noreply@anthropic.com`, no linked issue → human author unattributable from git. Not credited. (Would not change rank #1 either way.)

### Summary
Heavy day: 35 PRs merged in-window across the four repos (+ Serhan's #1875 just past midnight). gltanaka leads (47) on the GVS subtitle/distribution pipeline; Serhan second (28, 8 PRs) on the Codex-auth/fingerprint/metadata thread. pdd repo net −3 (big closeout day). claireevans101's 13 marketing/hackathon tickets all excluded.

---
**Gaps:** the 2026-06-01 routine run was also missed, so SF day **2026-05-31** has no report either. The cron has missed 2 consecutive days — likely a server-side token failure (consistent with the 401), so re-firing once won't fix it; the routine needs a re-auth / health check on claude.ai.
