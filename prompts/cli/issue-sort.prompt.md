# Sort issues before work

Own validation, freshness, routing decisions and groups. The coordinator supplies
semantic decisions in the same request as dependency review. PDD makes no model
call. Claims, trust and dependency review keep their existing meaning.

A sort record has schema_version pdd.issue-sort.v1, issue (full GitHub URL), base
(previous sort comment IDs), inputs (unique key/revision rows), belongs
({kind:area|repository|old-code|unknown,area,repository}), status
({state:still-happens|partly-fixed|fixed|unclear,release,fix,evidence}), genuine
({kind:bug|feature|docs|duplicate|not-genuine|unclear,duplicateOf,reason}), paths
(examined repo paths), rootCause (a short kebab-case tag or empty if unknown),
severity (high|medium|low), and question (empty or one question).
Require evidence, a fixing commit/PR/code locator for fixed, a different full
issue URL for duplicate, and a reason for not-genuine or old-code. Reject malformed
records before effects. A record must include its issue row, current area/release
row and every trusted requirement comment for its issue. Every examined input
must still have its recorded revision. Unrelated issues do not stale a record.
Trusted intact records supersede only their named base records. Conflicting heads
wait. New comments, source, release or area changes queue another sort.

`sortPlan({snapshot})` returns {queued,routes,groups}. Each route has issue,
action (work|close|assign|link|question|hold), area, owner, reason, record (or null),
umbrella (issue URL or empty), members (issue URLs), and evidence (string list).
Only open trusted issues in the root repo are considered. Unknown assignees,
human assignees and live claims hold; expired claims keep existing rules.
Fixed, duplicate, old-code and not-genuine take closure precedence over owner.
Otherwise resolve areas with autopilot-areas. Another owner is assign or link;
unknown owner is one question. Current unresolved local status is a question.
Only work routes can group. Same area and nonempty rootCause share one umbrella:
retain a running member if exactly one exists, else the lowest issue number.
Multiple running members hold the group. Do not group across areas or repository.
Members wait for that umbrella; group selection must not create a dependency
cycle or bypass the umbrella's ordinary eligibility. The dependency graph retains
its own links and reviews. The code PR for the umbrella closes every member.
