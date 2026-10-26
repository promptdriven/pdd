# Test slice 2: runs-list

Candidate branch: `alpha-slice-runs-list` from `origin/alpha`. This is a draft proof for the lead's later `alpha-slices` pack.

1. **Install the pack.** From the directory containing the tarball:
   ```sh
   npm install -g --prefix /tmp/pdd-runs-list-prefix ./pdd-0.1.0.tgz
   /tmp/pdd-runs-list-prefix/bin/pdd --version
   ```
   Expect `0.1.0`.
2. **Run in a real TTY.** In a checkout with a GitHub issue and Herdr available:
   ```sh
   script -q -e -c '/tmp/pdd-runs-list-prefix/bin/pdd workflow run small-change OWNER/REPO#ISSUE' /dev/null
   ```
   Run through the first gate; record the printed run UUID.
3. **List and open the run.** In the same checkout:
   ```sh
   script -q -e -c '/tmp/pdd-runs-list-prefix/bin/pdd workflow runs' /dev/null
   script -q -e -c '/tmp/pdd-runs-list-prefix/bin/pdd workflow runs RUN_ID' /dev/null
   ```
   Expect repo/issue, workflow, state, local age, stage local start/end clocks and durations. Finished stages show a session id and `cd '<worktree>' && codex resume <id>` (or Claude's equivalent) when exactly one session file matches the worktree and stage time window.
4. **Reopen the finished scope session.** Copy the printed `reopen:` command and run it in the TTY; it resumes that native scope conversation without starting a new workflow stage.
5. **Rollback.** Replace the candidate with the baseline: `npm install -g --prefix /tmp/pdd-runs-list-prefix github:promptdriven/pdd#alpha` and confirm `/tmp/pdd-runs-list-prefix/bin/pdd --version` prints `0.1.0`.

Pack proof on this Linux VM used the clean npm prefix `/tmp/pdd-runs-review.JQgHTI/prefix` and a real `script` TTY. A completed `scope` journal and matching Codex session file were prepared in the scratch checkout `/tmp/pdd-runs-review.JQgHTI/repo`; the printed reopen command was then executed verbatim. The captured output was:

```text
23:17:07
example/scratch#42 runs-list pack proof · small-change · done · age 8s · open: pdd workflow runs 123e4567-e89b-42d3-a456-426614174000
23:17:08
example/scratch#42 · small-change · done · worktree /tmp/pdd-runs-review.JQgHTI/repo
scope · done · start 23:16:59 · end 23:17:03 · duration 4s · agent codex · codex session 123e4567-e89b-42d3-a456-426614174001 · reopen: cd '/tmp/pdd-runs-review.JQgHTI/repo' && codex resume 123e4567-e89b-42d3-a456-426614174001
23:17:08
REOPENED agent=codex args=resume 123e4567-e89b-42d3-a456-426614174001
```

The previous live GitHub issue attempt timed out before a finished stage; it is retained only as an earlier diagnostic and is not the slice proof.
