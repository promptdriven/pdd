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

Pack proof on this Linux VM used `/tmp/pdd-runs-list-pack4.vDlmgx/prefix` and a real `script` TTY. The run of issue `promptdriven/pdd#2442` reached a saved `scope` recovery state after 32 seconds because the local Herdr/native launch timed out, so no finished stage session or reopen command was available. The same TTY then exercised `workflow runs` and `workflow runs 5dbe6eb2-5196-4ce0-800d-89fc154cdf0e --json`; output showed local clocks (`22:33:24`) and `unknown` for an unfinished duration, with no epoch milliseconds in human or JSON output.
