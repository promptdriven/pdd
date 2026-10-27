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

## Real pack proof

This is the clean npm-installed pack run from `/home/serhan_asad_promptdriven_ai/work/2026-10-26/alpha-lane/wt/LAB-RECIPE.md`, with an isolated HOME/CODEX_HOME, one Herdr server, and the supplied direct Codex shim. The scratch checkout used `seed.txt` (the lab recipe's README seed was omitted so this proof does not edit README.md). The pack was installed at `/tmp/pdd-runs-real.ofPnAz/prefix`:

```text
$ /tmp/pdd-runs-real.ofPnAz/prefix/bin/pdd --version
0.1.0
$ sha256sum /tmp/pdd-runs-real.ofPnAz/pdd-0.1.0.tgz
0061f582f5bd0e404b7b995f1ee5a3ae34369ed0c06619ae0879d4fc098d6d7b  /tmp/pdd-runs-real.ofPnAz/pdd-0.1.0.tgz
```

The run and both reads were each captured by `script` in a real TTY. The command reached the first gate after a real `scope` stage:

```text
$ /tmp/pdd-runs-real.ofPnAz/prefix/bin/pdd workflow run small-change example/pdd-w4-smoke#100
waiting: run 0855c84f-1cd7-41e9-9cd0-80cf425a21f6 / change. Review the independent proposal and test plan; resume with approve to advance.
```

```text
$ /tmp/pdd-runs-real.ofPnAz/prefix/bin/pdd workflow runs
example/pdd-w4-smoke#100 Real runs-list lab 100 · small-change · waiting for you · age 1m · open: pdd workflow runs 0855c84f-1cd7-41e9-9cd0-80cf425a21f6
```

```text
$ /tmp/pdd-runs-real.ofPnAz/prefix/bin/pdd workflow runs 0855c84f-1cd7-41e9-9cd0-80cf425a21f6
example/pdd-w4-smoke#100 · small-change · waiting for you · worktree /tmp/pdd-runs-real.ofPnAz/root/repo.pdd-worktrees/2434d562-3352-4332-a374-34961258c072
scope · done · start 00:20:02 · end 00:20:58 · duration 56s · agent codex · codex session 01a17aba-98bf-71b1-9ae3-9be6ee0f6811 · reopen: cd '/tmp/pdd-runs-real.ofPnAz/root/repo.pdd-worktrees/2434d562-3352-4332-a374-34961258c072' && codex resume 01a17aba-98bf-71b1-9ae3-9be6ee0f6811
change · waiting · start unknown · end unknown · duration unknown · agent unknown
verify · next · start unknown · end unknown · duration unknown · agent unknown
open-pr · next · start unknown · end unknown · duration unknown · agent unknown
wait-merge · next · start unknown · end unknown · duration unknown · agent unknown
```

The exact printed command was copied and executed in another real `script` TTY. The `codex` on `PATH` was the recipe's direct native delegating shim, not an echo stub:

```text
$ cd '/tmp/pdd-runs-real.ofPnAz/root/repo.pdd-worktrees/2434d562-3352-4332-a374-34961258c072' && codex resume 01a17aba-98bf-71b1-9ae3-9be6ee0f6811
WARNING: proceeding, even though we could not create PATH aliases: Refusing to create helper binaries under temporary dir "/tmp" (codex_home: AbsolutePathBuf("/tmp/pdd-runs-real.ofPnAz/root/codex-home"))
... Codex alternate-screen UI ...
state=idle:app=codex
```

The resumed process was observed as `codex ... resume 01a17aba-98bf-71b1-9ae3-9be6ee0f6811` while the TTY was live, then stopped with Ctrl-C without changing the worktree. Full captures are `/tmp/pdd-runs-real.ofPnAz/real-run-final.tty.log`, `runs-list.tty.log`, `runs-detail.tty.log`, and `reopen.tty.log`.

The live process check (paths abbreviated) showed the same saved session id in both the Node launcher and native Codex child:

```text
node /opt/node/bin/codex ... resume 01a17aba-98bf-71b1-9ae3-9be6ee0f6811
.../vendor/.../codex ... resume 01a17aba-98bf-71b1-9ae3-9be6ee0f6811
```
