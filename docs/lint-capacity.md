# Waiting for runtime capacity

When the runtime is busy and confirms that lint did not start, `pdd check`,
`pdd check --lint` and `pdd try` wait and try again. You see:

> The server is busy. Waiting for a lint slot…

Pdd follows the server's requested delay and keeps trying until your wait ends.
There is no fixed number of attempts. It keeps the same selected files and saves
every request ID. Check and remote lint use `--timeout` when you set it; otherwise
an agent waits 90 seconds and a terminal Check has no limit. Try keeps its
five-minute setup allowance and 90-second agent default. Waiting, retries and
lint all use the same time allowance.

If the server stays busy, pdd says that no checks ran and asks you to run the same
command again later. Check and lint exit with code 5; Try's `--cli` and `--serve`
wrappers exit with code 125.
No AI check or Try starts before lint passes. Lint uses no AI calls.

If a reply is lost, pdd reads the original request instead of sending it again.
It retries only when the runtime confirms that capacity prevented the job from
starting and that retrying is safe. Problems with the input need a correction.
Ctrl-C stops further submissions.

If lint is still queued or running when your wait ends, pdd says so and exits
with code 3. No checks or Try were sent. Check and explicit lint print a saved
batch that you can read with `pdd check --read BATCH`, without repeating lint.
The read shows the latest result and any prompt problems the runtime found.

After saved lint passes, a normal Check can start its original checks that were
waiting for lint. Pdd verifies the same owner and selected files, keeps the
original runtime address and call limits, and starts each check at most once,
even if reads overlap or stop halfway through. The read waits for `--timeout`,
or 90 seconds by default. Reading standalone lint never starts checks. Pdd also
leaves checks alone if they were already sent or their history is uncertain.
A missing or mismatched reply never counts as a pass.

Checks, remote lint and new Try setup share local slots across pdd processes,
repositories and worktrees. `PDD_MAX_JOBS` defaults to 4; invalid values warn and
use 4. Waiting jobs take turns in the order they arrived. Progress shows how many
slots are busy and how many jobs are ahead of you. `pdd jobs` lists active and
waiting local jobs without contacting the runtime or signing in.

Slot records live under `$PDD_STATE_DIR/slots/<runtime host>/` (the default state
directory is `~/.pdd/runtime`). The host and optional port are safely encoded in
the folder name. A job that may still be running keeps its slot after your
command stops waiting. If its local process dies, pdd reuses the slot only after
all recorded jobs are confirmed ended or after 30 minutes. A process ending
does not prove that the runtime job ended.

Before sending work, pdd asks whether the runtime has room. During announced
maintenance, it shows the end time and reason, waits, then asks again. It also
waits if a submission is refused because maintenance prevented the job from
starting. If the runtime does not offer capacity information, pdd uses the
reply to the submission instead. Other sign-in, access and service errors keep
their usual handling. A queued job keeps its ID while progress shows the queue
place and slot counts supplied by the runtime.

If the runtime confirms that a check ended because the service restarted, pdd
tries that Story row once more. It saves both request IDs, receipts and usage,
and prevents a second replacement across later or overlapping reads and retries.
Other uncertain outcomes and paid Try actions are never sent again automatically.
The [client prompt](../prompts/cli/runtime-client.prompt.md) and
[slots prompt](../prompts/cli/runtime-slots.prompt.md) define the exact retry
and slot rules.
