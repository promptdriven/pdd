# Dependency review before new issue work

Read the bundled prompts/cli/issue-dependencies-intake.prompt.md and its required
pure-model owner. Use their public boundaries; do not infer readiness from text.
This step leaves startup readiness, profiles, agent family and workflow handoff with
their existing owners. It is distinct from steps/handoff.md.

- When a wake names a request artifact, read its exact bytes and verify the
  declared SHA-256, valid request, opaque request ID and repository before any
  analysis or completion. Use that exact request for the existing completion;
  absent, unreadable, malformed or mismatched bytes leave the request pending,
  with no substitute prepare or completion based on another request. The artifact
  grants no start authority; retain current mode, ownership, graph and evidence
  checks. Without an artifact instruction, for unchecked or changed work run
  `pdd dependencies prepare`. Examine the actual
  trusted requirements/source packet, and send `{request,analysis}` to
  `pdd dependencies complete --input -`. Keep required source locators/revisions.
  Analyze a new issue's impact in both directions before replacing old heads.
- Reuse saved current reviews and completed unaffected impact. A stale or
  unchecked review is refreshed through the ordinary `pdd dependencies prepare`,
  analysis and `pdd dependencies complete --input -` path; do not treat its old
  result as current. Keep questions and unknown facts pending. After a review
  changes, read the graph again before starting affected work. A partial graph
  does not prove the backlog is empty: continue only issues already proved
  eligible, and keep checking the rest when the current graph is available.
  Graph reads use `pdd graph` and never trigger analysis.
- After the existing claim winner is established, retain the launcher's opaque
  coordinatorId in the same single claim comment that names the machine. Include a JSON object with string fields repository, coordinatorId, machine and labelEventId, matching the winning label event. Do not write `lastSeen`: the launcher tick adds it and keeps it current. Different
  coordinators on one machine keep different IDs. Reuse the existing label/event
  winner and [Autopilot claim rule](../SKILL.md); the current GitHub `Assignees`
  field is the source of human ownership. Keep the `pdd:working` claim until it
  is removed or expires ([handoff](handoff.md) steps 5-7), including during pause. A
  stopped launcher, or one in `off` mode, writes no `lastSeen`, so its claims expire after 4 hours. Add no claim lock or
  second service.
- Start with the ordinary workflow command. The launcher supplies the versioned
  coordinator context in the native agent environment; do not replace it. The
  workflow start binds the current winning comment and label event. Missing or
  unknown ownership waits. Explicit manual starts remain outside this context.
- Ordinary workflow start rereads current mode, ownership and the shared graph
  before replacing/releasing any run or claim, allocating or opening a new chat.
  A stale packet grants no authority. A different owner or Off stops new automatic
  starts; existing work may finish. The exact own winning claim alone must not
  block its first eligible start. Both observe and auto do issue work; a person
  merges in observe. Keep account/room/trust/activation/native custody rules.

Retain --runs as a concurrent cap. Current local starting/unconfirmed allocations
count as slots. Actual same-issue reuse adds no slot; an unknown count under a cap
waits. Ordinary start enforces this through the existing allocation owner, without
a separate cap lock/service. Use the allocation owner's existing occupied-slot classification. Paused, stuck
or question work yields only with confirmed no occupied worker. Labels/age do not
free a slot; unknown counts. Current saved cap wins over carried context. 

If ordinary automatic start reports current admission unavailable, keep the eligible
issue and its existing claim pending; retry the ordinary start on a later opportunity
after contention clears. Recheck current mode, ownership and graph at that boundary;
do not mark work complete or create a second claim.
