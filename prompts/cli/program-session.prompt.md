# Program sessions

Own src/program-session.mjs. Export module functions
`openProgramSession({root, file, program, data}, ports)` and
`closeProgramSession(session, ports)`. Open returns the interpreter's no-Story
session and metadata needed for calls; close stops that session with the existing
confirmed-stop protocol. file is the repository-relative entry, program its stable
name, data the programData result. Share these functions with app dispatch.

Reuse one session for unchanged program source/data/login. Capture only the entry
graph and compare reached prompt and dependency identity before reuse. On source
change replace automatically, carrying confirmed world; never require --new.
A fresh request invalidates saved answers and starts from selected initial data.
Unchanged input and data may reuse a confirmed result at0 calls. Never cache
failed/refused/unknown results or reuse another login's session. Retain pending
request IDs before dispatch; read ambiguous accepted work by GET only.
No synthetic Story/scenario is uploaded; the interpreter derives default fake
bindings for the graph. Session requests use entry, initial_world and optional
simulation, never seed. Preserve worlds, receipts, errors and call_chain unchanged.

## Dependencies

- [Runtime client](runtime-client.prompt.md): required native generation,
  verification/testing transport, authentication and confirmed-stop semantics.
- [Runtime preflight](runtime-preflight.prompt.md): required native generation,
  verification/testing entry graph privacy and source identity.
- [Program data](program-data.prompt.md): required native generation,
  verification/testing persisted world selection and record ownership.

## Runtime interface

Native session orchestration is tested with fake interpreter ports, without model
calls; it declares no model-executed operation.
