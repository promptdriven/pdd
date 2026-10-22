# Checks and evidence

Use commands supported by the installed release's `pdd --help`. Keep these results distinct:

- **Prompt checks** compare the prompt's behavior with expectations that a person authored and reviewed. They do not prove generated code.
- **Try** lets a person exercise proposed behavior when the installed release supports it. A link or saved design is not proof that an interaction occurred.
- **Code tests** exercise the implementation through a public code boundary. Keep test expectations independent from the implementation.
- **Formal analysis** is additional evidence only when a supported checker, rule, assumptions, and scope are stated. It does not replace behavior checks or person review; an unavailable formal check must be reported as unavailable.
- **Person review** decides whether the current PR revision meets the intended change. Only the person responsible for the repository merges it.

Report the command or tool actually used, the observed outcome, the revision checked, and material gaps. Do not turn an inconclusive result, an unavailable check, or a model answer into a pass.

The [synthetic ticket-status example](../examples/ticket-status/README.md) shows an ordinary Node test replaying example vectors. Its JSON shape belongs to that example; it is not a PDD runtime vector format.
