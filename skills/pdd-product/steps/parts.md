# parts

Read the approved map. For medium and large products, write `Boundaries` and `Runs`
in `product/plan.md`, plus a separate `## Prompts` section naming each part's
prompts and runnable startup boundary. Give each part its prompt folder with:
- Checkable domain and screen prompts verified by `pdd test` over injected `<port>.<op>` ports (never link `kind: native-only` adapters under their `## Dependencies`).
- Thin `kind: native-only` boundary adapters (`0` Runtime Stories, proved by native tests in `code`; RUNBOOK §21) that depend on the domain prompt for real HTTP/OAuth/SQLite/CLI/DOM shells.

Each part reads and writes only its own data; parts share data only via `contracts/`.
