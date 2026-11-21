# parts

Read the approved map. For medium and large products, write `Boundaries` and `Runs`
in `product/plan.md`, plus a separate `## Prompts` section naming each part's
prompts and runnable startup boundary. Give each part its prompt folder with:
- Checkable domain and screen prompts verified by `pdd test` over injected `<port>.<op>` ports (never link `kind: native-only` adapters under their `## Dependencies`).
- Complete `kind: native-only` boundary specification prompts (`0` Runtime Stories, proved by non-mocked real-host native tests in `code`; see `references/files.md` and RUNBOOK §21) that depend on the domain prompt and specify storage/DDL, locking, HTTP/wire/OS/auth boundaries, error mapping, and real-host verification cases rather than short stubs or mocked DI shells.

Each part reads and writes only its own data; parts share data only via `contracts/`. Give `.ui.svg` drawings and `app/maps/<part>.json` only to user-facing parts; backend servers, routers and daemons stay screenless. Keep each run small (`Needs` names `plan PR` or earlier runs) and list optional `Shared surfaces` (such as `cli`) on runs that update a shared entrypoint alongside their primary part. For large products, name each slice's journey and make slice 1 the thinnest path through every part; for a small product, keep only the map and say "run one feature run".
