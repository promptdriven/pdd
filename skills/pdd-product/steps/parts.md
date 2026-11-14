# parts

Read the approved map. For medium and large products, write the `Boundaries` and
`Runs` tables in `product/plan.md`, plus each part's planned prompts and runnable
startup boundary. Give each part its prompt folder and plan both kinds of modules:
- Checkable domain and screen prompts verified by `pdd test` over fake contract ports.
- Thin `"kind": "native-only"` adapter prompts (`0` Runtime Stories, proved by native
  tests in `code`; RUNBOOK §21) for real HTTP/HTTPS servers, OAuth/cookies, SQLite or
  external databases, CLI/OS processes and browser DOM/network shells.

Give `.ui.svg` drawings and `app-map.json` only to user-facing parts; backend
servers, routers and daemons stay screenless. Name what crosses each boundary and
what never crosses. Keep each run small; its `Needs` column names `plan PR` or
earlier runs. For large products, name each slice's journey and make slice 1 the
thinnest path through every part. For a small product, keep only the map and say
"run one feature run".
