# visual

- Build screens and `.ui.svg` mockups only for user-facing pages; backend servers, routers and daemons stay screenless. Single-file UI runs from plain prose (`render` + `handle_event`, inline `<style>`) with no `app-map.json` (RUNBOOK §13).
- For a visible interface, sketch 2 or 3 options, with empty and error states. The person's choice sets appearance rules; until then, use your recommendation.
- Use plain customer words on every screen: never show internal IDs, schema keys, version counters or backend terms (`router`, `dispatches`, `fleet`), and explain setup steps on the card.
- Write `.ui.svg` mockups (and optional compact `app-map.json` for timers/routing/external CSS) when designing a multi-view layout or requested (RUNBOOK §13); single-file plain-prose UI needs no `app-map.json` for the Screen tab.
- Linked `.ui.svg` is the layout spec for parts, words, order, ids and states; keep prose and drawing aligned (RUNBOOK §13).
- Run `pdd lint --local` (`<50ms`) to verify `.ui.svg` XML, `viewBox`, labels, controls and regions. Render PNGs only if asked.
- Put any `.ui.svg` or optional app map paths in your `done` summary.
