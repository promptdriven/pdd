# visual

- Build screens, `.ui.svg` mockups and an app map only for user-facing pages; backend servers, routers and daemons stay screenless.
- For a visible interface, sketch 2 or 3 options, with the empty and error states. The person's choice sets the prompt's appearance rules. Until they choose, use the option you recommend.
- Use plain customer words on every screen: never show internal IDs, schema keys, version counters or backend terms (`router`, `dispatches`, `fleet`), and explain setup steps or codes right on the card.
- For a page or a screen, also write the app map and its SVG mockups from that design (RUNBOOK §13), so `pdd simulate` shows the real screen (the Screen tab) and keys or taps work.
- Linked `.ui.svg` is the layout spec for parts, words, order, ids and states. Keep prose and drawing in agreement; follow RUNBOOK §13.
- Before showing the person, run `pdd lint --local`, render each `.ui.svg` to PNG in a headless browser, and inspect the image to fix overlaps, clipped borders, bad wrapping or crowded sections.
- Put the app map path in your `done` summary.
