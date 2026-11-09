# Verify missing PDD route parking

Use Node.js 22.16.0 or newer in a local checkout. No login, live service or agent account is needed.

Run the controlled public-boundary checks:

```sh
node --test test/autopilot-route-questions.test.mjs
node --test test/autopilot-parking.test.mjs test/autopilot-cli.test.mjs test/command-catalog.test.mjs test/docs-commands.test.mjs test/skills.test.mjs test/cost-ledger.test.mjs test/docs-first-time.test.mjs
```

The route checks use the repository's workflow fixture, real temporary Git repositories, fake Herdr and GitHub, and a controlled clock. The fixture supplies private `HOME`, `XDG_CONFIG_HOME` and `PDD_INTERPRETER_QUEUE`. Each fixture removes its files when the test ends.

The checks call the native workflow park API, CLI parser/dispatcher, coordinator tick and JSON status. They cover route classification, full question preservation, two reports before a tick, grouping and counting, one issue write per repeated kind, uncertain writes, installed capability wakes, retained sessions and independent gates/questions. Ordinary PDD/native vocabulary does not turn a product decision into a route gap. Local maintenance records questions without opening issues.

To check the regression control, copy the route test into a clean checkout of the candidate's parent and run it there. Expect the route parking, ledger, issue grouping and CLI route cases to fail at their behavior assertions. A setup or import failure does not establish the regression.

These checks prove native behavior with fake external ports. They do not prove live GitHub delivery, a real Herdr resume, the hosted interpreter or availability of a missing route. A release must advertise `route-KIND` in the installed workflow capabilities, or supply the explicit capability/ancestor-commit evidence named by the park. A version number or closed issue alone is insufficient.
