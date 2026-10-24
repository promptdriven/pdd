# PDD executable entry

Own `bin/pdd.mjs`. Thin Node executable: import the local public `runPdd`, pass process.argv.slice(2), assign returned integer to process.exitCode. Keep bin name pdd, not pdd-alpha. No extra launcher, setup/install hook or private adapter.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.
