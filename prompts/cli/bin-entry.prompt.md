# PDD executable entry

Own `bin/pdd.mjs`. Thin Node executable. Keep the bin name pdd, not pdd-alpha. No extra launcher or private adapter.

## Node version first

npm only warns about `engines`, so pdd can start on an old Node. Check `process.versions.node` before anything else loads. If its major version is below 22, write exactly `pdd needs Node.js 22 or newer. You have <process.version>. Update Node from https://nodejs.org, then run pdd again.` and a newline to stderr, write nothing to stdout, and exit 1. Load nothing else and make no other check.

Static imports load before any code runs, and newer syntax fails to parse on an old Node. So this file has no static import, no top-level await, and no `??` or `?.`. It loads `runPdd` with dynamic `import()` only after the check passes. Check no other tool version (Herdr, Codex, Claude, git, gh): pdd does not pin them.

## Then run the command

Load the local public `runPdd`, pass process.argv.slice(2), and assign the returned integer to process.exitCode. The entry installs no skills: only `pdd setup` does that.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.
