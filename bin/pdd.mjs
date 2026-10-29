#!/usr/bin/env node
// Generated from prompts/cli/bin-entry.prompt.md (sha256: e0db2323c30ba39aa5aeb612feb9da6a09cff685fa559f4e55bfa1407922416f).
// Check Node before anything loads: an old Node fails on pdd's modules with a raw error.
// So this file uses no static import, no top-level await and no newer syntax.
const major = Number(process.versions.node.split('.')[0]);
if (major < 22) {
  process.stderr.write(`pdd needs Node.js 22 or newer. You have ${process.version}. Update Node from https://nodejs.org, then run pdd again.\n`);
  process.exitCode = 1;
} else {
  import('../src/pdd-cli.mjs').then(async ({ runPdd }) => { process.exitCode = await runPdd(process.argv.slice(2)); });
}
