#!/usr/bin/env node
// Generated from prompts/cli/pdd-claude.prompt.md.
const [major] = process.versions.node.split('.').map(Number);
if (major < 22) {
  process.stderr.write(`pdd-claude requires Node.js 22 or newer; found ${process.version}.\n`);
  process.exit(1);
}
const { runPddClaudeCli } = await import('../src/pdd-claude.mjs');
const { exitCode } = await runPddClaudeCli(process.argv.slice(2), {
  cwd: process.cwd(),
  env: process.env,
  stdout: process.stdout,
  stderr: process.stderr,
});
process.exit(exitCode);
