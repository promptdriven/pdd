#!/usr/bin/env node
// Generated from prompts/cli/pdd-codex.prompt.md.
const [major] = process.versions.node.split('.').map(Number);
if (major < 22) {
  process.stderr.write(`pdd-codex requires Node.js 22 or newer; found ${process.version}.\n`);
  process.exit(1);
}
const { runPddCodexCli } = await import('../src/pdd-codex.mjs');
const { exitCode } = await runPddCodexCli(process.argv.slice(2), {
  cwd: process.cwd(),
  env: process.env,
  stdout: process.stdout,
  stderr: process.stderr,
});
process.exit(exitCode);
