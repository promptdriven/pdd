#!/usr/bin/env node
// Generated from prompts/cli/pdd-codex.prompt.md.
// Check Node before anything loads: an old Node fails on pdd's modules with a raw error.
// So this file uses no static import, no top-level await and no newer syntax.
const major = Number(process.versions.node.split('.')[0]);
if (major < 22) {
  process.stderr.write(`pdd-codex requires Node.js 22 or newer; found ${process.version}.\n`);
  process.exitCode = 1;
} else {
  import('../src/pdd-codex.mjs').then(async ({ runPddCodexCli }) => {
    const { exitCode } = await runPddCodexCli(process.argv.slice(2), {
      cwd: process.cwd(),
      env: process.env,
      stdin: process.stdin,
      stdout: process.stdout,
      stderr: process.stderr,
    });
    process.exitCode = exitCode;
  });
}
