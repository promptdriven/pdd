#!/usr/bin/env node
// Generated from prompts/cli/pdd-claude.prompt.md.
// Check Node before anything loads: an old Node fails on pdd's modules with a raw error.
// So this file uses no static import, no top-level await and no newer syntax.
const major = Number(process.versions.node.split('.')[0]);
if (major < 22) {
  process.stderr.write(`pdd-claude requires Node.js 22 or newer; found ${process.version}.\n`);
  process.exitCode = 1;
} else {
  import('../src/pdd-claude.mjs').then(async ({ runPddClaudeCli }) => {
    const { exitCode } = await runPddClaudeCli(process.argv.slice(2), {
      cwd: process.cwd(),
      env: process.env,
      stdout: process.stdout,
      stderr: process.stderr,
    });
    process.exitCode = exitCode;
  });
}
