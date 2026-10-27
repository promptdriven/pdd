#!/usr/bin/env node
// Generated from prompts/cli/bin-entry.prompt.md (sha256: bdd2c97e61c6be99e7036e5ee89e5af1a3e415f4a3b5a6e04774905902ae1066).
// Check Node before anything loads: an old Node fails on pdd's modules with a raw error.
// So this file uses no static import, no top-level await and no newer syntax.
const major = Number(process.versions.node.split('.')[0]);
if (major < 22) {
  process.stderr.write(`pdd needs Node.js 22 or newer. You have ${process.version}. Update Node from https://nodejs.org, then run pdd again.\n`);
  process.exitCode = 1;
} else {
  Promise.all([import('node:os'), import('node:url'), import('../src/skills-install.mjs'), import('../src/pdd-cli.mjs')])
    .then(async ([{ homedir }, { fileURLToPath }, { installSkills }, { runPdd }]) => {
      try { installSkills({ packageRoot: fileURLToPath(new URL('..', import.meta.url)), home: homedir(), claudeConfigDir: process.env.CLAUDE_CONFIG_DIR }); }
      catch (error) { process.stderr.write(`pdd: the PDD skills could not be installed in your home folder (${error.code || error.message}). pdd still runs.\n`); }
      process.exitCode = await runPdd(process.argv.slice(2));
    });
}
