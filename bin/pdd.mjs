#!/usr/bin/env node
// Generated from prompts/cli/bin-entry.prompt.md (sha256: e4153b6d8a91242bcf2dc61b267a32560ff4e364443fb527b6556ac8c8cd5480).
// Check Node before anything loads: an old Node fails on pdd's modules with a raw error.
// So this file uses no static import, no top-level await and no newer syntax.
const major = Number(process.versions.node.split('.')[0]);
if (major < 22) {
  process.stderr.write(`pdd needs Node.js 22 or newer. You have ${process.version}. Update Node from https://nodejs.org, then run pdd again.\n`);
  process.exitCode = 1;
} else {
  import('../src/pdd-cli.mjs').then(async ({ runPdd }) => {
    const { releaseNotice } = await import('../src/release-notice.mjs');
    const { readFile } = await import('node:fs/promises');
    try {
      const pkg = JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
      const { notice } = await releaseNotice({ version: pkg.version, ci: process.env.CI });
      if (notice) process.stderr.write(notice);
    } catch {}
    process.exitCode = await runPdd(process.argv.slice(2));
  });
}
