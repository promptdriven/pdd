#!/usr/bin/env node
// Generated from prompts/cli/bin-entry.prompt.md (sha256: d5e784c7f7cf23cbcb972eaeb7d24d58263e3388552534335fac14ecb522f43d).
// Check Node before anything loads: an old Node fails on pdd's modules with a raw error.
// So this file uses no static import, no top-level await and no newer syntax.
const major = Number(process.versions.node.split('.')[0]);
if (major < 22) {
  process.stderr.write(`pdd needs Node.js 22 or newer. You have ${process.version}. Update Node from https://nodejs.org, then run pdd again.\n`);
  process.exitCode = 1;
} else {
  import('../src/release-notice.mjs').then(async ({ releaseNotice }) => {
    try {
      const { readFile } = await import('node:fs/promises');
      const metadata = JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
      const ci = ['CI', 'GITHUB_ACTIONS', 'GITLAB_CI', 'CIRCLECI', 'TRAVIS', 'BUILDKITE', 'TF_BUILD', 'JENKINS_URL'].some(key => Boolean(process.env[key]));
      const result = await releaseNotice({ version: metadata.version, ci, probe: process.env.PDD_PATH_PROBE === '1' });
      if (result.message) process.stderr.write(result.message + '\n');
    } catch { /* A reminder failure must never prevent command dispatch. */ }
  }).catch(() => {}).then(() => import('../src/pdd-cli.mjs'))
    .then(async ({ runPdd }) => { process.exitCode = await runPdd(process.argv.slice(2)); });
}
