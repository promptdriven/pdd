import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { autopilotGithubWorld } from './helpers/autopilot-github-world.mjs';

// A selected source has its own storage contract. The launcher fixture uses
// legacy files so this test needs no historical Git objects or network access.
for (const adapter of [false, true]) test(`GitHub world reads ${adapter ? 'the selected adapter' : 'a legacy source'} after stop`, async t => {
  const host = await autopilotGithubWorld({ issues: 1 });
  t.after(host.cleanup);
  const src = join(host.dir, 'selected-src');
  mkdirSync(src);
  writeFileSync(join(src, 'autopilot-launcher.mjs'), `
    import { mkdirSync, writeFileSync } from 'node:fs';
    import { join } from 'node:path';
    export function runAutopilotLauncher({command}, {stateRoot}) {
      mkdirSync(stateRoot, {recursive:true});
      writeFileSync(join(stateRoot, '0123456789abcdef0123.json'), JSON.stringify({enabled:command === 'start'}));
      return {exitCode:0};
    }
  `);
  writeFileSync(join(src, 'issue-dependencies-intake.mjs'), 'export {};');
  writeFileSync(join(src, 'github-calls.mjs'), 'export const nativeGithubCounter = exec => exec;');
  if (adapter) writeFileSync(join(src, 'autopilot-store.mjs'), `
    import { readFileSync, readdirSync } from 'node:fs';
    export const autopilotStateFiles = root => readdirSync(root).filter(name => name.endsWith('.json'));
    export const readAutopilotState = file => JSON.parse(readFileSync(file, 'utf8'));
  `);
  const world = await autopilotGithubWorld({ src, issues: 1 });
  t.after(world.cleanup);
  assert.equal((await world.invoke('start')).exitCode, 0);
  assert.equal(world.state().enabled, true);
  assert.equal((await world.invoke('stop')).exitCode, 0);
  assert.equal(world.state().enabled, false);
});
