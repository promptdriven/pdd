import test from 'node:test';
import assert from 'node:assert/strict';
import { autopilotGithubWorld } from './helpers/autopilot-github-world.mjs';

test('launcher index stops pagination at reserve and retains complete coverage', async t => {
  const w = await autopilotGithubWorld({ issues: 200 }); t.after(w.cleanup);
  w.github.busy();
  assert.equal((await w.invoke('start')).exitCode, 0);
  const before = w.state();
  w.time += 7 * 60 * 60000;
  const run = w.ports.run, pages = [];
  w.ports.run = async (file, args, options = {}) => {
    if (file === 'gh' && args.some(a => a.includes('/issues?') && a.includes('sort=updated') && !a.includes('since='))) {
      if (!pages.length) {
        w.github.remaining = 1000;
        w.github.edit(200, 'Updated first page'); w.github.edit(100, 'Updated second page');
      }
      pages.push(w.github.remaining);
    }
    return run(file, args, options);
  };
  await w.tick();
  assert.deepEqual(pages, [1000]);
  const after = w.state();
  for (const key of ['cachedIssues', 'pages', 'issuesSince', 'issuesFullAt']) assert.deepEqual(after[key], before[key], key);
});
