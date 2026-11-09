import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as github from '../src/issue-dependencies-github.mjs';

// The fallback allows the old revision to produce an assertion counterexample.
const readManualHold = github.readManualHold ?? (async () => ({ held: false, known: false }));
const event = (event, login) => ({ event, label: { name: 'pdd:manual' }, actor: { login } });

function fixture({ permission = 'read', owner = 'owner', events = [event('labeled', 'author')], labels = ['pdd:manual'], failure = '' } = {}) {
  const calls = [];
  const ports = {
    github: {
      issue: async () => failure === 'issue' ? { json: '{}' } : { json: JSON.stringify({ labels }) },
      page: async ({ cursor }) => {
        if (failure === 'timeline' || failure === 'second-page' && cursor) throw Error('unavailable');
        const index = cursor ? Number(cursor) : 0;
        return { json: JSON.stringify({ items: events.slice(index, index + 1), next: index + 1 < events.length ? String(index + 1) : '' }) };
      },
    },
    // Keep a trusted author separate from native repository permission.
    authority: { read: async () => ({ authority: 'trusted' }) },
    execFile: async (_file, args) => {
      const endpoint = args.find(x => typeof x === 'string' && x.startsWith('repos/'));
      calls.push(endpoint);
      if (failure === 'repository' && endpoint === 'repos/owner/repo' || failure === 'permission' && endpoint?.includes('/permission')) throw Error('unavailable');
      const value = endpoint === 'repos/owner/repo' ? { owner: { login: owner } } : permission === 'missing' ? {} : { permission };
      return { stdout: JSON.stringify(value), code: 0 };
    },
  };
  return { ports, calls };
}

async function observe(options) {
  const f = fixture(options);
  return { result: await readManualHold({ repository: 'owner/repo', issue: 1 }, f.ports), calls: f.calls };
}

test('bounded manual label authority follows repository permissions and last application', async () => {
  const permissions = [
    ['admin', true, true], ['maintain', true, true], ['write', true, true],
    ['read', false, true], ['triage', false, true], ['none', false, true],
    ['malformed', false, false], ['missing', false, false],
  ];
  // All 8 permission values, for both one-page and three-page label histories.
  for (const [permission, held, known] of permissions) {
    for (const events of [[event('labeled', 'author')], [event('labeled', 'writer'), event('unlabeled', 'writer'), event('labeled', 'author')]]) {
      const { result } = await observe({ permission, events });
      assert.deepEqual(result, { held, known }, `permission ${permission}, ${events.length} pages`);
    }
  }
  const owner = await observe({ owner: 'AUTHOR', permission: 'none' });
  assert.deepEqual(owner.result, { held: true, known: true }, 'owner is authorized regardless of collaborator response');
  assert.equal(owner.calls.some(x => x?.includes('/permission')), false);
  assert.deepEqual((await observe({ labels: [], events: [event('unlabeled', 'author')] })).result, { held: false, known: true });
  assert.deepEqual((await observe({ events: [event('labeled', 'writer'), event('unlabeled', 'writer')] })).result, { held: false, known: false });
  for (const failure of ['issue', 'timeline', 'second-page', 'repository', 'permission']) {
    const events = [event('labeled', 'writer'), event('labeled', 'author')];
    assert.deepEqual((await observe({ failure, events })).result, { held: false, known: false }, `failure ${failure}`);
  }
});
