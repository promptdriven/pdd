import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { releaseNotice } from '../src/release-notice.mjs';

test('bounded release ordering, accepted prefixes and CI suppression', async () => {
  const versions = [];
  for (let a = 0; a < 4; a++) for (let b = 0; b < 4; b++) for (let c = 0; c < 4; c++) versions.push([a, b, c]);
  for (const installed of versions) for (const latest of versions) {
    const old = installed.join('.'), next = latest.join('.');
    const newer = latest[0] > installed[0] || (latest[0] === installed[0] && (latest[1] > installed[1] || (latest[1] === installed[1] && latest[2] > installed[2])));
    for (const prefix of ['', 'v', 'alpha-v']) {
      const actual = await releaseNotice({ version: old, ci: false }, { latest: async () => ({ tag: prefix + next }) });
      const expected = newer ? `pdd ${old}: update available (${next}). Run: npm install -g github:promptdriven/pdd\n` : '';
      assert.equal(actual.notice, expected, `${old} ${prefix}${next}`);
    }
    let calls = 0;
    const ci = await releaseNotice({ version: old, ci: true }, { latest: () => { calls++; return { tag: next }; } });
    assert.equal(ci.notice, '');
    assert.equal(calls, 0);
  }
});
