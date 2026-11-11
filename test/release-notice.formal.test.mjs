import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { releaseNotice } from '../src/release-notice.mjs';

// Exhaust the bounded version space from the Story's comparison rules.
test('bounded release ordering and suppressed reads', async () => {
  let cases = 0;
  for (let installed = 0; installed < 27; installed++) {
    const current = [Math.floor(installed / 9), Math.floor(installed / 3) % 3, installed % 3].join('.');
    for (let available = 0; available < 27; available++) {
      const next = [Math.floor(available / 9), Math.floor(available / 3) % 3, available % 3].join('.');
      for (const prerelease of [false, true]) for (const ci of [false, true]) for (const probe of [false, true]) {
        const version = current + (prerelease ? '-rc.1' : '');
        const tag = `v${next}`;
        let reads = 0;
        const result = await releaseNotice({version, ci, probe}, {releases: {latest: async () => {
          reads++;
          return {tag};
        }}});
        const enabled = !ci && !probe;
        const newer = available > installed || (available === installed && prerelease);
        const expected = enabled && newer
          ? `pdd ${next} is available (installed ${version}). Update: npm install -g github:promptdriven/pdd#${tag}`
          : '';
        const context = `installed=${version} tag=${tag} ci=${ci} probe=${probe}`;
        assert.deepEqual(result, {message: expected}, context);
        assert.equal(reads, enabled ? 1 : 0, context);
        cases++;
      }
    }
  }
  assert.equal(cases, 5832);
});
