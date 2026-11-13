import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { setTimeout } from 'node:timers/promises';
import { launcher } from './helpers/environment-launcher-fixture.mjs';
import { environmentHealthy } from '../src/autopilot-environment.mjs';

test('standalone retry checks the supplied checkout volume', async () => {
  const seen = [];
  const ports = { platform: 'linux', cpuCount: () => 4, load: () => 1,
    memory: () => ({ available: 20, total: 100 }), readFile: () => 'some avg10=0.00 total=0',
    suiteAvailable: async () => true,
    statfs: cwd => { seen.push(cwd); return { bavail: cwd === '/checkout' ? 2 : 0, blocks: 20, bsize: 1024 ** 3 }; } };
  assert.equal(await environmentHealthy({ cwd: '/checkout', env: {} }, ports), true);
  assert.deepEqual(seen, ['/checkout']);
});

// #3048 AC8: the timer's working volume can differ from the checkout volume.
// #3048 AC1: malformed protocol input must normalize at the native child boundary.
for (const frame of [null, [], 'synthetic-private', 0, false]) {
  for (const phase of ['initialize', 'account/rateLimits/read']) {
    test(`native account transport returns unknown and stops its child for ${JSON.stringify(frame)} at ${phase}`, async t => {
      const dir = mkdtempSync(join(tmpdir(), 'pdd-health-frame-'));
      t.after(() => rmSync(dir, { recursive: true, force: true }));
      const file = join(dir, 'codex'), stopped = join(dir, 'stopped');
      writeFileSync(file, `#!${process.execPath}
const fs = require('node:fs');
const reader = require('node:readline').createInterface({ input: process.stdin });
const keepAlive = setInterval(() => {}, 1000);
// A broken shutdown must fail the marker check without leaving an orphan.
const lifetime = setTimeout(() => {
  clearInterval(keepAlive); reader.close(); process.stdin.destroy();
}, 10_000).unref();
// EOF must not end the process before its SIGTERM handler can write the marker.
process.on('SIGTERM', () => {
  clearTimeout(lifetime);
  // Make shutdown asynchronous so a signal alone cannot prove completion.
  setTimeout(() => {
    fs.writeFileSync(${JSON.stringify(stopped)}, 'stopped');
    clearInterval(keepAlive); reader.close(); process.stdin.destroy();
  }, 50);
});
reader.on('line', text => {
  const row = JSON.parse(text);
  if (row.method === ${JSON.stringify(phase)}) {
    console.log(${JSON.stringify(JSON.stringify(frame))});
    // A later valid reply cannot erase the preceding protocol error.
    console.log(JSON.stringify({ id: ${phase === 'initialize' ? 1 : 2}, result: ${phase === 'initialize' ? '{}' : '{ rateLimits: { primary: { usedPercent: 4, resetsAt: null } } }'} }));
  }
  else if (row.method === 'initialize') console.log(JSON.stringify({ id: 1, result: {} }));
  else if (row.method === 'account/rateLimits/read') console.log(JSON.stringify({ id: 2, result: { rateLimits: { primary: { usedPercent: 4, resetsAt: null } } } }));
});
`, { mode: 0o755 });
      const code = `import { readCodexLimits } from ${JSON.stringify(new URL('../src/codex-limits.mjs', import.meta.url).href)};
console.log(JSON.stringify(await readCodexLimits({ command: ${JSON.stringify(file)}, cwd: ${JSON.stringify(dir)} })));`;
      const reply = spawnSync(process.execPath, ['--input-type=module', '-e', code], { cwd: dir, encoding: 'utf8', timeout: 15_000 });
      assert.equal(reply.error, undefined, 'transport must finish within its bound');
      assert.equal(reply.status, 0, 'malformed frame must not crash the consumer');
      assert.deepEqual(JSON.parse(reply.stdout), { state: 'unknown', resetAt: null, usedPercent: null });
      assert.equal(reply.stderr, '', 'transport must not expose raw protocol diagnostics');
      const deadline = performance.now() + 5_000;
      while (!existsSync(stopped) && performance.now() < deadline) await setTimeout(10);
      assert.equal(readFileSync(stopped, 'utf8'), 'stopped');
    });
  }
}

// Release integration: #3048 and #3067 must use the same tick sample.
