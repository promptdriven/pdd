import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { allRuns, readRun, writeRun } from '../src/workflow-runs.mjs';

for (const errorCode of ['EISDIR', 'EACCES']) {
  for (const publish of [false, true]) test(`run index retries ${errorCode} after ${publish ? 'a run publication' : 'discovery'}`, t => {
    const root = fs.mkdtempSync(join(tmpdir(), 'pdd-index-retry-'));
    t.after(() => fs.rmSync(root, { recursive: true, force: true }));
    const stateDir = join(root, 'state'), indexFile = join(stateDir, 'runs.json');
    const commonDir = join(root, 'repo', '.git');
    const record = number => ({ v: 1, number, runId: `run-${number}`, repo: 'owner/repo',
      runDir: join(commonDir, 'pdd', 'runs', String(number)), commonDir,
      root: join(root, 'repo'), areas: [], chats: [], state: 'running' });
    const existing = record(7), next = record(8);
    fs.mkdirSync(existing.runDir, { recursive: true });
    fs.writeFileSync(join(existing.runDir, 'status.json'), JSON.stringify(existing));
    const indexBytes = JSON.stringify({ runs: [existing] });
    fs.mkdirSync(stateDir);
    if (errorCode === 'EISDIR') fs.mkdirSync(indexFile);
    else {
      fs.writeFileSync(indexFile, indexBytes);
      fs.chmodSync(indexFile, 0);
      if (process.getuid?.() === 0) return t.skip('root bypasses file read permissions');
    }
    assert.throws(() => fs.readFileSync(indexFile, 'utf8'), { code: errorCode });
    assert.deepEqual(allRuns({}, { stateDir }), []);
    if (publish) {
      writeRun(next, { stateDir });
      assert.equal(readRun(next.runDir).number, 8);
      // The failed update cannot consume the import through its empty-index path.
      assert.deepEqual(allRuns({}, { stateDir }), []);
    }
    if (errorCode === 'EISDIR') {
      fs.rmSync(indexFile, { recursive: true });
      fs.writeFileSync(indexFile, indexBytes);
    } else fs.chmodSync(indexFile, 0o600);
    // Discovery retries without another publication, including the saved run.
    for (let repeat = 0; repeat < 2; repeat++) {
      assert.deepEqual(allRuns({}, { stateDir }).map(run => run.number), publish ? [7, 8] : [7]);
    }
    assert.equal(fs.readFileSync(indexFile, 'utf8'), indexBytes);
  });
}
