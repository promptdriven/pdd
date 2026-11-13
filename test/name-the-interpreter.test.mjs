import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { runPdd } from '../src/pdd-cli.mjs';
import { sink } from './helpers/runtime-fake.mjs';

const KEEP = [/PDD_RUNTIME_URL/g, /Runtime check\b/g, /[Rr]untime interface/g, /prompt-runtime\.[a-z.-]+/g, /pdd check --read/g, /pdd-runtime-\w+/g];
function wordRule(output, marker, serverTexts = []) {
  if (marker) assert.match(output.split('\n').find(line => marker.test(line)) ?? '', /interpreter/, `${marker}: ${output}`);
  let rest = output;
  for (const text of serverTexts) { assert.ok(rest.includes(text), `server text passes through unchanged: ${text}`); rest = rest.split(text).join(''); }
  for (const word of KEEP) rest = rest.replace(word, '');
  assert.match(rest, /interpreter/, output);
  assert.doesNotMatch(rest, /runtime/i, output);
}

test('interpreter words: pdd jobs CLI reports an unreadable list using interpreter wording', async () => {
  const out = sink(), err = sink();
  assert.equal(await runPdd(['jobs'], { stdout: out, stderr: err, env: {}, runtimeSlots: { runJobs: async () => { throw Error('denied'); } } }), 5);
  assert.equal(out.text, ''); wordRule(err.text, /jobs/);
});
