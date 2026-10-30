// PROPOSAL ONLY: command shape and behavior have not been approved by the person.
import test from 'node:test';
import assert from 'node:assert/strict';
import { runPdd } from '../src/pdd-cli.mjs';

const proposed = name => `2627 PROPOSAL (not approved): ${name}`;
function capture() { return { text: '', write(value) { this.text += value; } }; }
async function invoke(words, reply = { exitCode: 0, message: 'opened selected chat' }) {
  const stdout = capture(), stderr = capture(), calls = [];
  const cwd = '/synthetic/project', packageRoot = '/synthetic/pdd';
  const exitCode = await runPdd(['workflow', 'open', ...words], {
    stdout, stderr, cwd, packageRoot,
    workflowRunner: { openRun: async (...args) => { calls.push(args); return reply; } },
  });
  return { stdout, stderr, calls, exitCode, cwd, packageRoot };
}
function forwarded(out, extra, reply = { exitCode: 0, message: 'opened selected chat' }) {
  assert.equal(out.exitCode, reply.exitCode, 'CLI must reach openRun and return its result');
  assert.equal(out.calls.length, 1, 'Forward exactly once');
  assert.deepEqual(out.calls[0][0], { ref: '17', ...extra, cwd: out.cwd, packageRoot: out.packageRoot });
  assert.equal(typeof out.calls[0][1].say, 'function');
  assert.equal(reply.exitCode ? out.stderr.text : out.stdout.text, `${reply.message}\n`);
  assert.equal(reply.exitCode ? out.stdout.text : out.stderr.text, '');
}

test(proposed('runPdd forwards AREA and keeps the default call unchanged'), async () => {
  // These controls already pass on the base, before the proposed AREA assertion.
  forwarded(await invoke(['17']), {});
  for (const words of [[], ['17', '--unknown'], ['17', '--new', '--new'], ['17', 'plan', 'build']]) {
    const out = await invoke(words);
    assert.equal(out.exitCode, 2);
    assert.equal(out.calls.length, 0, 'Invalid syntax has no runner/native effect');
    assert.equal(out.stdout.text, '');
    assert.match(out.stderr.text, /Unsupported command or options/);
  }
  forwarded(await invoke(['17', 'plan']), { area: 'plan' });
});

test(proposed('runPdd forwards --new as newSession true'), async () => {
  forwarded(await invoke(['17', '--new']), { newSession: true });
});

test(proposed('runPdd forwards AREA and --new once and preserves a runner refusal'), async () => {
  const reply = { exitCode: 1, message: 'selected historical replacement refused' };
  forwarded(await invoke(['17', 'build', '--new'], reply), { area: 'build', newSession: true }, reply);
});
