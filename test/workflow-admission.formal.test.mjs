import test from 'node:test';
import assert from 'node:assert/strict';
import { runPdd } from '../src/pdd-cli.mjs';

const states = ['ready', 'missing', 'signed_out', 'unavailable'];
const sink = () => ({ write() {} });

test('bounded Story rule: workflow admission requires the chosen ready or installed agent', async () => {
  for (const codex of states) for (const claude of states) for (const gemini of ['ready', 'missing', 'unavailable']) for (const requested of [undefined, 'codex', 'claude', 'gemini']) {
    const observed = { codex, claude, gemini };
    const expected = requested === undefined
      ? (codex === 'ready' ? 'codex' : claude === 'ready' ? 'claude' : gemini === 'ready' ? 'gemini' : null)
      : (observed[requested] === 'ready' ? requested : null);
    const starts = [];
    const run = async agent => {
      const state = observed[agent];
      if (state === 'missing') throw Object.assign(new Error('missing'), { code: 'ENOENT', executableMissing: true });
      if (state === 'unavailable') return { code: 2, stdout: 'invalid', stderr: '' };
      if (agent === 'gemini') return { code: 0, stdout: '0.67.1', stderr: '' };
      if (agent === 'codex') return { code: state === 'ready' ? 0 : 1, stdout: state === 'ready' ? 'Logged in' : 'Not logged in', stderr: '' };
      return { code: 0, stdout: JSON.stringify({ loggedIn: state === 'ready' }), stderr: '' };
    };
    const args = ['workflow', 'run', 'bug', '42', ...(requested ? ['--agent', requested] : [])];
    const code = await runPdd(args, { cwd: '/project', env: { HOME: '/home/test', PATH: '/bin' }, stdout: sink(), stderr: sink(), pathDiagnostic: () => [], workflowAgentPorts: { run }, workflowRunner: { startRun: async input => { starts.push(input.agent); return { exitCode: 0, message: 'Started' }; } } });
    const label = `codex=${codex} claude=${claude} gemini=${gemini} requested=${requested ?? 'omitted'}`;
    assert.equal(code, expected === null ? 1 : 0, label);
    assert.deepEqual(starts, expected === null ? [] : [expected], label);
  }
});
