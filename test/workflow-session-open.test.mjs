import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';

// The independent boundary is argv observed by the native executable.
test('native reopen restricts tools, preserves cwd and sends no prompt', async () => {
  const { reopenNativeSession } = await import('../src/workflow-session-open.mjs');
  const id = '123e4567-e89b-42d3-a456-426614174001';
  for (const agent of ['codex', 'claude']) {
    const signals = new EventEmitter();
    const code = await reopenNativeSession({ session: { agent, id }, cwd: '/tmp/accepted' }, {
      signals, spawn(command, argv, options) {
        assert.equal(command, agent); assert.equal(options.cwd, '/tmp/accepted');
        assert.equal(options.shell, false); assert.equal(options.stdio, 'inherit');
        assert.equal(argv.at(-1), id);
        if (agent === 'codex') assert.deepEqual(argv, ['--sandbox', 'read-only', '--ask-for-approval', 'never', '-c', 'projects={"/tmp/accepted"={trust_level="trusted"}}', 'resume', id]);
        else assert.deepEqual(argv, ['--permission-mode', 'plan', '--tools', '', '--resume', id]);
        const child = new EventEmitter(); queueMicrotask(() => child.emit('close', 4)); return child;
      }
    });
    assert.equal(code, 4); assert.equal(signals.listenerCount('SIGTERM'), 0);
  }
});
test('native reopen rejects unsafe identity and reports absent executable', async () => {
  const { reopenNativeSession } = await import('../src/workflow-session-open.mjs');
  let text = ''; const stderr = { write(value) { text += value; } };
  assert.equal(await reopenNativeSession({session: {agent:'codex', id:'--bad'}, cwd:'/tmp', stderr}, {spawn(){assert.fail();}}), 1);
  assert.equal(await reopenNativeSession({session: {agent:'codex', id:'123e4567-e89b-42d3-a456-426614174001'}, cwd:'/tmp', stderr}, {spawn(){throw Object.assign(Error(), {code:'ENOENT'});}}), 127);
  assert.match(text, /not on PATH/);
});
