// Contract: prompts/cli/workflow-session-open.prompt.md.
import { spawn as spawnChild } from 'node:child_process';
import { constants } from 'node:os';

export function reopenNativeSession({ session, cwd, stderr = process.stderr },
  { spawn = spawnChild, signals = process, stdinIsTTY = Boolean(process.stdin.isTTY) } = {}) {
  const { agent, id } = session ?? {};
  if (!['codex', 'claude'].includes(agent) || !/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(id ?? '')
    || typeof cwd !== 'string' || !cwd.startsWith('/')) {
    stderr.write('The saved native session identity is unavailable.\n'); return Promise.resolve(1);
  }
  return new Promise(resolve => {
    let child, settled = false, launchError;
    const listeners = [];
    const finish = code => {
      if (settled) return; settled = true;
      for (const [name, fn] of listeners) signals.removeListener(name, fn);
      resolve(code);
    };
    const failed = error => {
      launchError = error;
      stderr.write(error?.code === 'ENOENT'
        ? `The native ${agent} CLI is not on PATH. Install and sign in with that native tool, then retry workflow open.\n`
        : `The native ${agent} session could not be launched. Check the native tool and saved session.\n`);
    };
    try { child = spawn(agent, agent === 'codex'
      ? ['--sandbox', 'read-only', '--ask-for-approval', 'never', 'resume', id]
      : ['--permission-mode', 'plan', '--tools', '', '--resume', id], { cwd, stdio: 'inherit', shell: false }); }
    catch (error) { failed(error); finish(error.code === 'ENOENT' ? 127 : 1); return; }
    for (const name of ['SIGINT', 'SIGTERM', 'SIGHUP']) {
      const fn = () => {
        // The inherited foreground terminal already sends Ctrl-C to both processes.
        if (name === 'SIGINT' && stdinIsTTY) return;
        try { child.kill(name); } catch { /* Still wait for the real child close. */ }
      };
      signals.on(name, fn); listeners.push([name, fn]);
    }
    child.once('error', failed);
    child.once('close', (code, signal) => finish(launchError ? launchError.code === 'ENOENT' ? 127 : 1
      : Number.isInteger(code) ? code : constants.signals[signal] ? 128 + constants.signals[signal] : 1));
  });
}
