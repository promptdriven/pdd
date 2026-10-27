// Generated from prompts/cli/native-session.prompt.md (sha256: 9319c24c4ccd995e49592eb0b2b4ceb158a6407f2f4cc99cb588ac9a74773b1a).
import { spawn as spawnChild } from 'node:child_process';
import { constants } from 'node:os';
import { resolve as resolvePath } from 'node:path';

export function launchNativeSession({ agent, cwd, message, stderr = process.stderr },
  { spawn = spawnChild, signals = process, stdinIsTTY = Boolean(process.stdin.isTTY) } = {}) {
  if (!['codex', 'claude'].includes(agent)) return Promise.resolve(2);
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
        ? `The native ${agent} CLI is not on PATH. Install and sign in with that native tool, then run pdd session again.\n`
        : `The native ${agent} session could not be launched. Check that tool.\n`);
    };
    try { child = spawn(agent, agent === 'codex'
      ? ['--no-daemon', '--dangerously-bypass-approvals-and-sandbox', '-c', `projects={${JSON.stringify(resolvePath(cwd))}={trust_level="trusted"}}`, message]
      : ['--dangerously-skip-permissions', message], { cwd, stdio: 'inherit', shell: false, env: { ...process.env, PDD_AGENT_SESSION: '1' } }); }
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
