// Layer-0 direct subprocess execution and POSIX signal exit-code helpers.
import { spawn as nativeSpawn } from 'node:child_process';
import { lstatSync, statSync } from 'node:fs';
import { delimiter, isAbsolute, resolve } from 'node:path';

/**
 * Map a terminating POSIX signal name to its standard shell exit code (`128 + signum`).
 */
export function signalToExitCode(signal) {
  if (signal === 'SIGINT') return 130;
  if (signal === 'SIGTERM') return 143;
  if (signal === 'SIGHUP') return 129;
  return 1;
}

/**
 * Conservatively determine whether `ENOENT` means `command` has no installed candidate on the
 * effective search path (returning `false` for missing `cwd`, broken symlinks, or bad shebangs).
 */
export function executableMissing(command, { cwd, env } = {}) {
  try {
    const directory = cwd ?? process.cwd();
    const childEnv = env ?? process.env;
    if (!statSync(directory).isDirectory()) return false;
    const pathKey = process.platform === 'win32'
      ? Object.keys(childEnv).find(key => key.toLowerCase() === 'path')
      : (Object.hasOwn(childEnv, 'PATH') ? 'PATH' : undefined);
    const search = pathKey === undefined
      ? (process.platform === 'win32' ? (process.env.PATH ?? '') : '/usr/bin:/bin')
      : childEnv[pathKey];
    const qualified = isAbsolute(command) || /[\\/]/.test(command);
    const endings = process.platform === 'win32'
      ? ['', ...(childEnv.PATHEXT ?? '.COM;.EXE;.BAT;.CMD').split(';')]
      : [''];
    const candidates = qualified
      ? [resolve(directory, command)]
      : (search ?? '').split(delimiter).flatMap(folder => endings.map(ending => resolve(directory, folder || '.', command + ending)));
    for (const file of candidates) {
      try {
        lstatSync(file);
        return false;
      } catch (error) {
        if (error.code !== 'ENOENT') return false;
      }
    }
    return true;
  } catch {
    return false;
  }
}

/**
 * Execute a subprocess directly (`shell: false`) with bounded output capture, timeout,
 * `AbortSignal` cancellation, process-group `SIGTERM` -> `SIGKILL` cleanup, and conservative
 * `error.executableMissing` classification on `ENOENT`.
 */
export function runProcess(
  command,
  args,
  { cwd, env, input = '', signal, timeoutMs = 120_000, maxBytes = 131_072, spawn = nativeSpawn } = {},
) {
  return new Promise((resolveRun, rejectRun) => {
    if (signal?.aborted) {
      rejectRun(new Error('cancelled'));
      return;
    }
    let child;
    let stdout = '';
    let stderr = '';
    let size = 0;
    let settled = false;
    let killTimer;
    let stopping = false;

    const stop = () => {
      if (!child) return;
      stopping = true;
      try { process.kill(-child.pid, 'SIGTERM'); } catch { child.kill('SIGTERM'); }
      killTimer = setTimeout(() => {
        try { process.kill(-child.pid, 'SIGKILL'); } catch { child.kill('SIGKILL'); }
      }, 500);
      killTimer.unref();
    };

    const finish = (error, code) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      signal?.removeEventListener('abort', abort);
      if (error) {
        if (error.code === 'ENOENT') error.executableMissing = executableMissing(command, { cwd, env });
        if (error.stdout === undefined) error.stdout = stdout;
        error.stderr = stderr;
        rejectRun(error);
      } else {
        resolveRun({ code, stdout, stderr });
      }
    };

    const abort = () => {
      stop();
      finish(new Error('cancelled'));
    };

    const timer = setTimeout(() => {
      stop();
      finish(new Error('timeout'));
    }, timeoutMs);

    try {
      child = spawn(command, args, {
        cwd,
        env,
        stdio: ['pipe', 'pipe', 'pipe'],
        shell: false,
        detached: process.platform !== 'win32',
      });
    } catch (e) {
      finish(e);
      return;
    }

    signal?.addEventListener('abort', abort, { once: true });
    const onData = (kind, chunk) => {
      size += chunk.length;
      if (size > maxBytes) {
        stop();
        finish(new Error('output limit'));
        return;
      }
      if (kind === 'stdout') stdout += chunk;
      else stderr += chunk;
    };

    child.stdout.on('data', chunk => onData('stdout', chunk));
    child.stderr.on('data', chunk => onData('stderr', chunk));
    child.on('error', err => finish(err));
    child.on('close', code => {
      if (!stopping) clearTimeout(killTimer);
      finish(null, code);
    });
    child.stdin.on('error', () => {});
    child.stdin.end(input);
  });
}

/**
 * Spawn an interactive/passthrough command with `stdio: 'inherit'`, forwarding `SIGINT`/`SIGTERM`/`SIGHUP`
 * when no outer lifecycle handler owns signal dispatch, and mapping `ENOENT -> 127` and signals via `signalToExitCode`.
 */
export function spawnInheritedProcess(
  command,
  args,
  { cwd, env, onChild = null, spawn = nativeSpawn } = {},
) {
  return new Promise(resolveExit => {
    let child;
    try {
      child = spawn(command, args, { cwd, env, stdio: 'inherit' });
    } catch (err) {
      resolveExit({ exitCode: err?.code === 'ENOENT' ? 127 : 1, code: err?.code === 'ENOENT' ? 127 : 1, error: err });
      return;
    }
    onChild?.(child);
    const forward = sig => {
      try { child.kill?.(sig); } catch {}
    };
    const onSigInt = () => forward('SIGINT');
    const onSigTerm = () => forward('SIGTERM');
    const onSigHup = () => forward('SIGHUP');
    if (!onChild) {
      process.on('SIGINT', onSigInt);
      process.on('SIGTERM', onSigTerm);
      process.on('SIGHUP', onSigHup);
    }

    const detach = () => {
      onChild?.(null);
      if (!onChild) {
        process.off('SIGINT', onSigInt);
        process.off('SIGTERM', onSigTerm);
        process.off('SIGHUP', onSigHup);
      }
    };

    child.on('error', err => {
      detach();
      const code = err?.code === 'ENOENT' ? 127 : 1;
      resolveExit({ exitCode: code, code, error: err });
    });
    child.on('close', (code, signal) => {
      detach();
      const exitCode = typeof code === 'number'
        ? code
        : (signal ? signalToExitCode(signal) : 1);
      resolveExit({ exitCode, code: exitCode });
    });
  });
}
