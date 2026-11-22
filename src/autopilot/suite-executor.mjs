// Isolated test suite execution, process-group liveness, and signal diagnostics.
import * as files from 'node:fs';
import { spawn } from 'node:child_process';
import { safeEvidenceText } from '../validation-evidence.mjs';

export const delay = ms => new Promise(done => setTimeout(done, ms));

export function groupAlive(pgid) {
  try { process.kill(-pgid, 0); } catch (error) { return error.code === 'ESRCH' ? false : null; }
  if (process.platform !== 'linux') return true;
  // Orphaned zombies cannot execute or hold resources for a validation command.
  // A permission or parse error is uncertainty, never evidence of termination.
  try {
    for (const name of files.readdirSync('/proc').filter(name => /^\d+$/.test(name))) {
      let stat;
      try { stat = files.readFileSync(`/proc/${name}/stat`, 'utf8'); }
      catch (error) { if (error.code === 'ENOENT' || error.code === 'ESRCH') continue; return null; }
      const fields = stat.slice(stat.lastIndexOf(') ') + 2).split(' ');
      if (fields.length < 3) return null;
      if (Number(fields[2]) === pgid && !['Z', 'X'].includes(fields[0])) return true;
    }
    return false;
  } catch { return null; }
}

export const alive = pid => {
  if (pid < 0) return groupAlive(-pid) !== false;
  try { process.kill(pid, 0); return true; }
  catch (error) { return error.code !== 'ESRCH'; }
};

function readProcLine(path, fs = files) {
  try {
    const raw = fs.readFileSync(path, 'utf8');
    const first = String(raw).split(/\r?\n/).find(line => line.trim())?.trim() ?? '';
    return first ? safeEvidenceText(first.slice(0, 240)) : null;
  } catch { return null; }
}

export function collectSignalDiagnostics({
  signal = null,
  exitCode = null,
  phase = 'running',
  source = 'process-signal',
  pid = process.pid,
  ppid = process.ppid,
  queuedAt = null,
  startedAt = null,
  now = Date.now,
  fs = files,
} = {}) {
  const atMs = now();
  const safePid = Number.isSafeInteger(pid) && pid > 0 ? pid : null;
  const safePpid = Number.isSafeInteger(ppid) && ppid > 0 ? ppid : null;
  const readLiveProc = source === 'process-signal' && phase !== 'reconciled' && safePid === process.pid;
  const parentCommand = readLiveProc && safePpid ? readProcLine(`/proc/${safePpid}/comm`, fs) : null;
  const cgroup = readLiveProc && safePid ? readProcLine(`/proc/${safePid}/cgroup`, fs) : null;
  return {
    signal: typeof signal === 'string' && signal ? safeEvidenceText(signal) : null,
    exitCode: Number.isSafeInteger(exitCode) ? exitCode : null,
    phase: safeEvidenceText(String(phase ?? 'running')),
    source: safeEvidenceText(String(source ?? 'process-signal')),
    pid: safePid,
    ppid: safePpid,
    parentCommand,
    cgroup,
    elapsedMs: Number.isFinite(startedAt) ? Math.max(0, atMs - startedAt) : null,
    waitedMs: Number.isFinite(queuedAt) ? Math.max(0, (Number.isFinite(startedAt) ? startedAt : atMs) - queuedAt) : null,
    at: new Date(atMs).toISOString(),
  };
}

export function formatSignalDiagnostic(diag) {
  if (!diag || typeof diag !== 'object') return '';
  const parts = [
    diag.signal ? `signal=${diag.signal}` : null,
    diag.exitCode !== null && diag.exitCode !== undefined ? `exit=${diag.exitCode}` : null,
    diag.phase ? `phase=${diag.phase}` : null,
    diag.source ? `source=${diag.source}` : null,
    diag.pid ? `pid=${diag.pid}` : null,
    diag.ppid ? `ppid=${diag.ppid}` : null,
    diag.parentCommand ? `parent=${diag.parentCommand}` : null,
    diag.cgroup ? `cgroup=${diag.cgroup}` : null,
    Number.isFinite(diag.waitedMs) ? `waitedMs=${diag.waitedMs}` : null,
    Number.isFinite(diag.elapsedMs) ? `elapsedMs=${diag.elapsedMs}` : null,
  ].filter(Boolean);
  return safeEvidenceText(`Signal diagnostic: ${parts.join(' ')}`);
}

export async function executeSuite(command, { cwd, env, timeoutMs, onChild, onOutput, startGate = false, cpuIds = [], taskset = null }, ports = {}) {
  return new Promise(done => {
    const file = taskset ?? '/bin/bash';
    const args = taskset ? ['--cpu-list', cpuIds.join(','), '/bin/bash', '-c', command] : ['-c', command];
    const child = (ports.spawn ?? spawn)(
      startGate ? '/bin/bash' : file,
      startGate ? ['-c', 'read -r _pdd_gate; exec "$@" </dev/null', 'pdd-suite-gate', file, ...args] : args,
      { cwd, env, detached: true, stdio: [startGate ? 'pipe' : 'ignore', onOutput ? 'pipe' : 'inherit', onOutput ? 'pipe' : 'inherit'] },
    );
    if (onOutput) {
      for (const stream of ['stdout', 'stderr']) {
        child[stream]?.on('data', bytes => {
          try { onOutput(stream, bytes); }
          catch (error) { stop(1, `Test suite output could not be saved: ${error.code ?? error.message}`); }
        });
      }
    }
    child.stdin?.on('error', () => {});
    const startedAt = (ports.now ?? Date.now)();
    let reason = null;
    let forcedCode = null;
    let forcedSignal = null;
    let signalDiagnostics = null;
    let escalation;
    const killGroup = signal => {
      if (child.pid) {
        try { (ports.kill ?? process.kill)(-child.pid, signal); }
        catch (error) { if (error.code !== 'ESRCH') throw error; }
      }
    };
    const stop = (code, why, sig = null) => {
      if (forcedCode !== null) return;
      forcedCode = code;
      reason = why;
      if (sig) {
        forcedSignal = sig;
        signalDiagnostics = collectSignalDiagnostics({
          signal: sig,
          exitCode: code,
          phase: 'running',
          source: 'process-signal',
          pid: process.pid,
          ppid: process.ppid,
          startedAt,
          now: ports.now ?? Date.now,
          fs: ports.fs ?? files,
        });
      }
      killGroup('SIGTERM');
      escalation = setTimeout(() => killGroup('SIGKILL'), 2000);
    };
    const interrupt = () => stop(130, 'Test suite interrupted (SIGINT).', 'SIGINT');
    const terminate = () => stop(143, 'Test suite interrupted (SIGTERM).', 'SIGTERM');
    process.on('SIGINT', interrupt);
    process.on('SIGTERM', terminate);
    const timer = timeoutMs ? setTimeout(() => stop(124, `Test suite execution timeout after ${timeoutMs / 60_000} minutes.`), timeoutMs) : null;
    const cleanup = () => {
      clearTimeout(timer);
      clearTimeout(escalation);
      process.off('SIGINT', interrupt);
      process.off('SIGTERM', terminate);
      killGroup('SIGKILL');
    };
    let settled = false;
    const finish = async result => {
      if (settled) return;
      settled = true;
      cleanup();
      const effectiveSignal = result.signal ?? forcedSignal ?? null;
      const diag = signalDiagnostics ?? (effectiveSignal ? collectSignalDiagnostics({
        signal: effectiveSignal,
        exitCode: result.exitCode ?? null,
        phase: 'child-signal',
        source: 'child-close',
        pid: child.pid ?? process.pid,
        ppid: process.ppid,
        startedAt,
        now: ports.now ?? Date.now,
        fs: ports.fs ?? files,
      }) : null);
      let ownershipConfirmed = !child.pid;
      if (child.pid) {
        for (let attempt = 0; attempt <= 100; attempt++) {
          let live;
          try { live = (ports.groupAlive ?? groupAlive)(child.pid); } catch { live = null; }
          if (live === false) { ownershipConfirmed = true; break; }
          if (attempt < 100) await (ports.sleep ?? delay)(20);
        }
      }
      done(ownershipConfirmed
        ? { ...result, ...(result.reason == null ? {} : { reason: safeEvidenceText(result.reason) }), ...(diag ? { signalDiagnostics: diag } : {}), ownershipConfirmed: true }
        : { exitCode: 1, signal: effectiveSignal, ...(diag ? { signalDiagnostics: diag } : {}), reason: 'Test suite descendants could not be confirmed stopped.', ownershipConfirmed: false });
    };
    child.once('error', error => { void finish({ exitCode: 1, reason: `Test suite could not start: ${error.code ?? error.message}` }); });
    child.once('close', (code, signal) => { void finish({ signal, exitCode: forcedCode ?? code ?? 1, reason: reason ?? (signal ? `Test suite ended by ${signal}.` : null) }); });
    try { if (child.pid) onChild(child.pid); if (startGate) child.stdin.end('\n'); }
    catch (error) { stop(1, `Test suite could not save its child ownership: ${error.code ?? error.message}`); }
  });
}
