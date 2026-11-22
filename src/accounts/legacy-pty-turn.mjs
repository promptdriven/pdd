// Generated from prompts/cli/accounts-cli.prompt.md.
// Legacy single-turn supervised Python PTY runner (kept behind PDD_LEGACY_PTY_ROTATE=1).
import { spawn } from 'node:child_process';
import { stripAnsiText } from './import-auth.mjs';
import {
  checkCloudAccountQuotaExhausted,
  discoverPinnedCodexRollout,
  findRolloutPathBySessionId,
  inspectRolloutQuotaError,
  OUTPUT_SESSION_ID_RE,
  UUID_TOKEN_RE,
} from './legacy-pty-rollout.mjs';

const PYTHON_PTY_SUPERVISOR_SCRIPT = [
  'import errno, fcntl, os, pty, select, signal, struct, sys, termios, time',
  'initial_ppid = os.getppid()',
  'rows = int(os.environ.get("PDD_PTY_ROWS", "24") or "24")',
  'cols = int(os.environ.get("PDD_PTY_COLS", "80") or "80")',
  'master_fd, slave_fd = pty.openpty()',
  'try:',
  '    fcntl.ioctl(slave_fd, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))',
  'except Exception:',
  '    pass',
  'pid = os.fork()',
  'if pid == 0:',
  '    os.close(master_fd)',
  '    try:',
  '        os.close(3)',
  '    except Exception:',
  '        pass',
  '    os.setsid()',
  '    try:',
  '        fcntl.ioctl(slave_fd, termios.TIOCSCTTY, 0)',
  '    except Exception:',
  '        pass',
  '    os.dup2(slave_fd, 0)',
  '    os.dup2(slave_fd, 1)',
  '    os.dup2(slave_fd, 2)',
  '    if slave_fd > 2:',
  '        os.close(slave_fd)',
  '    os.execvp(sys.argv[1], sys.argv[1:])',
  'os.close(slave_fd)',
  'ctrl_open = True',
  'try:',
  '    fcntl.fcntl(3, fcntl.F_GETFD)',
  'except OSError:',
  '    ctrl_open = False',
  'def _killpg_safe(sig):',
  '    try:',
  '        os.killpg(pid, sig)',
  '        return True',
  '    except ProcessLookupError:',
  '        return False',
  '    except Exception:',
  '        try:',
  '            os.kill(pid, sig)',
  '            return True',
  '        except ProcessLookupError:',
  '            return False',
  '        except Exception:',
  '            return False',
  'stop_requested = False',
  'def _fwd(signum, _frame):',
  '    global stop_requested',
  '    _killpg_safe(signum)',
  '    if signum in (signal.SIGTERM, signal.SIGHUP):',
  '        stop_requested = True',
  'for _s in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):',
  '    signal.signal(_s, _fwd)',
  'reaped_status = None',
  'def _terminate_child_group():',
  '    global reaped_status',
  '    if reaped_status is not None:',
  '        return',
  '    if not _killpg_safe(signal.SIGTERM):',
  '        return',
  '    deadline = time.monotonic() + 0.5',
  '    while time.monotonic() < deadline:',
  '        try:',
  '            wpid, st = os.waitpid(pid, os.WNOHANG)',
  '            if wpid == pid:',
  '                reaped_status = st',
  '                return',
  '        except ChildProcessError:',
  '            reaped_status = 0',
  '            return',
  '        time.sleep(0.02)',
  '    _killpg_safe(signal.SIGKILL)',
  'def _drain_master_nonblocking():',
  '    while True:',
  '        try:',
  '            rdy, _, _ = select.select([master_fd], [], [], 0)',
  '            if not rdy:',
  '                break',
  '            chunk = os.read(master_fd, 16384)',
  '            if not chunk:',
  '                break',
  '            os.write(1, chunk)',
  '        except Exception:',
  '            break',
  'stdin_open = True',
  'ctrl_buf = b""',
  'while True:',
  '    if stop_requested or os.getppid() == 1 or os.getppid() != initial_ppid:',
  '        _terminate_child_group()',
  '        break',
  '    watch = [master_fd] + ([0] if stdin_open else []) + ([3] if ctrl_open else [])',
  '    try:',
  '        rlist, _, _ = select.select(watch, [], [], 0.2)',
  '    except InterruptedError:',
  '        continue',
  '    except Exception:',
  '        _terminate_child_group()',
  '        break',
  '    if master_fd in rlist:',
  '        try:',
  '            data = os.read(master_fd, 16384)',
  '        except OSError as exc:',
  '            if exc.errno == errno.EIO:',
  '                break',
  '            raise',
  '        if not data:',
  '            break',
  '        os.write(1, data)',
  '    if ctrl_open and 3 in rlist:',
  '        try:',
  '            cdata = os.read(3, 4096)',
  '        except OSError:',
  '            cdata = b""',
  '        if not cdata:',
  '            ctrl_open = False',
  '            _terminate_child_group()',
  '            break',
  '        ctrl_buf += cdata',
  '        while b"\\n" in ctrl_buf:',
  '            line, ctrl_buf = ctrl_buf.split(b"\\n", 1)',
  '            parts = line.strip().split()',
  '            if len(parts) == 2:',
  '                try:',
  '                    r_val, c_val = int(parts[0]), int(parts[1])',
  '                    if r_val > 0 and c_val > 0:',
  '                        fcntl.ioctl(master_fd, termios.TIOCSWINSZ, struct.pack("HHHH", r_val, c_val, 0, 0))',
  '                        _killpg_safe(signal.SIGWINCH)',
  '                except Exception:',
  '                    pass',
  '    if stdin_open and 0 in rlist:',
  '        try:',
  '            inp = os.read(0, 16384)',
  '        except OSError:',
  '            inp = b""',
  '        if not inp:',
  '            stdin_open = False',
  '            _terminate_child_group()',
  '            break',
  '        else:',
  '            try:',
  '                os.write(master_fd, inp)',
  '            except OSError:',
  '                break',
  '_drain_master_nonblocking()',
  'try:',
  '    os.close(master_fd)',
  'except Exception:',
  '    pass',
  'if ctrl_open:',
  '    try:',
  '        os.close(3)',
  '    except Exception:',
  '        pass',
  'if reaped_status is None:',
  '    try:',
  '        _, reaped_status = os.waitpid(pid, 0)',
  '    except ChildProcessError:',
  '        reaped_status = 0',
  'if os.WIFSIGNALED(reaped_status):',
  '    sys.exit(128 + os.WTERMSIG(reaped_status))',
  'sys.exit(os.WEXITSTATUS(reaped_status))',
].join('\n');

export async function runSingleSupervisedCodexTurn({
  fs, args, cwd, env, stdin, stdout, stderr, turn, turnStartedMs, activeEntry, codexHomes,
  preSpawnSnapshot, expectedCwd, sessionState, excludedSessionId = null, initialRolloutOffset = 0,
}, ports = {}) {
  let rollingPlain = '', capturedSessionId = null, quotaExhausted = false, quotaReasonText = '';
  let exhaustedAccountSnapshot = null, rolloutOffset = initialRolloutOffset, abortedByParentSignal = null;
  const abortController = new AbortController();
  const settleMs = ports.quotaSettleMs ?? 60;
  const rolloutPollMs = ports.rolloutPollIntervalMs ?? 200;
  const cloudPollMs = ports.cloudQuotaPollIntervalMs ?? 0;

  const inspectChunk = rawChunk => {
    const clean = stripAnsiText(String(rawChunk ?? ''));
    if (!clean) return;
    const sidMatch = OUTPUT_SESSION_ID_RE.exec(clean);
    if (sidMatch?.[1]) capturedSessionId = sidMatch[1];
    rollingPlain = `${rollingPlain}${clean}`.slice(-16_384);
  };
  const triggerStructuredQuotaAbort = (reasonText, cloudAccount = null) => {
    if (quotaExhausted) return;
    quotaExhausted = true;
    quotaReasonText = String(reasonText || 'usage_limit_reached');
    if (cloudAccount) exhaustedAccountSnapshot = cloudAccount;
    abortController.abort();
  };
  const pollRolloutOnce = () => {
    if (!sessionState.rolloutPath) {
      if (sessionState.sessionId) {
        const foundPath = findRolloutPathBySessionId(fs, codexHomes, sessionState.sessionId);
        if (foundPath) { sessionState.rolloutPath = foundPath; rolloutOffset = 0; }
      } else {
        const discovered = discoverPinnedCodexRollout(fs, codexHomes, { preSpawnSnapshot, expectedCwd, turnStartedMs, explicitSessionId: null, excludedSessionId });
        if (discovered) { sessionState.sessionId = discovered.sessionId; sessionState.rolloutPath = discovered.rolloutPath; rolloutOffset = 0; }
      }
    }
    if (sessionState.rolloutPath && !quotaExhausted) {
      const checked = inspectRolloutQuotaError(fs, sessionState.rolloutPath, rolloutOffset, turnStartedMs);
      rolloutOffset = checked.nextOffset;
      if (checked.quotaError) triggerStructuredQuotaAbort(checked.quotaError.message);
    }
  };

  let rolloutInterval = null, cloudInterval = null, cloudCheckInFlight = false;
  const startStructuredMonitors = () => {
    if (rolloutPollMs > 0) { rolloutInterval = setInterval(pollRolloutOnce, rolloutPollMs); rolloutInterval.unref?.(); }
    if (cloudPollMs > 0 && activeEntry?.account_id) {
      cloudInterval = setInterval(() => {
        if (quotaExhausted || cloudCheckInFlight) return;
        cloudCheckInFlight = true;
        checkCloudAccountQuotaExhausted(activeEntry.account_id, { cwd, env }, ports)
          .then(acc => { if (acc) triggerStructuredQuotaAbort('usage_limit_reached', acc); })
          .finally(() => { cloudCheckInFlight = false; });
      }, cloudPollMs);
      cloudInterval.unref?.();
    }
  };
  const stopStructuredMonitors = () => {
    if (rolloutInterval) { clearInterval(rolloutInterval); rolloutInterval = null; }
    if (cloudInterval) { clearInterval(cloudInterval); cloudInterval = null; }
  };

  if (typeof ports.spawnCodexPty === 'function') {
    startStructuredMonitors();
    let res;
    try {
      res = await ports.spawnCodexPty({
        command: 'codex', args, cwd, env, turn, signal: abortController.signal,
        onOutput(chunk) { try { stdout?.write?.(chunk); } catch {} inspectChunk(chunk); },
      });
    } finally { stopStructuredMonitors(); }
    if (res?.stdout) inspectChunk(res.stdout);
    if (res?.stderr) inspectChunk(res.stderr);
    if (typeof res?.sessionId === 'string' && UUID_TOKEN_RE.test(res.sessionId)) capturedSessionId = res.sessionId;
    pollRolloutOnce();
    if (!sessionState.sessionId && capturedSessionId && (!excludedSessionId || capturedSessionId.toLowerCase() !== excludedSessionId.toLowerCase())) sessionState.sessionId = capturedSessionId;
    return { code: res?.code ?? 0, signal: res?.signal ?? null, quotaExhausted, quotaReasonText, exhaustedAccountSnapshot, abortedByParentSignal, rollingPlain, capturedSessionId };
  }

  const spawnImpl = ports.spawnInteractive ?? spawn;
  const usePythonPty = ports.usePythonPty !== false && Boolean(stdin?.isTTY && stdout?.isTTY);
  const runWithChild = tryPython => new Promise((resolveTurn, rejectTurn) => {
    let settled = false, ttyRestored = false, settleTimer = null, killTimer = null, wasRaw = false, rawEnabled = false;
    let onStdinData = null, onStdinEnd = null, onResize = null;
    const childEnv = tryPython ? { ...env, PDD_PTY_ROWS: String(stdout?.rows || 24), PDD_PTY_COLS: String(stdout?.columns || 80) } : env;
    let child;
    try {
      child = tryPython
        ? spawnImpl('python3', ['-u', '-c', PYTHON_PTY_SUPERVISOR_SCRIPT, 'codex', ...args], { cwd, env: childEnv, stdio: ['pipe', 'pipe', 'pipe', 'pipe'], shell: false })
        : spawnImpl('codex', args, { cwd, env: childEnv, stdio: [stdin === process.stdin || !stdin ? 'inherit' : 'pipe', 'pipe', 'pipe'], shell: false });
    } catch (err) { rejectTurn(err); return; }
    const resizePipe = tryPython ? (child.stdio?.[3] ?? null) : null;
    resizePipe?.on?.('error', () => {});
    const removeListener = (s, ev, h) => { if (!s || !h) return; try { (s.off ?? s.removeListener)?.call(s, ev, h); } catch {} };
    const restoreTty = () => {
      if (ttyRestored) return;
      ttyRestored = true;
      removeListener(stdin, 'data', onStdinData); removeListener(stdin, 'end', onStdinEnd); removeListener(stdin, 'close', onStdinEnd); removeListener(stdout, 'resize', onResize);
      if (rawEnabled && typeof stdin?.setRawMode === 'function') { try { stdin.setRawMode(wasRaw); } catch {} }
      if (rawEnabled && typeof stdin?.pause === 'function') { try { stdin.pause(); } catch {} }
    };
    const terminateChild = () => {
      try { resizePipe?.end?.(); } catch {}
      try { child.stdin?.end?.(); } catch {}
      try { child.kill('SIGTERM'); } catch {}
      if (!killTimer) { killTimer = setTimeout(() => { try { child.kill('SIGKILL'); } catch {} }, 600); killTimer.unref?.(); }
    };
    const onProcessExit = () => { restoreTty(); try { resizePipe?.destroy?.(); } catch {} try { child.kill('SIGTERM'); } catch {} };
    const onSigterm = () => { abortedByParentSignal = 'SIGTERM'; restoreTty(); terminateChild(); };
    const onSighup = () => { abortedByParentSignal = 'SIGHUP'; restoreTty(); terminateChild(); };
    const onSigint = () => { if (tryPython) { try { child.kill('SIGINT'); } catch {} } };
    process.on('exit', onProcessExit); process.on('SIGTERM', onSigterm); process.on('SIGHUP', onSighup); process.on('SIGINT', onSigint);
    const onAbort = () => { if (settleMs <= 0) terminateChild(); else { settleTimer = setTimeout(terminateChild, settleMs); settleTimer.unref?.(); } };
    abortController.signal.addEventListener('abort', onAbort, { once: true });
    startStructuredMonitors();

    const finish = (err, code, signal) => {
      if (settled) return;
      settled = true; stopStructuredMonitors();
      if (settleTimer) clearTimeout(settleTimer); if (killTimer) clearTimeout(killTimer);
      abortController.signal.removeEventListener('abort', onAbort);
      process.off('exit', onProcessExit); process.off('SIGTERM', onSigterm); process.off('SIGHUP', onSighup); process.off('SIGINT', onSigint);
      try { resizePipe?.end?.(); } catch {}
      restoreTty();
      if (err) { rejectTurn(err); return; }
      pollRolloutOnce();
      if (!sessionState.sessionId && capturedSessionId && (!excludedSessionId || capturedSessionId.toLowerCase() !== excludedSessionId.toLowerCase())) sessionState.sessionId = capturedSessionId;
      const effectiveSignal = abortedByParentSignal ?? signal ?? null;
      const effectiveCode = effectiveSignal === 'SIGINT' ? 130 : (abortedByParentSignal === 'SIGTERM' ? 143 : (abortedByParentSignal === 'SIGHUP' ? 129 : (code ?? 0)));
      resolveTurn({ code: effectiveCode, signal: effectiveSignal, quotaExhausted, quotaReasonText, exhaustedAccountSnapshot, abortedByParentSignal, rollingPlain, capturedSessionId });
    };
    if (tryPython && resizePipe && typeof stdout?.on === 'function') {
      onResize = () => { const r = Number(stdout?.rows) || 24, c = Number(stdout?.columns) || 80; if (r > 0 && c > 0) { try { resizePipe.write(`${r} ${c}\n`); } catch {} } };
      stdout.on('resize', onResize);
    }
    if (tryPython && stdin && child.stdin) {
      if (stdin.isTTY && typeof stdin.setRawMode === 'function') { wasRaw = Boolean(stdin.isRaw); try { stdin.setRawMode(true); rawEnabled = true; } catch {} }
      onStdinData = chunk => { try { child.stdin.write(chunk); } catch {} };
      onStdinEnd = () => { try { child.stdin.end(); } catch {} try { resizePipe?.end?.(); } catch {} };
      stdin.on?.('data', onStdinData); stdin.once?.('end', onStdinEnd); stdin.once?.('close', onStdinEnd); stdin.resume?.(); child.stdin.on('error', () => {});
    } else if (!tryPython && stdin && stdin !== process.stdin && typeof stdin.pipe === 'function' && child.stdin) {
      stdin.pipe(child.stdin); child.stdin.on('error', () => {});
    }
    child.stdout?.on('data', chunk => { try { stdout?.write?.(chunk); } catch {} inspectChunk(chunk); });
    child.stderr?.on('data', chunk => { try { stderr?.write?.(chunk); } catch {} inspectChunk(chunk); });
    child.on('error', err => finish(err));
    child.on('close', (code, signal) => finish(null, code, signal));
  });

  if (usePythonPty) {
    try { return await runWithChild(true); }
    catch (err) { if (err?.code !== 'ENOENT') throw err; }
  }
  return runWithChild(false);
}
