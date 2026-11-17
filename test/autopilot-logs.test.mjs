import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { createHash } from 'node:crypto';
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, statSync, utimesSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { formatWorkerLogLine, inspectAutopilotWorkers, parseIssueSelector, runAutopilotLogs } from '../src/autopilot-logs.mjs';
import { runAutopilotSubcommand } from '../src/autopilot.mjs';
import { renderCompletion } from '../src/completion.mjs';
import { renderHelp, runPdd } from '../src/pdd-cli.mjs';

const sink = () => ({ text: '', write(chunk) { this.text += chunk; return true; } });

function makeSandbox(t, { mode = 'observe', repo = 'acme/widgets' } = {}) {
  const base = mkdtempSync(join(tmpdir(), 'pdd-ap-logs-'));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const gitRoot = join(base, 'repo');
  const stateRoot = join(base, 'state', 'pdd', 'autopilot');
  const stateId = createHash('sha256').update(gitRoot).digest('hex').slice(0, 20);
  const coreRoot = join(stateRoot, `${stateId}-core`);
  mkdirSync(gitRoot, { recursive: true });
  mkdirSync(join(coreRoot, 'jobs'), { recursive: true });
  mkdirSync(join(coreRoot, 'intake', 'jobs'), { recursive: true });
  mkdirSync(join(coreRoot, 'logs'), { recursive: true });

  writeFileSync(join(gitRoot, 'pdd.json'), JSON.stringify({ autopilot: { mode, trust: ['alice'] } }, null, 2) + '\n');
  writeFileSync(join(stateRoot, `${stateId}.json`), JSON.stringify({
    repo,
    root: gitRoot,
    enabled: true,
    mode,
  }, null, 2) + '\n');
  writeFileSync(join(coreRoot, 'core.json'), JSON.stringify({ streak: 0 }, null, 2) + '\n');

  const git = async args => {
    if (args[0] === 'rev-parse' && args[1] === '--show-toplevel') return { code: 0, stdout: `${gitRoot}\n`, stderr: '' };
    return { code: 1, stdout: '', stderr: 'unexpected git call' };
  };

  return { base, gitRoot, stateRoot, stateId, coreRoot, git };
}

function snapshotTree(dir) {
  const entries = [];
  const walk = current => {
    for (const name of readdirSync(current).sort()) {
      const full = join(current, name);
      const st = statSync(full);
      if (st.isDirectory()) {
        entries.push({ path: full, kind: 'dir' });
        walk(full);
      } else {
        entries.push({ path: full, kind: 'file', size: st.size, sha: createHash('sha256').update(readFileSync(full)).digest('hex') });
      }
    }
  };
  walk(dir);
  return entries;
}

test('3475: pdd autopilot logs is discoverable in help and shell completion and validates selectors', async () => {
  assert.match(renderHelp(['autopilot']), /pdd autopilot logs \[ISSUE\] \[--follow\|-f\] \[--lines N\] \[--json\]/);
  assert.match(renderCompletion('bash'), /\blogs\b/);
  assert.match(renderCompletion('zsh'), /\blogs\b/);

  assert.deepEqual(parseIssueSelector('42'), { ok: true, issue: 42, repo: null });
  assert.deepEqual(parseIssueSelector('#42'), { ok: true, issue: 42, repo: null });
  assert.deepEqual(parseIssueSelector('acme/widgets#42'), { ok: true, issue: 42, repo: 'acme/widgets' });
  assert.deepEqual(parseIssueSelector('https://github.com/acme/widgets/issues/42'), { ok: true, issue: 42, repo: 'acme/widgets' });
  assert.equal(parseIssueSelector('0').ok, false);
  assert.equal(parseIssueSelector('not-an-issue').ok, false);

  // Invalid CLI combinations fail fast with exit 2 and no side effects
  for (const argv of [
    ['autopilot', 'logs', '--follow'],
    ['autopilot', 'logs', '-f'],
    ['autopilot', 'logs', '12', '--follow', '--json'],
    ['autopilot', 'logs', '12', '--issue', '13'],
    ['autopilot', 'logs', 'acme/widgets#12', '--issue', 'other/repo#12'],
    ['autopilot', 'logs', 'not-an-issue'],
    ['autopilot', 'logs', '--issue', 'not-an-issue'],
    ['autopilot', 'logs', '--lines', '0'],
  ]) {
    const stdout = sink(), stderr = sink();
    const code = await runPdd(argv, { stdout, stderr, cwd: '/tmp' });
    assert.equal(code, 2, argv.join(' '));
    assert.equal(stdout.text, '');
    assert.ok(stderr.text.trim().length > 0);
  }

  // CLI passes { issue } contract and accepts "#42", "owner/repo#42", and matching positional + --issue
  const capturedInputs = [];
  for (const argv of [
    ['autopilot', 'logs', '#42'],
    ['autopilot', 'logs', 'acme/widgets#42'],
    ['autopilot', 'logs', '#42', '--issue', '42'],
  ]) {
    const stdout = sink(), stderr = sink();
    const code = await runPdd(argv, {
      stdout,
      stderr,
      cwd: '/tmp/repo',
      autopilotLogs: {
        runAutopilotLogs: async input => {
          capturedInputs.push(input);
          return { exitCode: 0, message: `ok ${input.issue}` };
        },
      },
    });
    assert.equal(code, 0, `${argv.join(' ')}: ${stderr.text}`);
  }
  assert.equal(capturedInputs[0].issue, '#42');
  assert.equal(capturedInputs[1].issue, 'acme/widgets#42');
  assert.equal(capturedInputs[2].issue, '42');
  assert.equal('positionalIssue' in capturedInputs[0], false);

  const unknownSub = await runAutopilotSubcommand('unknown', {});
  assert.equal(unknownSub.exitCode, 2);
});

test('3475: outside a Git repository pdd autopilot logs exits 1 with exact docs/cli.md guidance', async () => {
  const stdout = sink(), stderr = sink();
  const code = await runPdd(['autopilot', 'logs'], {
    stdout,
    stderr,
    cwd: '/tmp/not-a-repo',
    autopilotLogsPorts: {
      git: async () => ({ code: 128, stdout: '', stderr: 'fatal: not a git repository (or any of the parent directories): .git\n' }),
    },
  });
  assert.equal(code, 1);
  assert.equal(stdout.text, '');
  assert.equal(
    stderr.text.trim(),
    'This folder is not a Git repository. cd into the repo you want Autopilot to work on, then run the command again.',
  );
});

test('3475: formatWorkerLogLine renders Codex, Claude, Gemini/agy JSONL and redacts secrets & ANSI codes', () => {
  // Codex events
  assert.equal(
    formatWorkerLogLine(JSON.stringify({ type: 'thread.started', model: 'gpt-5-codex' })),
    '[session] started (gpt-5-codex)',
  );
  assert.equal(
    formatWorkerLogLine(JSON.stringify({
      type: 'item.started',
      item: { type: 'command_execution', command: '/bin/zsh -lc "node --test test/foo.test.mjs"' },
    })),
    '[run] $ /bin/zsh -lc "node --test test/foo.test.mjs"',
  );
  const completedCmd = formatWorkerLogLine(JSON.stringify({
    type: 'item.completed',
    item: {
      type: 'command_execution',
      command: 'bash -lc "gh auth token"',
      exit_code: 0,
      aggregated_output: '\x1b[32mToken: ghp_ABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890\x1b[0m\nDone\n',
    },
  }));
  assert.match(completedCmd, /\[cmd exit=0\] \$ bash -lc "gh auth token"/);
  assert.doesNotMatch(completedCmd, /ghp_ABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890/);
  assert.doesNotMatch(completedCmd, /\x1b\[/);

  assert.equal(
    formatWorkerLogLine(JSON.stringify({
      type: 'item.completed',
      item: { type: 'file_change', changes: [{ kind: 'update', path: 'src/foo.mjs' }] },
    })),
    '[edit] src/foo.mjs',
  );
  assert.equal(
    formatWorkerLogLine(JSON.stringify({
      type: 'item.completed',
      item: { type: 'agent_message', text: 'Updated prompt and verified tests.' },
    })),
    '[agent] Updated prompt and verified tests.',
  );
  // Noisy token heartbeat events return empty string
  assert.equal(formatWorkerLogLine(JSON.stringify({ type: 'turn.started' })), '');
  assert.equal(formatWorkerLogLine(JSON.stringify({ type: 'token_count', total: 100 })), '');

  // Claude stream-json events
  const claudeLine = formatWorkerLogLine(JSON.stringify({
    type: 'assistant',
    message: {
      content: [
        { type: 'text', text: 'Checking worker logs.' },
        { type: 'tool_use', name: 'Bash', input: { command: 'git status' } },
      ],
    },
  }));
  assert.match(claudeLine, /\[agent\] Checking worker logs\./);
  assert.match(claudeLine, /\[tool\] Bash: git status/);

  // Gemini / agy stream-json events
  assert.equal(
    formatWorkerLogLine(JSON.stringify({ type: 'tool_use', tool_name: 'read_file', parameters: { path: 'docs/cli.md' } })),
    '[tool] read_file: docs/cli.md',
  );
});

test('3475: distinguishes queued suite, live running suite, repair worker, and stale suite receipt / dead process', async t => {
  const sb = makeSandbox(t, { mode: 'observe' });
  const nowMs = Date.parse('2026-11-17T20:30:00Z');

  // Worker #101: PR check queued in shared test-suite queue (position 2)
  const log101 = join(sb.coreRoot, 'logs', '101-suite-1.log');
  writeFileSync(log101, 'Waiting in shared suite queue...\n');
  utimesSync(log101, (nowMs - 15_000) / 1000, (nowMs - 15_000) / 1000);
  writeFileSync(join(sb.coreRoot, 'jobs', '101.json'), JSON.stringify({
    issue: 101,
    title: 'Add queue status header',
    phase: 'pr',
    pr: 210,
    head: 'aaaa1111bbbb2222',
    root: join(sb.base, 'wt-101'),
    suite: {
      cwd: join(sb.base, 'wt-101'),
      head: 'aaaa1111bbbb2222',
      agent: { pid: 4101, token: 'tok-101', log: log101, startedAt: nowMs - 60_000 },
    },
  }));

  // Worker #102: PR check with LIVE running full test suite + validation log + saved evidence
  const suiteLiveLog = join(sb.base, 'validation-102.log');
  writeFileSync(suiteLiveLog, 'ok 1 - first suite case\nok 2 - second suite case\n');
  utimesSync(suiteLiveLog, (nowMs - 5_000) / 1000, (nowMs - 5_000) / 1000);
  const ev102 = join(sb.coreRoot, 'logs', '102-evidence-cccc3333.json');
  writeFileSync(ev102, '{"ok":true}\n');
  writeFileSync(join(sb.coreRoot, 'jobs', '102.json'), JSON.stringify({
    issue: 102,
    title: 'Stream validation progress',
    phase: 'pr',
    pr: 211,
    head: 'cccc3333dddd4444',
    root: join(sb.base, 'wt-102'),
    suite: {
      cwd: join(sb.base, 'wt-102'),
      head: 'cccc3333dddd4444',
      agent: { pid: 4102, token: 'tok-102', log: join(sb.coreRoot, 'logs', '102-suite-1.log'), startedAt: nowMs - 90_000 },
    },
  }));

  // Worker #103: Active repair #2 on PR #212
  const log103 = join(sb.coreRoot, 'logs', '103-repair-2.log');
  writeFileSync(log103, JSON.stringify({
    type: 'item.completed',
    item: { type: 'agent_message', text: 'Fixing failing edge case in parser.' },
  }) + '\n');
  utimesSync(log103, (nowMs - 3_000) / 1000, (nowMs - 3_000) / 1000);
  writeFileSync(join(sb.coreRoot, 'jobs', '103.json'), JSON.stringify({
    issue: 103,
    title: 'Handle empty input',
    role: 'repair',
    repairs: 2,
    pr: 212,
    head: 'eeee5555ffff6666',
    lastError: 'Review requested null guard',
    agent: { pid: 4103, token: 'tok-103', log: log103, startedAt: nowMs - 45_000 },
  }));

  // Worker #104: Stale suite receipt (runner crashed before reporting)
  const log104 = join(sb.coreRoot, 'logs', '104-suite-1.log');
  writeFileSync(log104, 'Started suite wrapper\n');
  writeFileSync(join(sb.coreRoot, 'jobs', '104.json'), JSON.stringify({
    issue: 104,
    title: 'Detect stale suite receipt',
    phase: 'pr',
    pr: 213,
    head: '99990000aaaa1111',
    root: join(sb.base, 'wt-104'),
    suite: {
      cwd: join(sb.base, 'wt-104'),
      head: '99990000aaaa1111',
      agent: { pid: 4104, token: 'tok-104', log: log104, startedAt: nowMs - 300_000 },
    },
  }));

  // Historical finished worker #99 in history.jsonl
  const log99 = join(sb.coreRoot, 'logs', '99-build-1.log');
  writeFileSync(log99, JSON.stringify({
    type: 'item.completed',
    item: { type: 'agent_message', text: 'Opened PR #199 cleanly.' },
  }) + '\n');
  writeFileSync(join(sb.coreRoot, 'history.jsonl'), JSON.stringify({
    issue: 99,
    outcome: 'ready-observe',
    pr: 199,
    at: nowMs - 600_000,
    text: 'checks passed in observe mode',
  }) + '\n');

  const alivePids = new Set([4101, 4102, 4103]); // 4104 is dead with no .exit.json!
  const ports = {
    git: sb.git,
    stateRoot: sb.stateRoot,
    now: () => nowMs,
    isProcessAlive: pid => alivePids.has(pid),
    readSuite: ({ cwd }) => {
      if (cwd.endsWith('wt-101')) return { ok: true, state: 'waiting', position: 2, commit: 'aaaa1111bbbb2222' };
      if (cwd.endsWith('wt-102')) {
        return {
          ok: true,
          state: 'running',
          childPid: 5202,
          commit: 'cccc3333dddd4444',
          counts: { pass: 2, fail: 0 },
          logPath: suiteLiveLog,
        };
      }
      if (cwd.endsWith('wt-104')) {
        return {
          ok: false,
          reason: 'recorder_not_running',
          outcome: 'The suite runner ended before reporting.',
          commit: '99990000aaaa1111',
        };
      }
      return { ok: false, reason: 'none' };
    },
  };

  const beforeSnapshot = snapshotTree(sb.base);

  // 1. List view (`pdd autopilot logs`)
  const listOut = sink(), listErr = sink();
  const listCode = await runPdd(['autopilot', 'logs'], {
    stdout: listOut,
    stderr: listErr,
    cwd: sb.gitRoot,
    autopilotLogsPorts: ports,
  });
  assert.equal(listCode, 0, listErr.text);
  assert.equal(listErr.text, '');
  assert.match(listOut.text, /mode observe \(read-only viewer; observe mode never approves or merges\)/);
  assert.match(listOut.text, /#101 "Add queue status header"[\s\S]*?queued in shared test-suite queue \(position 2\)/);
  assert.match(listOut.text, /#102 "Stream validation progress"[\s\S]*?running full test suite \(pid 5202\) \[pass 2, fail 0\]/);
  assert.match(listOut.text, /#103 "Handle empty input"[\s\S]*?Stage: repair #2 on PR #212/);
  assert.match(listOut.text, /#104 "Detect stale suite receipt"[\s\S]*?stale suite receipt/);
  assert.match(listOut.text, /Recent finished workers[\s\S]*?#99 \(PR #199\): ready-observe/);
  assert.match(listOut.text, /Follow a worker live: pdd autopilot logs 101 --follow/);

  // 2. Selected worker view via "#102" (`pdd autopilot logs "#102" --lines 5`) and --issue 102
  for (const argv of [
    ['autopilot', 'logs', '#102', '--lines', '5'],
    ['autopilot', 'logs', '--issue', '102', '--lines', '5'],
  ]) {
    const issueOut = sink(), issueErr = sink();
    const issueCode = await runPdd(argv, {
      stdout: issueOut,
      stderr: issueErr,
      cwd: sb.gitRoot,
      autopilotLogsPorts: ports,
    });
    assert.equal(issueCode, 0, issueErr.text);
    assert.match(issueOut.text, /Stage: PR #211 \(cccc3333\): running full test suite \(pid 5202\) \[pass 2, fail 0\]/);
    assert.match(issueOut.text, new RegExp(ev102.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')));
    assert.match(issueOut.text, /ok 1 - first suite case/);
    assert.match(issueOut.text, /ok 2 - second suite case/);
  }

  // 3. JSON snapshot (`pdd autopilot logs 101 --json`)
  const jsonOut = sink(), jsonErr = sink();
  const jsonCode = await runPdd(['autopilot', 'logs', '101', '--json'], {
    stdout: jsonOut,
    stderr: jsonErr,
    cwd: sb.gitRoot,
    autopilotLogsPorts: ports,
  });
  assert.equal(jsonCode, 0, jsonErr.text);
  const parsed = JSON.parse(jsonOut.text);
  assert.equal(parsed.schema, 'pdd.autopilot-logs.v1');
  assert.equal(parsed.mode, 'observe');
  assert.equal(parsed.worker.stage, 'suite-queued');
  assert.equal(parsed.worker.suite.position, 2);

  // 4. Historical worker inspection (`pdd autopilot logs 99`)
  const histRes = await runAutopilotLogs({ cwd: sb.gitRoot, issue: '99' }, ports);
  assert.equal(histRes.exitCode, 0);
  assert.match(histRes.message, /Stage: finished \(ready-observe/);
  assert.match(histRes.message, /\[agent\] Opened PR #199 cleanly\./);

  // Strict read-only invariant: zero files created, modified or deleted anywhere in repo or state folder!
  assert.deepEqual(snapshotTree(sb.base), beforeSnapshot, 'viewer must be 100% read-only and preserve observe mode');
});

test('3475: --follow streams live updates across stage transitions and detaches cleanly without stopping the worker', async t => {
  const sb = makeSandbox(t, { mode: 'observe' });
  let nowMs = Date.parse('2026-11-17T20:40:00Z');
  const buildLog = join(sb.coreRoot, 'logs', '77-build-1.log');
  const suiteLog = join(sb.base, 'suite-77.log');
  const jobFile = join(sb.coreRoot, 'jobs', '77.json');

  writeFileSync(buildLog, JSON.stringify({
    type: 'item.completed',
    item: { type: 'agent_message', text: 'Initial build step started.' },
  }) + '\n');
  writeFileSync(jobFile, JSON.stringify({
    issue: 77,
    title: 'Follow live worker safely',
    role: 'build',
    agent: { pid: 7701, token: 'tok-77', log: buildLog, startedAt: nowMs - 10_000 },
  }));

  const abortController = new AbortController();
  let suiteState = { ok: false, reason: 'none' };
  let tick = 0;
  const stdout = sink(), stderr = sink();

  const exitCode = await runPdd(['autopilot', 'logs', '77', '-f'], {
    stdout,
    stderr,
    cwd: sb.gitRoot,
    autopilotLogsPorts: {
      git: sb.git,
      stateRoot: sb.stateRoot,
      now: () => nowMs,
      isProcessAlive: pid => pid === 7701 || pid === 7702,
      readSuite: () => suiteState,
      signal: abortController.signal,
      pollMs: 10,
      sleep: async () => {
        tick++;
        nowMs += 1000;
        if (tick === 1) {
          // Worker appends another JSONL progress line while building
          writeFileSync(buildLog, readFileSync(buildLog, 'utf8') + JSON.stringify({
            type: 'item.completed',
            item: { type: 'command_execution', command: 'npm run check', exit_code: 0, aggregated_output: '' },
          }) + '\n');
        } else if (tick === 2) {
          // Worker transitions to PR suite-running and opens live suite validation log
          writeFileSync(suiteLog, 'TAP version 13\nok 1 - live streamed test\n');
          suiteState = {
            ok: true,
            state: 'running',
            childPid: 7702,
            commit: '1234abcd',
            counts: { pass: 1, fail: 0 },
            logPath: suiteLog,
          };
          writeFileSync(jobFile, JSON.stringify({
            issue: 77,
            title: 'Follow live worker safely',
            phase: 'pr',
            pr: 301,
            head: '1234abcd',
            root: sb.gitRoot,
            suite: {
              cwd: sb.gitRoot,
              head: '1234abcd',
              agent: { pid: 7701, token: 'tok-77', log: buildLog, startedAt: nowMs - 10_000 },
            },
          }));
        } else if (tick === 3) {
          // Operator presses Ctrl-C (aborts viewer) while worker is still running
          abortController.abort();
        }
      },
    },
  });

  assert.equal(exitCode, 0, stderr.text);
  assert.equal(stderr.text, '');
  assert.match(stdout.text, /Following live output \(press Ctrl-C to detach without stopping the worker\)/);
  assert.match(stdout.text, /\[agent\] Initial build step started\./);
  assert.match(stdout.text, /\[cmd exit=0\] \$ npm run check/);
  assert.match(stdout.text, /\[stage\] PR #301 \(1234abcd\): running full test suite \(pid 7702\) \[pass 1, fail 0\]/);
  assert.match(stdout.text, /\[stage\] Streaming suite log:/);
  assert.match(stdout.text, /ok 1 - live streamed test/);
  assert.match(stdout.text, /Detached from issue #77 \(background worker continues untouched\)\./);

  // Confirm observe mode in pdd.json and active job file remain untouched after detach
  assert.equal(JSON.parse(readFileSync(join(sb.gitRoot, 'pdd.json'), 'utf8')).autopilot.mode, 'observe');
  const postSnap = await inspectAutopilotWorkers({ cwd: sb.gitRoot }, {
    git: sb.git,
    stateRoot: sb.stateRoot,
    now: () => nowMs,
    isProcessAlive: () => true,
    readSuite: () => suiteState,
  });
  assert.equal(postSnap.workers.length, 1);
  assert.equal(postSnap.workers[0].issue, 77);
  assert.equal(postSnap.workers[0].liveProcess, true);
});

test('3475: enforces pid > 1 and treats EPERM / non-owned PIDs as not running in default liveness check', async t => {
  const sb = makeSandbox(t, { mode: 'observe' });
  const nowMs = Date.parse('2026-11-17T21:00:00Z');
  const logFile = join(sb.coreRoot, 'logs', '51-build-1.log');
  writeFileSync(logFile, 'Starting step\n');

  // Job #51 has pid: 1 (system init/launchd — EPERM if probed) and suite childPid: 1
  writeFileSync(join(sb.coreRoot, 'jobs', '51.json'), JSON.stringify({
    issue: 51,
    title: 'Reject pid 1 and invalid pids',
    phase: 'pr',
    pr: 88,
    head: 'abcd1234',
    agent: { pid: 1, log: logFile, started: nowMs - 5000 },
    review: { agent: { pid: 0, log: logFile, started: nowMs - 5000 } },
    vectors: { agent: { pid: -9, log: logFile, started: nowMs - 5000 } },
    suite: { cwd: sb.gitRoot, head: 'abcd1234', agent: { pid: 1, log: logFile } },
  }));

  // Omit isProcessAlive so real defaultIsProcessAlive runs!
  const snap = await inspectAutopilotWorkers({ cwd: sb.gitRoot }, {
    git: sb.git,
    stateRoot: sb.stateRoot,
    now: () => nowMs,
    readSuite: () => ({
      ok: true,
      state: 'running',
      childPid: 1,
      counts: { pass: 1, fail: 0 },
      logPath: logFile,
    }),
  });

  assert.equal(snap.ok, true);
  const worker = snap.workers.find(w => w.issue === 51);
  assert.ok(worker);
  assert.equal(worker.suite.childPid, null, 'childPid 1 must be rejected');
  assert.doesNotMatch(worker.suite.detail, /pid 1\b/);
  assert.equal(worker.liveProcess, false, 'pid 1 must never be treated as a live worker');
  assert.equal(worker.processState, 'idle');
});

test('3475: redacts input.env secrets and strips ANSI across --json, state/path fields, and long tail/follow lines without mid-line slicing', async t => {
  const sb = makeSandbox(t, { mode: 'observe' });
  const nowMs = Date.parse('2026-11-17T21:10:00Z');
  const envSecret = 'custom-env-secret-value-998877';
  const inputEnv = { ...process.env, MY_WORKER_SECRET_TOKEN: envSecret };

  // Put secret and ANSI codes in launcherState, machineState, worker metadata, and file path!
  writeFileSync(join(sb.stateRoot, `${sb.stateId}.json`), JSON.stringify({
    repo: `acme/\x1b[31mwidgets-${envSecret}\x1b[0m`,
    root: sb.gitRoot,
    enabled: true,
    mode: 'observe',
  }));
  writeFileSync(join(sb.coreRoot, 'core.json'), JSON.stringify({
    poolOut: { wakeAt: `2026-11-17T22:00:00Z-${envSecret}\x1b[33m` },
  }));

  const secretDir = join(sb.base, `dir-${envSecret}`);
  mkdirSync(secretDir, { recursive: true });
  const longLogPath = join(secretDir, '60-build.log');
  const receiptPath = join(secretDir, '60-receipt.json');
  writeFileSync(receiptPath, '{"ok":true}\n');

  // Create a 110 KiB single-line log ending in '\n' (exceeds initial 64 KiB readSize)
  // with secret near the front and multi-byte UTF-8 characters throughout, to prove
  // formatLogTail expands its window rather than dropping trailing-'\n' tails or slicing mid-line!
  const utf8Pad = '🚀日本語テスト'.repeat(6500); // ~117 KiB of multi-byte UTF-8
  const singleLongLine = `${envSecret} start-marker ${utf8Pad} end-marker\n`;
  writeFileSync(longLogPath, singleLongLine);

  const exitPath = join(sb.coreRoot, 'logs', '60.exit.json');
  writeFileSync(exitPath, JSON.stringify({
    code: null,
    signal: `SIGTERM-${envSecret}\x1b[0m`,
    at: nowMs - 1000,
  }));

  writeFileSync(join(sb.coreRoot, 'jobs', '60.json'), JSON.stringify({
    issue: 60,
    title: `Fix auth ${envSecret}`,
    phase: 'pr',
    pr: 310,
    head: `${envSecret}abcdef`,
    lane: { state: 'waiting', holder: `99-${envSecret}` },
    review: { verdict: `FAIL-${envSecret}`, agent: { pid: 6002, exit: exitPath, agentKind: `codex-${envSecret}` } },
    stepStop: { poolExhausted: true, wakeAt: `soon-${envSecret}` },
    lastError: `Auth failed with ${envSecret}`,
    agent: { pid: 6001, agentKind: `codex-${envSecret}\x1b[35m`, log: longLogPath, started: nowMs - 5000 },
    suite: { cwd: sb.gitRoot, head: 'abcdef12' },
  }));

  const ports = {
    git: sb.git,
    stateRoot: sb.stateRoot,
    now: () => nowMs,
    isProcessAlive: pid => pid === 6001,
    readSuite: () => ({
      ok: true,
      state: 'waiting',
      position: 1,
      logPath: longLogPath,
      receiptPath,
    }),
  };

  // Check list --json, issue --json, and human snapshot: zero leaks of envSecret or ANSI!
  for (const argv of [
    ['autopilot', 'logs', '--json'],
    ['autopilot', 'logs', '60', '--json'],
    ['autopilot', 'logs', '60', '--lines', '5'],
  ]) {
    const stdout = sink(), stderr = sink();
    const code = await runPdd(argv, {
      stdout,
      stderr,
      cwd: sb.gitRoot,
      env: inputEnv,
      autopilotLogsPorts: ports,
    });
    assert.equal(code, 0, `${argv.join(' ')}: ${stderr.text}`);
    assert.equal(stdout.text.includes(envSecret), false, `leaked env secret in ${argv.join(' ')}:\n${stdout.text}`);
    assert.doesNotMatch(stdout.text, /\x1b\[/, `leaked ANSI in ${argv.join(' ')}`);
    assert.equal(stdout.text.includes('\ufffd'), false, `corrupted UTF-8 in ${argv.join(' ')}`);
  }

  // Verify the single 117 KiB line ending in '\n' was NOT dropped by formatLogTail!
  const issueJsonOut = sink();
  await runPdd(['autopilot', 'logs', '60', '--json'], {
    stdout: issueJsonOut,
    stderr: sink(),
    cwd: sb.gitRoot,
    env: inputEnv,
    autopilotLogsPorts: ports,
  });
  const issuePayload = JSON.parse(issueJsonOut.text);
  assert.equal(issuePayload.lines.length, 1, 'single long line ending in EOF newline must not be dropped');
  assert.match(issuePayload.lines[0], /\[redacted\] start-marker 🚀日本語テスト/);

  // Also test readAppendedCompleteLines in --follow when a > 550 KiB line (> READ_CHUNK_LIMIT) is appended!
  const followLog = join(sb.coreRoot, 'logs', '61-build.log');
  writeFileSync(followLog, 'initial line\n');
  writeFileSync(join(sb.coreRoot, 'jobs', '61.json'), JSON.stringify({
    issue: 61,
    title: 'Large follow line',
    role: 'build',
    agent: { pid: 6101, log: followLog, started: nowMs - 2000 },
  }));

  const abort = new AbortController();
  let followTick = 0;
  const followOut = sink();
  // Place envSecret right across the 512 KiB byte boundary inside a ~542 KiB line!
  const prefixBytes = '🚀'.repeat(Math.floor((512 * 1024 - 12) / 4));
  const hugeAppendedLine = `big-line ${prefixBytes}${envSecret}-${'x'.repeat(30 * 1024)}-tail-ok\n`;
  assert.ok(Buffer.byteLength(hugeAppendedLine, 'utf8') > 530 * 1024);

  const followCode = await runPdd(['autopilot', 'logs', '61', '--follow'], {
    stdout: followOut,
    stderr: sink(),
    cwd: sb.gitRoot,
    env: inputEnv,
    autopilotLogsPorts: {
      git: sb.git,
      stateRoot: sb.stateRoot,
      now: () => nowMs,
      isProcessAlive: pid => pid === 6101,
      signal: abort.signal,
      pollMs: 10,
      sleep: async () => {
        followTick++;
        if (followTick === 1) {
          writeFileSync(followLog, readFileSync(followLog, 'utf8') + hugeAppendedLine);
        } else {
          abort.abort();
        }
      },
    },
  });
  assert.equal(followCode, 0);
  assert.equal(followOut.text.includes(envSecret), false, 'secret straddling 512 KiB boundary must be redacted');
  assert.equal(followOut.text.includes('\ufffd'), false, 'multi-byte UTF-8 straddling 512 KiB boundary must not corrupt');
  assert.match(followOut.text, /big-line 🚀/);
});

test('3475: --follow handles stdout EPIPE cleanly, reuses gitRoot across polls, and enforces maxDurationMs', async t => {
  const sb = makeSandbox(t, { mode: 'observe' });
  let nowMs = Date.parse('2026-11-17T21:20:00Z');
  const logFile = join(sb.coreRoot, 'logs', '88-build.log');
  writeFileSync(logFile, 'line 1\nline 2\nline 3\n');
  writeFileSync(join(sb.coreRoot, 'jobs', '88.json'), JSON.stringify({
    issue: 88,
    title: 'Pipe and maxDuration safety',
    role: 'build',
    agent: { pid: 8801, log: logFile, started: nowMs - 2000 },
  }));

  // 1. Simulate `pdd autopilot logs 88 --follow | head -n 5`: stdout emits EPIPE after 5 writes
  class BrokenPipeStdout extends EventEmitter {
    constructor(limit) {
      super();
      this.limit = limit;
      this.lines = [];
      this.destroyed = false;
      this.writableEnded = false;
    }
    write(chunk) {
      if (this.destroyed) {
        const err = new Error('write EPIPE');
        err.code = 'EPIPE';
        throw err;
      }
      this.lines.push(String(chunk));
      if (this.lines.length >= this.limit) {
        this.destroyed = true;
        const err = new Error('write EPIPE');
        err.code = 'EPIPE';
        this.emit('error', err);
        this.emit('close');
      }
      return true;
    }
  }

  const pipeStdout = new BrokenPipeStdout(5);
  let gitCalls = 0;
  let sleepCalls = 0;
  const pipeCode = await runPdd(['autopilot', 'logs', '#88', '--follow'], {
    stdout: pipeStdout,
    stderr: sink(),
    cwd: sb.gitRoot,
    autopilotLogsPorts: {
      git: async (args, opts) => {
        gitCalls++;
        return sb.git(args, opts);
      },
      stateRoot: sb.stateRoot,
      now: () => nowMs,
      isProcessAlive: () => true,
      pollMs: 10,
      sleep: async () => { sleepCalls++; },
    },
  });
  assert.equal(pipeCode, 0, 'broken pipe must exit 0 cleanly');
  assert.equal(pipeStdout.lines.length, 5, 'must stop writing immediately once pipe closes');
  assert.equal(sleepCalls, 0, 'must not enter or leak polling loop after pipe closes');
  assert.equal(pipeStdout.listenerCount('close'), 0, 'must clean up close listener');
  assert.equal(pipeStdout.listenerCount('error'), 0, 'must clean up error listener');

  // 2. Verify git rev-parse is called ONCE and reused across polls, and maxDurationMs stops follow cleanly
  gitCalls = 0;
  let pollCount = 0;
  const boundedOut = sink();
  const boundedCode = await runPdd(['autopilot', 'logs', '88', '--follow'], {
    stdout: boundedOut,
    stderr: sink(),
    cwd: sb.gitRoot,
    autopilotLogsPorts: {
      git: async (args, opts) => {
        gitCalls++;
        return sb.git(args, opts);
      },
      stateRoot: sb.stateRoot,
      now: () => nowMs,
      isProcessAlive: () => true,
      pollMs: 10,
      maxDurationMs: 2500,
      sleep: async () => {
        pollCount++;
        nowMs += 1000;
      },
    },
  });
  assert.equal(boundedCode, 0);
  assert.equal(gitCalls, 1, 'git rev-parse must run only once and reuse gitRoot on polls');
  assert.equal(pollCount, 3, 'maxDurationMs must bound unattended polling');
  assert.match(boundedOut.text, /Reached follow time limit; detached from issue #88/);
});
