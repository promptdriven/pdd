import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, writeFileSync, realpathSync } from 'node:fs';
import { join } from 'node:path';
import { startRun } from '../../src/workflow-runner.mjs';
import { writeRun } from '../../src/workflow-runs.mjs';
import { fixture as runFixture, packageRoot } from './workflow-runner-fixture.mjs';
const origin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };
export async function environmentRun(t) {
  const f = await runFixture(t, { name: 'small-change', agent: 'codex' });
  f.ports.env = { HOME: f.ports.env.HOME };
  assert.equal((await startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  const run = f.record();
  // Seed the build area of a synthetic already-approved run. No approval command is called.
  run.area = 1; run.state = 'running'; run.gate = null; run.done = { scope: { at: f.clock, area: 'plan', summary: 'fixture' } };
  run.chats.at(-1).area = 'build';
  run.automaticOrigin = structuredClone(origin); writeRun(run);
  const root = realpathSync(f.source), stateRoot = join(f.state, 'autopilot'); mkdirSync(stateRoot, { recursive: true });
  writeFileSync(join(stateRoot, `${createHash('sha256').update(root).digest('hex').slice(0, 20)}.json`), JSON.stringify({ repo: run.repo, cwd: root, coordinatorId: origin.coordinatorId }));
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const fixturePath = join(f.base, 'reader.json'), logPath = join(f.base, 'gh.log');
  writeFileSync(fixturePath, JSON.stringify({ labels: ['pdd:working'], events: [{ id: 12, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' } }], comments: [{ id: 11, user: { login: 'example' }, body: JSON.stringify({ repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, labelEventId: '12' }) }] }));
  const { execFile: callback } = await import('node:child_process'); const { promisify } = await import('node:util'); const exec = promisify(callback);
  const original = f.ports.execFile;
  const execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === '--include' ? exec(process.execPath, [join(packageRoot, 'test/helpers/continuation-fake-gh.mjs'), ...args], { ...opts, env: { ...process.env, READER_FIXTURE_FILE: fixturePath, READER_GH_LOG: logPath } }) : original(file, args, opts);
  const ports = extra => ({ ...f.agentPorts(), execFile, autopilotStateRoot: stateRoot, ...extra });
  return { f, ports, root: f.record().root };
}
