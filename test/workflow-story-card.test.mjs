// #2962: normal runs show a Story card from the run's real files, open PR 1 by themselves after a verified full check
// pass, skip the try question, and keep code-or-stop at the card. Strict mode and Autopilot runs keep their gates.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { chmodSync, cpSync, mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { execFile as callbackExec } from 'node:child_process';
import { promisify } from 'node:util';
import * as runner from '../src/workflow-runner.mjs';

// A namespace import, so each test shows its own result on a pdd without the card command.
const { approveRun, runStatus, startRun, stepDone } = runner;
const showStoryCard = (...args) => { assert.equal(typeof runner.showStoryCard, 'function', 'workflow card must be available'); return runner.showStoryCard(...args); };
import { writeRun } from '../src/workflow-runs.mjs';
import { fakeRuntime, portsFor, storyTest } from './runtime-fake.mjs';
import { runCheck } from '../src/runtime-seam.mjs';
import { renderJson } from '../src/runtime/runtime-output.mjs';
import { captureSource, fillHashes } from '../src/runtime/runtime-preflight.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const harbor = join(packageRoot, 'test', 'fixtures', 'harbor');
const STORY = 'user_stories/place-order.md', TEST = 'tests/place-order.json', PROMPT = 'prompts/place_order.prompt.md';
const ASKED = 'Show my order total before I pay, so I know the price.';
const KEEP = 'The menu prices stay the same.';
const RULE = 'The total is the sum of the line totals, in whole cents; a rounded or estimated total is forbidden.';
const said = (f, words, extra = {}) => ({ ...f.agentPorts(extra), stdin: (async function* () { yield words; })() });

// A feature run whose issue text has a quoted request, with the Harbor fixture as the Story, its test and its prompt.
async function storyGate(t, { through, start = {}, existingStory = false, existingScenario = false, existingFixtures = false } = {}) {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  f.ports.env.PDD_STATE_DIR = join(f.state, 'runtime');
  const original = f.ports.execFile;
  f.ports.execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/17'
    ? { stdout: JSON.stringify({ number: 17, html_url: 'https://github.com/example/project/issues/17', title: 'Show the order total',
      body: `<!-- template -->\n## User request\n\n> ${ASKED}\n\nMore notes that are not the request.` }) }
    : original(file, args, opts);
  if (existingFixtures) {
    const nested = join(f.source, 'test', 'fixtures', 'nested-project');
    for (const dir of ['user_stories', 'tests', 'prompts']) mkdirSync(join(nested, dir), { recursive: true });
    for (const path of [STORY, TEST, PROMPT]) cpSync(join(harbor, path), join(nested, path));
    f.git(f.source, 'add', '.'); f.git(f.source, 'commit', '-qm', 'Existing fixture project');
    f.git(f.source, 'update-ref', 'refs/remotes/origin/main', f.git(f.source, 'rev-parse', 'HEAD'));
  }
  if (existingScenario) {
    for (const dir of ['user_stories', 'tests', 'prompts']) mkdirSync(join(f.source, dir), { recursive: true });
    cpSync(join(harbor, PROMPT), join(f.source, PROMPT));
    storyTest(f.source, 'existing-order');
    f.git(f.source, 'add', '.'); f.git(f.source, 'commit', '-qm', 'Existing scenario');
    f.git(f.source, 'update-ref', 'refs/remotes/origin/main', f.git(f.source, 'rev-parse', 'HEAD'));
  }
  if (existingStory) {
    mkdirSync(join(f.source, 'user_stories'), { recursive: true });
    writeFileSync(join(f.source, STORY), `${readFileSync(join(harbor, STORY), 'utf8').trimEnd()}\n\n## Rules to check\n\n${RULE}\n\n## What must not change\n\n${KEEP}\n`);
    f.git(f.source, 'add', '.'); f.git(f.source, 'commit', '-qm', 'Existing Story');
    f.git(f.source, 'update-ref', 'refs/remotes/origin/main', f.git(f.source, 'rev-parse', 'HEAD'));
  }
  const started = await startRun({ name: 'feature', issue: '17', agent: 'codex', cwd: f.source, packageRoot, ...(through ? { through } : {}), ...start }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  const run = f.record();
  f.done = async (step, summary = step, extra = {}) => { f.tick(); const out = await stepDone({ step, summary, cwd: run.root, ...extra }, f.agentPorts()); assert.equal(out.exitCode, 0, out.message); return out; };
  await f.done('understand');
  await f.done('visual', undefined, { skipped: 'no screen' });
  for (const dir of ['prompts', 'user_stories', 'tests']) mkdirSync(join(run.root, dir), { recursive: true });
  cpSync(join(harbor, PROMPT), join(run.root, PROMPT));
  if (existingScenario) writeFileSync(join(run.root, PROMPT), readFileSync(join(run.root, PROMPT), 'utf8').replace('Return the order:', 'Return the priced order:'));
  cpSync(join(harbor, TEST), join(run.root, TEST));
  writeFileSync(join(run.root, STORY), `${readFileSync(join(harbor, STORY), 'utf8').trimEnd()}\n\n## Rules to check\n\n${RULE}\n\n## What must not change\n\n${KEEP}\n`);
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'Story, test and prompt');
  f.gate = await f.done('prompt-story');
  f.run = run;
  return f;
}
// Keep synthetic Story text and its scenario criteria consistent while testing gate changes.
function reviseStory(f,before,after) {
  writeFileSync(join(f.run.root,STORY),readFileSync(join(f.run.root,STORY),'utf8').replace(before,after));
  const doc=JSON.parse(readFileSync(join(f.run.root,TEST)));
  doc.criteria=doc.criteria.map(item=>({...item,text:item.text.replace(before.replace(/^\d+\.\s*/,''),after.replace(/^\d+\.\s*/,''))}));
  writeFileSync(join(f.run.root,TEST),JSON.stringify(doc));
}
// pdd's own saved check batch for the current files, as pdd test writes it.
let batches = 0;
function saveCheck(f, { state = 'passed', criteria = { passed: 3, total: 3 }, tests = [TEST] } = {}) {
  const stamp = new Date(f.clock).toISOString().replace(/[-:]/g, '').replace('T', '-').slice(0, 15), name = `${stamp}-${String(++batches).padStart(4, '0')}`;
  const folder = join(f.ports.env.PDD_STATE_DIR, 'batches', name), capture = captureSource(f.run.root, { tests, appMap: null });
  mkdirSync(folder, { recursive: true });
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({ version: 1, batch: name, root: f.run.root, created_at: new Date(f.clock).toISOString(), intent: 'check',
    source_sha256: capture.sha256, files: capture.files.map(file => file.path), contract_snapshots: capture.stories, rows: tests.map(test => ({ test, state, request_ids: [] })) }));
  const line = `Prompt tests (place-order): ${state === 'passed' ? '✓' : '✗'} ${criteria ? `${criteria.passed} of ${criteria.total} criteria` : 'no verdict'}`;
  writeFileSync(join(folder, 'summary.json'), JSON.stringify(renderJson({ batch: name, repo: f.run.root, sourceSha256: capture.sha256, exitCode: state === 'passed' ? 0 : 1, rows: tests.map(test => ({ test, story: test, state, criteria })), summaryLine: line })));
  return name;
}
const approveStory = async (f, words = 'Yes, this is what I asked for.', extra = {}) => {
  f.tick(); const out = await approveRun({ ref: '17', cwd: f.run.root, said: '-', ...extra }, said(f, words)); assert.equal(out.exitCode, 0, out.message); return out;
};

test('#2962 card: the Story gate shows each part from the real fixture files', async t => {
  const f = await storyGate(t), root = f.run.root, card = f.gate.message;
  const storyText = readFileSync(join(root, STORY), 'utf8'), scenario = JSON.parse(readFileSync(join(root, TEST), 'utf8'));
  assert.match(card, /example\/project#17/); assert.ok(card.includes('"Show the order total"')); const issue = new URL(card.split('\n').find(line => line.startsWith('Issue: ')).slice(7));
  assert.equal(issue.protocol, 'https:'); assert.equal(issue.hostname, 'github.com'); assert.equal(issue.pathname, '/example/project/issues/17');
  assert.ok(card.includes(ASKED), 'what the reporter asked, from the saved issue text');
  assert.equal(card.includes('More notes that are not the request'), false);
  for (const line of storyText.split('\n').filter(text => /^\d+\. /.test(text))) assert.ok(card.includes(line), `criterion ${line}`);
  assert.ok(card.includes(KEEP)); assert.ok(card.includes(RULE)); assert.match(card, /Verdict:/);
  assert.ok(card.includes(join(root, STORY)) && card.includes(join(root, TEST)) && card.includes(join(root, PROMPT)), 'full file paths');
  const row = card.split('\n').find(line => line.trimStart().startsWith(`| ${scenario.steps[0].step_id} |`));
  assert.ok(row, 'one table row for the test case'); assert.match(row, /"customerName":"Sam"/); assert.match(row, /AC1 \/totalCents equals 900/);
  const promptLines = readFileSync(join(root, PROMPT), 'utf8').split('\n').length - 1;
  assert.ok(card.includes(`${join(root, PROMPT)} (+${promptLines} −0 lines)`), 'the prompt that changes, with its lines');
  // The read-only command prints the same card and changes nothing.
  const before = readFileSync(join(f.run.runDir, 'status.json'), 'utf8');
  const shown = await showStoryCard({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(shown.exitCode, 0, shown.message);
  assert.ok(card.includes(shown.message), 'the gate prints the card of pdd workflow card');
  assert.equal(readFileSync(join(f.run.runDir, 'status.json'), 'utf8'), before);
  // A batch of runs: status names the runs that wait for a Story approval.
  f.herdr.idle();
  const status = await runStatus({ cwd: f.source }, f.ports);
  assert.ok(status.message.split('\n').some(line => line.includes('example/project#17') && line.includes('pdd workflow card')), status.message);
  assert.equal(JSON.parse((await runStatus({ cwd: f.source, json: true }, f.ports)).message).runs[0].waitingForStory, true);
});

test('#2962 card: long test tables are cut with a count and the path', async t => {
  const f = await storyGate(t), root = f.run.root, scenario = JSON.parse(readFileSync(join(root, TEST), 'utf8'));
  scenario.steps = Array.from({ length: 11 }, (_, index) => ({ ...scenario.steps[0], step_id: `case-${index + 1}` }));
  writeFileSync(join(root, TEST), JSON.stringify(scenario));
  const card = (await showStoryCard({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.ok(card.includes('| case-8 |') && !card.includes('| case-9 |'));
  assert.ok(card.split('\n').some(line => line.includes('3') && line.includes(join(root, TEST)) && line.startsWith('  … ')), card);
  scenario.story_path = 'user_stories/missing.md';
  writeFileSync(join(root, TEST), JSON.stringify(scenario));
  const missing = (await showStoryCard({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.ok(missing.includes(join(root, scenario.story_path)));
  assert.match(missing, /cannot read/);
  const outside = join(f.base, 'user_stories'); mkdirSync(outside);
  writeFileSync(join(outside, 'private.md'), '## Acceptance criteria\n\n1. PRIVATE_SENTINEL\n');
  scenario.story_path = '../../user_stories/private.md';
  writeFileSync(join(root, TEST), JSON.stringify(scenario));
  const escaped = (await showStoryCard({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.equal(escaped.includes('PRIVATE_SENTINEL'), false);
});

test('#2962 a full check pass opens PR 1 with no question and skips try; pdd stops after PR 1', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  let record = f.record();
  assert.equal(record.areas[record.area].name, 'prompt-pr'); assert.equal(record.through, undefined); assert.ok(record.storyApproval?.evidenceId);
  const batch = saveCheck(f);
  f.prompts.length = 0;
  const out = await f.done('check', 'Prompt tests (place-order): ✓ 3 of 3 criteria');
  record = f.record();
  assert.equal(f.prs.length, 1, out.message); assert.equal(f.prompts.length, 0, 'no terminal question');
  assert.equal(record.done.try.skipped.by, 'pdd', 'try is not asked');
  assert.equal(record.gate?.kind, 'ask-code'); assert.equal(record.areas[record.area].name, 'prompt-pr', 'no code area without a code choice');
  const decision = record.decisions.at(-1);
  assert.equal(decision.via, 'automatic-check-pass'); assert.equal(decision.evidence.words, null);
  assert.deepEqual(decision.evidence.basis, { storyEvidenceId: record.storyApproval.evidenceId, batches: [batch], headSha: f.prs[0].headRefOid });
  assert.ok(out.message.includes(f.prs[0].url));
  assert.equal(record.question, null);
  await autopilotUnchanged(t);
});

test('#2962 a failed check does not open PR 1 and keeps the gate', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  saveCheck(f, { state: 'failed', criteria: { passed: 2, total: 3 } });
  const out = await f.done('check', 'Prompt tests (place-order): ✗ 2 of 3 criteria');
  const record = f.record();
  assert.equal(f.prs.length, 0, out.message); assert.equal(record.gate?.kind, 'approve-pr'); assert.equal(record.state, 'waiting');
  assert.ok(out.message.split('\n').some(line => line.includes('failed') && line.includes(TEST)), out.message);
  assert.equal(record.decisions.some(item => item.via === 'automatic-check-pass'), false);
});

test('#2962 an AI-service failure is no verdict: no PR 1 and no approval question', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  saveCheck(f, { state: 'refused', criteria: null });
  const out = await f.done('check', 'Prompt tests (place-order): no verdict');
  assert.equal(f.prs.length, 0);
  assert.ok(out.message.split('\n').some(line => line.includes('no-verdict') && line.includes(TEST)), out.message);
  assert.equal(f.record().question, null);
});

test('#2962 a changed expected value reopens the Story gate; the person approval then opens PR 1', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  const scenario = JSON.parse(readFileSync(join(f.run.root, TEST), 'utf8'));
  scenario.steps[0].checks.find(check => check.path === '/totalCents').value = 950;
  writeFileSync(join(f.run.root, TEST), JSON.stringify(scenario, null, 2));
  saveCheck(f);
  const out = await f.done('check', 'Prompt tests (place-order): ✓ 3 of 3 criteria');
  let record = f.record();
  assert.equal(f.prs.length, 0, 'no PR 1 before the person sees the change'); assert.equal(record.gate?.kind, 'approve-pr');
  assert.ok(record.gate?.storyChanges?.some(line => line.includes(TEST)));
  const change = out.message.split('\n').find(line => line.includes(scenario.steps[0].step_id) && line.includes('900') && line.includes('950'));
  assert.ok(change, out.message);
  assert.ok(out.message.includes(join(f.run.root, STORY)), 'the card shows again');
  f.tick();
  const approved = await approveRun({ ref: '17', cwd: f.run.root, said: '-' }, said(f, '950 is right now.'));
  assert.equal(approved.exitCode, 0, approved.message);
  record = f.record();
  assert.equal(f.prs.length, 1); assert.equal(record.gate?.kind, 'ask-code');
  assert.equal(record.storyApproval.fingerprint.tests[0].cases[0].text.includes('950'), true);
});

test('#2962 a changed Story reopens the Story gate', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  reviseStory(f, '1. An order', '1. Any order');
  saveCheck(f);
  await f.done('check');
  assert.equal(f.prs.length, 0); assert.ok(f.record().gate?.storyChanges?.some(line => line.includes(STORY)));
});

test('#2962 a prompt-only repair that passes the check keeps the Story approval', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  const before = f.record().storyApproval;
  const text = readFileSync(join(f.run.root, PROMPT), 'utf8');
  writeFileSync(join(f.run.root, PROMPT), text.replace('Return the order:', 'Return the priced order:'));
  saveCheck(f);
  const out = await f.done('check');
  const record = f.record();
  assert.equal(f.prs.length, 1, out.message); assert.equal(record.decisions.at(-1).via, 'automatic-check-pass');
  assert.deepEqual(record.storyApproval, before);
  const iface = JSON.parse(readFileSync(join(f.run.root, PROMPT), 'utf8').match(/```json\n([\s\S]*?)\n```/)[1]);
  const { proseSha256 } = await import('../src/runtime/runtime-preflight.mjs');
  assert.equal(iface.status, 'approved'); assert.equal(iface.prose_sha256, proseSha256(readFileSync(join(f.run.root, PROMPT), 'utf8')));
  assert.match(f.prs[0].body, /automatic-check-pass/);
});

test('#2962 the approval covers the card that was shown: a later Story edit needs a new card', async t => {
  const f = await storyGate(t), before = f.record();
  reviseStory(f, '900 cents', '901 cents');
  f.tick();
  const refused = await approveRun({ ref: '17', cwd: f.run.root, said: '-' }, said(f, 'Approved.'));
  assert.equal(refused.exitCode, 1);
  assert.equal(f.record().area, before.area); assert.deepEqual(f.record().decisions, before.decisions);
  await f.done('prompt-story');
  await approveStory(f, 'Approved.');
  assert.equal(f.record().areas[f.record().area].name, 'prompt-pr');
});

test('#2962 code-or-stop is chosen at the card: --through code makes the code area start after PR 1', async t => {
  const f = await storyGate(t);
  const stop = (await showStoryCard({ ref: '17', cwd: f.source }, f.ports)).message;
  await approveStory(f, 'Approve, and make the code PR too.', { through: 'code' });
  assert.equal(f.record().through, 'code');
  const go = (await showStoryCard({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.notEqual(go.split('\n').find(line => line.startsWith('Next step:')), stop.split('\n').find(line => line.startsWith('Next step:')));
  saveCheck(f);
  const out = await f.done('check');
  const record = f.record();
  assert.equal(f.prs.length, 1, out.message);
  assert.equal(record.areas[record.area].name, 'code', out.message);
  assert.equal(record.decisions.at(-1).via, 'card-choice');
  assert.equal(record.metricsOrigin.requiredOutcome, 'code');
});

test('#2962 the run option --through code is saved and used at the card', async t => {
  const f = await storyGate(t, { through: 'code' });
  assert.equal(f.record().through, 'code');
  await approveStory(f);
  assert.equal(f.record().through, 'code');
  const refused = await approveRun({ ref: '17', cwd: f.run.root, said: 'yes', through: 'later' }, f.agentPorts());
  assert.equal(refused.exitCode, 1);
});

test('#3103 a normal run without saved Story coverage keeps its person gate', async t => {
  const f = await storyGate(t);
  assert.equal((await approveRun({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  const run = f.record();
  delete run.storyApproval;
  writeRun(run);
  saveCheck(f);
  await f.done('check');
  if (!f.record().done.try) await f.done('try', 'synthetic skip', {skipped: 'no simulation'});
  assert.equal(f.record().storyApproval, undefined);
  assert.equal(f.record().gate.kind, 'approve-pr');
  assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
});

test('#2962 strict mode keeps today\'s gates: no card, try is asked, no automatic PR 1, the code question stays', async t => {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  f.ports.env.PDD_STATE_DIR = join(f.state, 'runtime');
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ strict_approvals: true }));
  assert.equal((await startRun({ name: 'feature', issue: '17', agent: 'codex', through: 'code', cwd: f.source, packageRoot }, f.ports)).exitCode, 1, 'strict mode refuses the normal-only start option');
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record();
  const done = async (step, extra = {}) => { f.tick(); const out = await stepDone({ step, summary: step, cwd: run.root, ...extra }, f.agentPorts()); assert.equal(out.exitCode, 0, out.message); return out; };
  await done('understand'); await done('visual', { skipped: 'no screen' });
  for (const dir of ['prompts', 'user_stories', 'tests']) mkdirSync(join(run.root, dir), { recursive: true });
  for (const path of [PROMPT, STORY, TEST]) cpSync(join(harbor, path), join(run.root, path));
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'Story');
  const gate = await done('prompt-story');
  assert.equal(gate.message.includes(join(run.root, TEST)), false, 'no card in strict mode');
  assert.equal((await approveRun({ ref: '17', cwd: f.source, through: 'code' }, f.ports)).exitCode, 1, 'no card choice in strict mode');
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.equal(f.record().storyApproval, undefined);
  f.run = run; saveCheck(f);
  await done('check');
  assert.equal(f.record().done.try, undefined, 'try is still a step for the agent');
  await done('try', { skipped: 'person declined' });
  assert.equal(f.prs.length, 0, 'strict mode never opens PR 1 without the person'); assert.equal(f.record().gate?.kind, 'approve-pr');
  const answers = [true, false]; f.prompts.length = 0; f.ports.confirm = async question => { f.prompts.push(question); return answers.shift(); }; f.tick();
  const opened = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(opened.exitCode, 0, opened.message);
  assert.equal(f.prs.length, 1); assert.equal(f.prompts.length, 2, 'the terminal still asks the code question');
});

// The automatic-run harness of workflow-automatic-continuation.test.mjs, for a bug run.
const origin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };
async function autopilotUnchanged(t) {
  const f = await fixture(t, { name: 'bug', agent: 'codex' });
  assert.equal((await startRun({ name: 'bug', issue: '17', agent: 'codex', through: 'code', coordinator: { ...origin, activation: 'start-a' }, cwd: f.source, packageRoot }, f.ports)).exitCode, 1, 'Autopilot refuses the normal-only start option');
  f.ports.env = { HOME: f.ports.env.HOME, PDD_STATE_DIR: join(f.state, 'runtime') };
  assert.equal((await startRun({ name: 'bug', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  let run = f.record();
  for (const dir of ['prompts', 'user_stories', 'tests']) mkdirSync(join(run.root, dir), { recursive: true });
  for (const path of [PROMPT, STORY, TEST]) cpSync(join(harbor, path), join(run.root, path));
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'Story');
  for (const step of ['reproduce', 'prompt-story']) { f.tick(); const r = await stepDone({ step, summary: step, cwd: run.root }, f.agentPorts()); assert.equal(r.exitCode, 0, r.message); }
  run = f.record(); run.automaticOrigin = structuredClone(origin); writeRun(run);
  const root = realpathSync(f.source), stateRoot = join(f.state, 'autopilot'); mkdirSync(stateRoot, { recursive: true });
  writeFileSync(join(stateRoot, `${createHash('sha256').update(root).digest('hex').slice(0, 20)}.json`), JSON.stringify({ repo: run.repo, cwd: root, coordinatorId: origin.coordinatorId }));
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const fixturePath = join(f.base, 'reader.json'), exec = promisify(callbackExec), original = f.ports.execFile;
  writeFileSync(fixturePath, JSON.stringify({ labels: ['pdd:working'], events: [{ id: 12, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' } }], comments: [{ id: 11, user: { login: 'example' }, body: JSON.stringify({ repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, labelEventId: '12' }) }] }));
  const execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === '--include' ? exec(process.execPath, [join(packageRoot, 'test/helpers/continuation-fake-gh.mjs'), ...args], { ...opts, env: { ...process.env, READER_FIXTURE_FILE: fixturePath, READER_GH_LOG: join(f.base, 'gh.log') } }) : original(file, args, opts);
  const ports = () => ({ ...f.agentPorts(), execFile, autopilotStateRoot: stateRoot });
  f.tick();
  const approved = await approveRun({ ref: '17', cwd: run.root, said: 'I approve' }, ports());
  assert.equal(approved.exitCode, 0, approved.message);
  assert.equal(f.record().storyApproval, undefined);
  f.run = run; saveCheck(f);
  f.tick(); assert.equal((await stepDone({ step: 'check', summary: 'check', cwd: run.root }, ports())).exitCode, 0);
  assert.equal(f.record().done.try, undefined, 'Autopilot keeps its own try route');
  f.tick(); assert.equal((await stepDone({ step: 'try', skipped: 'pdd-check runs the changed path', cwd: run.root }, ports())).exitCode, 0);
  assert.equal(f.prs.length, 0); assert.equal(f.record().gate?.kind, 'approve-pr');
}


test('#2962 a card stays bounded with many Stories and keeps the final choice', async t => {
  const f = await storyGate(t), root = f.run.root;
  for (let i = 0; i < 180; i++) writeFileSync(join(root, 'user_stories', `extra-${i}.md`), readFileSync(join(root, STORY)));
  const card = (await showStoryCard({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.ok(card.split('\n').length <= 160);
  assert.match(card, /161 more Stories/);
  assert.match(card.split('\n').slice(-3).join('\n'), /Next step:.*PR 1/);
});

test('#2962 a Story named by a changed test is in the card and its approval', async t => {
  const f = await storyGate(t, { existingStory: true });
  assert.ok(f.gate.message.includes(join(f.run.root, STORY)));
  await approveStory(f);
  assert.equal(f.record().storyApproval.fingerprint.stories[0].path, STORY);
  reviseStory(f, '900 cents', '950 cents');
  saveCheck(f);
  const out = await f.done('check');
  assert.equal(f.prs.length, 0);
  assert.ok(f.record().gate?.storyChanges?.some(line => line.includes(STORY)), out.message);
});

test('#2962 a stale or incomplete check cannot open PR 1; a fresh full check can', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  const approval = f.record().storyApproval;
  saveCheck(f);
  writeFileSync(join(f.run.root, PROMPT), readFileSync(join(f.run.root, PROMPT), 'utf8').replace('Return the order:', 'Return the priced order:'));
  let out = await f.done('check');
  assert.equal(f.prs.length, 0);
  assert.match(out.message, /Not passed \(changed\)/);
  f.tick(); saveCheck(f, { criteria: { passed: 2, total: 3 } });
  out = await f.done('check');
  assert.equal(f.prs.length, 0);
  assert.match(out.message, /Not passed \(failed\)/);
  f.tick(); saveCheck(f, { criteria: { passed: 1, total: 1 } });
  out = await f.done('check');
  assert.equal(f.prs.length, 0, 'all actual criteria must pass');
  assert.match(out.message, /Not passed \(failed\)/);
  // Identical saved file hashes do not excuse stale dependency provenance.
  f.tick(); const changedReferences = saveCheck(f);
  const batchFile = join(f.ports.env.PDD_STATE_DIR, 'batches', changedReferences, 'batch.json');
  const batch = JSON.parse(readFileSync(batchFile, 'utf8'));
  batch.contract_snapshots[0].references = [{ consumer: PROMPT, source_pointer: '/entries/0/input_schema', target: 'contracts/old-order.json', kind: 'contract', value_json: '{"type":"object"}' }];
  writeFileSync(batchFile, JSON.stringify(batch));
  out = await f.done('check');
  assert.equal(f.prs.length, 0, 'saved reference provenance must also match');
  assert.match(out.message, /Not passed \(changed\)/);
  f.tick(); const partialBatch = saveCheck(f);
  const partialFile = join(f.ports.env.PDD_STATE_DIR, 'batches', partialBatch, 'batch.json');
  const partial = JSON.parse(readFileSync(partialFile, 'utf8'));
  partial.contract_snapshots[0].tests = ['tests/another-story.json'];
  writeFileSync(partialFile, JSON.stringify(partial));
  out = await f.done('check');
  assert.equal(f.prs.length, 0, 'a partial snapshot cannot use the legacy source hash fallback');
  assert.match(out.message, /Not passed \(unavailable\)/);
  f.tick(); saveCheck(f);
  await f.done('check');
  assert.equal(f.prs.length, 1);
  assert.deepEqual(f.record().storyApproval, approval);
});

test('#2962 typed results cannot replace a missing check, and status does not request approval', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  const out = await f.done('check', 'Prompt tests (place-order): ✓ 3 of 3 criteria');
  assert.equal(f.prs.length, 0);
  assert.equal(f.record().done.try?.skipped?.by, 'pdd');
  assert.equal(f.record().question, null);
  assert.match(out.message, /Not passed \(missing\)/);
  f.herdr.idle();
  const status = JSON.parse((await runStatus({ cwd: f.source, json: true }, f.ports)).message).runs[0];
  assert.equal(status.waitingForStory, false);
  assert.doesNotMatch(status.words, /approve|try it/);
});

test('#2962 approving a changed Story with a failed check keeps the new approval and waits for a pass', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  reviseStory(f, '900 cents', '950 cents');
  saveCheck(f, { state: 'failed', criteria: { passed: 2, total: 3 } });
  await f.done('check');
  assert.ok(f.record().gate?.storyChanges?.length, 'changed Story must reopen the gate');
  f.tick();
  const out = await approveRun({ ref: '17', cwd: f.run.root, said: '-' }, said(f, 'The revised Story is right.'));
  assert.equal(out.exitCode, 0, out.message);
  assert.equal(f.prs.length, 0, 'approving the Story does not make a failed check pass');
  const approval = f.record().storyApproval;
  f.tick(); saveCheck(f);
  await f.done('check');
  assert.equal(f.prs.length, 1);
  assert.deepEqual(f.record().storyApproval, approval);
  assert.equal(f.record().decisions.at(-1).via, 'automatic-check-pass');
});


test('#2962 a Story change after failed publication records the new person approval', async t => {
  const f = await storyGate(t);
  await approveStory(f);
  saveCheck(f);
  f.createError = 'fixture: publication unavailable';
  f.tick();
  const refused = await stepDone({ step: 'check', summary: 'check', cwd: f.run.root }, f.agentPorts());
  assert.equal(refused.exitCode, 1);
  assert.equal(f.prs.length, 0);
  const automatic = f.record().decisions.at(-1);
  assert.equal(automatic.via, 'automatic-check-pass');
  reviseStory(f, '900 cents', '950 cents');
  f.git(f.run.root, 'add', STORY); f.git(f.run.root, 'commit', '-qm', 'Revised Story');
  f.tick(); saveCheck(f);
  await f.done('check');
  assert.notEqual(f.record().gate.id, automatic.gateId);
  const words = 'The revised Story is right.';
  f.tick();
  const out = await approveRun({ ref: '17', cwd: f.run.root, said: '-' }, said(f, words));
  assert.equal(out.exitCode, 0, out.message);
  assert.equal(f.prs.length, 1);
  const decisions = f.record().decisions;
  const person = decisions.find(item => item.evidence?.words === words);
  assert.ok(person, 'the later person decision is retained');
  assert.equal(f.record().storyApproval.evidenceId, person.evidence.id);
  assert.equal(decisions.at(-1).via, 'automatic-check-pass');
  assert.equal(decisions.at(-1).evidence.basis.storyEvidenceId, person.evidence.id);
});


test('#2962 a saved code choice can retry code entry with no new question', async t => {
  for (const merged of [false, true]) {
    const f = await storyGate(t, { through: 'code' });
    await approveStory(f);
    f.ports.readPrStatus = async () => ({ state: 'closed', ci: 'none' });
    saveCheck(f);
    await f.done('check');
    assert.equal(f.prs.length, 1);
    assert.equal(f.record().areas[f.record().area].name, 'prompt-pr');
    assert.equal(f.record().gate.kind, 'ask-code');
    f.herdr.idle();
    const status = JSON.parse((await runStatus({ cwd: f.source, json: true }, f.ports)).message).runs[0];
    assert.doesNotMatch(status.words, /stopped|approve|now or stop/);
    delete f.ports.readPrStatus;
    if (merged) {
      f.merged = true; f.mergedNumbers = [f.prs[0].number];
      await runStatus({ ref: '17', cwd: f.source }, f.ports);
      assert.equal(f.record().doneAt, 'PR 1');
    }
    f.prompts.length = 0;
    await f.done('check');
    assert.equal(f.record().areas[f.record().area].name, 'code');
    assert.equal(f.record().through, 'code');
    assert.equal(f.prompts.length, 0);
  }
});


for (const kind of ['Story', 'expected']) test(`#2962 repair 1: open PR 1 waits for approval of changed ${kind}`, async t => {
  const f = await storyGate(t);
  await approveStory(f);
  saveCheck(f); await f.done('check');
  const pushes = f.pushes.length, edits = f.edits.length, approval = f.record().storyApproval;
  // A saved code choice must not bypass the revised Story gate.
  const record = f.record(); record.through = 'code'; writeRun(record);
  if (kind === 'Story') reviseStory(f, '900 cents', '950 cents');
  else {
    const doc = JSON.parse(readFileSync(join(f.run.root, TEST), 'utf8'));
    doc.steps[0].checks.find(check => check.path === '/totalCents').value = 950;
    writeFileSync(join(f.run.root, TEST), JSON.stringify(doc));
  }
  saveCheck(f);
  const out = await f.done('check');
  assert.equal(f.pushes.length, pushes, 'unapproved behavior must not be pushed');
  assert.equal(f.edits.length, edits, 'unapproved behavior must not update the PR body');
  assert.equal(f.record().areas[f.record().area].name, 'prompt-pr');
  assert.equal(f.record().gate.kind, 'approve-pr');
  assert.ok(f.record().gate.storyChanges.some(line => line.includes(kind === 'Story' ? STORY : TEST)));
  assert.ok(out.message.includes(join(f.run.root, STORY)));
  assert.deepEqual(f.record().storyApproval, approval);
  // Reapproval permits the existing PR update, then follows the saved code choice.
  await approveStory(f, 'Approve the revised case.');
  assert.equal(f.prs.length, 1);
  assert.ok(f.pushes.length > pushes);
  assert.equal(f.record().areas[f.record().area].name, 'code');
});

test('#2962 repair 1: open PR 1 accepts a checked prompt-only repair with the same Story approval', async t => {
  const f = await storyGate(t);
  await approveStory(f); saveCheck(f); await f.done('check');
  const approval = f.record().storyApproval, pushes = f.pushes.length;
  writeFileSync(join(f.run.root, PROMPT), readFileSync(join(f.run.root, PROMPT), 'utf8').replace('Return the order:', 'Return the priced order:'));
  await f.done('check');
  assert.equal(f.pushes.length, pushes, 'a stale check cannot publish a prompt repair');
  saveCheck(f); await f.done('check');
  assert.ok(f.pushes.length > pushes);
  assert.equal(f.prs.length, 1);
  assert.deepEqual(f.record().storyApproval, approval);
});

test('#2962 repair 1: an unchecked existing scenario blocks the full pass; selective rechecks reuse current results', async t => {
  const f = await storyGate(t, { existingScenario: true });
  await approveStory(f);
  saveCheck(f); await f.done('check');
  assert.equal(f.prs.length, 0, 'an unchecked existing Story must block automatic PR 1');
  // The full check can be accumulated across batches. The latest place-order result replaces its failure.
  f.tick(); saveCheck(f, { tests: ['tests/existing-order.json'] });
  f.tick(); saveCheck(f, { state: 'failed', criteria: { passed: 2, total: 3 } });
  await f.done('check'); assert.equal(f.prs.length, 0);
  f.tick(); saveCheck(f); await f.done('check');
  assert.equal(f.prs.length, 1);
});

for (const field of ['batch', 'repo', 'source_sha256']) test(`#2962 repair 1: a foreign summary ${field} cannot supply a verdict`, async t => {
  const f = await storyGate(t);
  await approveStory(f);
  const name = saveCheck(f), path = join(f.ports.env.PDD_STATE_DIR, 'batches', name, 'summary.json');
  const summary = JSON.parse(readFileSync(path, 'utf8'));
  summary[field] = field === 'batch' ? '20261027-170000-zzzz' : field === 'repo' ? f.source : '0'.repeat(64);
  writeFileSync(path, JSON.stringify(summary));
  await f.done('check');
  assert.equal(f.prs.length, 0, 'a mismatched summary must block automatic PR 1');
  f.tick(); saveCheck(f); await f.done('check'); assert.equal(f.prs.length, 1);
});

test('#2962 repair 1: the native card retains wrapped criteria and reports bounded omissions', async t => {
  const f = await storyGate(t), path = join(f.run.root, STORY);
  const lines = readFileSync(path, 'utf8').split('\n'), first = lines.findIndex(line => /^1\. /.test(line));
  lines.splice(first + 1, 0, '   criterion-continuation-1', '   criterion-continuation-2');
  writeFileSync(path, lines.join('\n'));
  const exec = promisify(callbackExec);
  const card = async () => (await exec(process.execPath, [join(packageRoot, 'bin/pdd.mjs'), 'workflow', 'card', '17'], { cwd: f.run.root, env: { ...process.env, ...f.ports.env } })).stdout;
  const shown = await card();
  for (const line of lines.slice(first, first + 3)) assert.ok(shown.includes(line.trim()), 'the full criterion must be shown before approval');
  lines.splice(first + 1, 0, ...Array.from({ length: 20 }, (_, i) => `   continuation-${i}`));
  writeFileSync(path, lines.join('\n'));
  const bounded = await card();
  assert.ok(bounded.split('\n').length <= 160);
  assert.ok(bounded.split('\n').some(line => line.includes('…') && line.includes(join(f.run.root, STORY))), 'omitted criterion lines name the file');
  assert.equal(bounded.includes('continuation-19'), false);
});

test('#2962 repair 1: the real saved-result writer binds publication to its summary identity', async t => {
  const f = await storyGate(t); await approveStory(f);
  const fake = await fakeRuntime(t, (entry, runtime) => {
    if (entry.command === 'lint') return { status: 200, json: runtime.lint(entry.request.requestId) };
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return { status: 200, json: runtime.check(id, 'passed', ['AC1', 'AC2', 'AC3'].map(criterion_id => ({ criterion_id, target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }))) };
  });
  const made = portsFor({ ...f.ports.env, PDD_RUNTIME_URL: fake.origin }); made.clock.now = f.clock;
  const exit = await runCheck({ cwd: f.run.root, words: [], options: { '--json': true } }, made.ports);
  assert.equal(exit, 0, made.ports.stderr.text);
  const result = JSON.parse(made.ports.stdout.text);
  assert.equal(result.rows[0].state, 'passed');
  assert.deepEqual(result.rows[0].criteria, { passed: 3, total: 3 });
  const summaryPath = join(f.ports.env.PDD_STATE_DIR, 'batches', result.batch, 'summary.json');
  const original = readFileSync(summaryPath, 'utf8'), foreign = JSON.parse(original);
  foreign.batch = '20261027-170000-zzzz';
  writeFileSync(summaryPath, JSON.stringify(foreign));
  await f.done('check'); assert.equal(f.prs.length, 0, 'a foreign summary cannot publish the real writer batch');
  writeFileSync(summaryPath, original);
  await f.done('check'); assert.equal(f.prs.length, 1);
  assert.deepEqual(f.record().decisions.at(-1).evidence.basis.batches, [result.batch]);
});


test('#2962 repair 1: a saved code choice after merged PR 1 cannot bypass a revised Story', async t => {
  const f = await storyGate(t, { through: 'code' });
  await approveStory(f);
  f.ports.readPrStatus = async () => ({ state: 'closed', ci: 'none' });
  saveCheck(f); await f.done('check');
  delete f.ports.readPrStatus;
  f.merged = true; f.mergedNumbers = [f.prs[0].number];
  await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(f.record().doneAt, 'PR 1');
  reviseStory(f, '900 cents', '950 cents');
  const pushes = f.pushes.length, edits = f.edits.length;
  await f.done('check');
  assert.equal(f.record().areas[f.record().area].name, 'prompt-pr', 'a revised Story must block saved code entry');
  assert.equal(f.record().gate.kind, 'approve-pr');
  assert.ok(f.record().gate.storyChanges.some(line => line.includes(STORY)));
  assert.equal(f.pushes.length, pushes); assert.equal(f.edits.length, edits);
});

test('#2962 repair 2: normal full checks should not require excluded nested fixture projects', async t => {
  const f = await storyGate(t, { existingFixtures: true });
  await approveStory(f);
  const fake = await fakeRuntime(t, (entry, runtime) => {
    if (entry.command === 'lint') return { status: 200, json: runtime.lint(entry.request.requestId) };
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return { status: 200, json: runtime.check(id, 'passed', ['AC1', 'AC2', 'AC3'].map(criterion_id => ({ criterion_id, target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }))) };
  });
  const made = portsFor({ ...f.ports.env, PDD_RUNTIME_URL: fake.origin }); made.clock.now = f.clock;
  const exit = await runCheck({ cwd: f.run.root, words: [], options: { '--json': true } }, made.ports);
  assert.equal(exit, 0, made.ports.stderr.text);
  const result = JSON.parse(made.ports.stdout.text);
  assert.equal(result.rows.length, 1, 'the real default check excludes nested fixtures');
  const out = await f.done('check');
  assert.equal(f.prs.length, 1, out.message);
});

for (const route of ['said', 'terminal']) for (const merged of [false, true]) {
  test(`#2962 repair 2: later ${route} code request reopens changed Story, merged=${merged}`, async t => {
    const f = await storyGate(t); await approveStory(f); saveCheck(f); await f.done('check');
    if (merged) { f.merged = true; await runStatus({ ref: '17', cwd: f.source }, f.ports); assert.equal(f.record().state, 'completed'); }
    const pushes = f.pushes.length, edits = f.edits.length, decisions = f.record().decisions.length, questions = f.prompts.length;
    reviseStory(f, '900 cents', '950 cents');
    f.git(f.run.root, 'add', STORY); f.git(f.run.root, 'commit', '-qm', 'Unapproved Story revision');
    const out = route === 'said' ? await approveStory(f, 'Make the code PR now.') : await approveRun({ ref: '17', cwd: f.source }, f.ports);
    assert.equal(f.pushes.length, pushes, 'a code request cannot publish an unseen Story');
    assert.equal(f.edits.length, edits); assert.equal(f.record().decisions.length, decisions);
    assert.equal(f.prompts.length, questions, 'show the revised card before asking for code approval');
    assert.equal(f.record().areas[f.record().area].name, 'prompt-pr', out.message);
    assert.equal(f.record().gate.kind, 'approve-pr'); assert.ok(out.message.includes(join(f.run.root, STORY)));
    assert.equal(f.record().state, 'waiting');
  });
}

test('#2962 repair 2: later code request needs a current check for a prompt-only repair', async t => {
  const f = await storyGate(t); await approveStory(f); saveCheck(f); await f.done('check');
  const approval = f.record().storyApproval, pushes = f.pushes.length, decisions = f.record().decisions.length;
  writeFileSync(join(f.run.root, PROMPT), readFileSync(join(f.run.root, PROMPT), 'utf8').replace('Return the order:', 'Return the priced order:'));
  f.git(f.run.root, 'add', PROMPT); f.git(f.run.root, 'commit', '-qm', 'Repair prompt');
  await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(f.pushes.length, pushes, 'a stale check cannot synchronize prompt repairs at code approval');
  assert.equal(f.record().decisions.length, decisions);
  assert.deepEqual(f.record().storyApproval, approval);
  saveCheck(f); await f.done('check');
  await approveStory(f, 'Make the code PR now.');
  assert.equal(f.record().areas[f.record().area].name, 'code');
  assert.deepEqual(f.record().storyApproval, approval);
});

test('#2962 repair 2: terminal code confirmation cannot approve a Story changed during the question', async t => {
  const f = await storyGate(t); await approveStory(f); saveCheck(f); await f.done('check');
  const pushes = f.pushes.length, decisions = f.record().decisions.length;
  const out = await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async () => {
    reviseStory(f, '900 cents', '950 cents');
    f.git(f.run.root, 'add', STORY); f.git(f.run.root, 'commit', '-qm', 'Story changed while answering');
    return true;
  } });
  assert.equal(f.pushes.length, pushes, 'terminal confirmation cannot publish a newly changed Story');
  assert.equal(f.record().decisions.length, decisions);
  assert.equal(f.record().gate.kind, 'approve-pr', out.message);
  assert.equal(f.record().areas[f.record().area].name, 'prompt-pr');
});

for(const reopened of [false,true]) test(`2962 integration confirmation: ${reopened?'reopened':'initial'} Story gate refuses a change during terminal confirmation`, async t=>{
  const f=await storyGate(t);
  let scenario;
  if(reopened) {
    await approveStory(f);
    scenario=JSON.parse(readFileSync(join(f.run.root,TEST)));
    scenario.steps[0].checks.find(c=>c.path==='/totalCents').value=950;
    writeFileSync(join(f.run.root,TEST),JSON.stringify(scenario));saveCheck(f);await f.done('check');
    assert.ok(f.record().gate.storyChanges.length);
  }
  const before=f.record(),prompt=readFileSync(join(f.run.root,PROMPT),'utf8');
  const out=await approveRun({ref:'17',cwd:f.source},{...f.ports,confirm:async()=>{
    if(reopened) {
      scenario.steps[0].checks.find(c=>c.path==='/totalCents').value=975;
      writeFileSync(join(f.run.root,TEST),JSON.stringify(scenario));saveCheck(f);
    } else writeFileSync(join(f.run.root,STORY),readFileSync(join(f.run.root,STORY),'utf8').replace('900 cents','950 cents'));
    return true;
  }});
  assert.equal(out.exitCode,1);
  assert.equal(f.prs.length,0);assert.deepEqual(f.record().decisions,before.decisions);
  assert.deepEqual(f.record().storyApproval,before.storyApproval);
  assert.equal(readFileSync(join(f.run.root,PROMPT),'utf8'),prompt);
  assert.equal(f.record().area,before.area);
});

test('2962 integration completeness: a missing approved Story test blocks until both Stories have current checks', async t=>{
  const f=await storyGate(t),second='user_stories/refund-order.md';
  writeFileSync(join(f.run.root,second),readFileSync(join(harbor,STORY),'utf8').replace('# Place a coffee order','# Refund an order'));
  f.git(f.run.root,'add',second);f.git(f.run.root,'commit','-qm','Second Story without a test');
  await f.done('prompt-story');await approveStory(f);
  const fake=await fakeRuntime(t,(entry,runtime)=>{
    if(entry.command==='lint')return {status:200,json:runtime.lint(entry.request.requestId)};
    const id=entry.request?.requestId??entry.url.split('/').at(-1);
    return {status:200,json:runtime.check(id,'passed',['AC1','AC2','AC3'].map(criterion_id=>({criterion_id,target:'result',path:'/totalCents',op:'equals',expected:900,actual:900,passed:true})))};
  });
  const check=async()=>{
    const made=portsFor({...f.ports.env,PDD_RUNTIME_URL:fake.origin});made.clock.now=f.clock;
    const code=await runCheck({cwd:f.run.root,words:[],options:{'--json':true}},made.ports);
    assert.equal(code,0,made.ports.stderr.text);
    return JSON.parse(made.ports.stdout.text);
  };
  assert.equal((await check()).rows.length,1);
  const out=await f.done('check');
  assert.equal(f.prs.length,0);assert.ok(out.message.includes(second));
  assert.ok(!f.record().decisions.some(d=>d.via==='automatic-check-pass'));
  const scenario=JSON.parse(readFileSync(join(f.run.root,TEST)));
  writeFileSync(join(f.run.root,'tests/refund-order.json'),JSON.stringify({...scenario,story_path:second}));
  f.git(f.run.root,'add','.');f.git(f.run.root,'commit','-qm','Complete the second Story test');
  assert.equal((await check()).rows.length,2);
  await f.done('check');await approveStory(f);
  assert.equal(f.prs.length,1);
  assert.equal(f.record().decisions.at(-1).via,'automatic-check-pass');
});

// Exercise the native writer before deliberately interrupting a saved transition.
async function writeRealCheck(f, t) {
  const fake = await fakeRuntime(t, (entry, runtime) => {
    if (entry.command === 'lint') return { status: 200, json: runtime.lint(entry.request.requestId) };
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return { status: 200, json: runtime.check(id, 'passed', ['AC1', 'AC2', 'AC3'].map(criterion_id =>
      ({ criterion_id, target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }))) };
  });
  const made = portsFor({ ...f.ports.env, PDD_RUNTIME_URL: fake.origin }); made.clock.now = f.clock;
  assert.equal(await runCheck({ cwd: f.run.root, words: [], options: { '--json': true } }, made.ports), 0, made.ports.stderr.text);
  return JSON.parse(made.ports.stdout.text).batch;
}
for (const fault of ['not run', 'partial', 'refused', 'unchecked', 'broken', 'duplicate', 'criteria']) {
  test(`release: native batch ${fault} blocks a stale passing summary and recovers`, async t => {
    const f = await storyGate(t); await approveStory(f); const batch = await writeRealCheck(f, t);
    const path = join(f.ports.env.PDD_STATE_DIR, 'batches', batch, 'batch.json');
    const good = readFileSync(path, 'utf8'), saved = JSON.parse(good);
    if (fault === 'unchecked') saved.rows[0].not_checked = ['AC3'];
    else if (fault === 'broken') saved.rows[0].reason = { code: 'broken-test' };
    else if (fault === 'duplicate') saved.rows.push({ ...saved.rows[0] });
    else if (fault === 'criteria') saved.rows[0].criteria = { passed: 2, total: 3 };
    else saved.rows[0].state = fault;
    writeFileSync(path, JSON.stringify(saved));
    await f.done('check');
    assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
    assert.equal(f.record().decisions.some(row => row.via === 'automatic-check-pass'), false);
    writeFileSync(path, good);
    await f.done('check'); assert.equal(f.prs.length, 1);
  });
}
for (const existing of [false, true]) for (const target of ['prompt', 'Story', 'expected', 'dependency']) {
  test(`release: publication revalidates late ${target} edits (${existing ? 'update' : 'new'})`, async t => {
    const f = await storyGate(t); await approveStory(f);
    if (target === 'dependency') {
      writeFileSync(join(f.run.root, 'rules.md'), 'The menu uses whole cents.\n');
      writeFileSync(join(f.run.root, PROMPT), readFileSync(join(f.run.root, PROMPT), 'utf8').replace('## Dependencies', '## Dependencies\n\n- [Rules](../rules.md)'));
    }
    if (target === 'dependency') {
      const path = join(f.run.root, PROMPT);
      writeFileSync(path, readFileSync(path, 'utf8').replace('\"status\": \"approved\"', '\"status\": \"draft\"'));
      const filled = fillHashes({ root: f.run.root }); assert.equal(filled.refused.length, 0);
    }
    await writeRealCheck(f, t);
    if (existing) { await f.done('check'); await writeRealCheck(f, t); }
    const decisions = f.record().decisions.filter(row => row.via === 'automatic-check-pass').length;
    const pushes = f.pushes.length, edits = f.edits.length;
    const original = f.ports.execFile; let changed = false;
    f.ports.execFile = async (file, args, options) => {
      if (!changed && file === 'git' && args[0] === 'status' && args.includes('--porcelain=v1')) {
        changed = true;
        if (target === 'prompt') writeFileSync(join(f.run.root, PROMPT), readFileSync(join(f.run.root, PROMPT), 'utf8').replace('Return the order:', 'Return different prices:'));
        if (target === 'Story') writeFileSync(join(f.run.root, STORY), readFileSync(join(f.run.root, STORY), 'utf8') + '\nNew requirement.\n');
        if (target === 'expected') reviseStory(f, '900', '950');
        if (target === 'dependency') writeFileSync(join(f.run.root, 'rules.md'), 'The menu uses different prices.\n');
      }
      return original(file, args, options);
    };
    f.tick(); await stepDone({ step: 'check', summary: 'checked', cwd: f.run.root }, f.agentPorts());
    assert.equal(changed, true); assert.equal(f.prs.length, existing ? 1 : 0);
    assert.equal(f.pushes.length, pushes); assert.equal(f.edits.length, edits);
    assert.equal(f.record().decisions.filter(row => row.via === 'automatic-check-pass').length, decisions);
    if (['Story', 'expected'].includes(target)) assert.equal(f.record().gate.kind, 'approve-pr');
  });
}

for (const boundary of ['metadata-commit', 'prepared-intent', 'metadata-Story', 'prepared-Story', 'metadata-mode']) test(`release: approval waits for validation at ${boundary}`, async t => {
  const f = await storyGate(t); await approveStory(f); await writeRealCheck(f, t);
  const original = f.ports.execFile; let changed = false, statuses = 0;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'git' && args[0] === 'status') statuses++;
    if (!changed && file === 'git' && (boundary.startsWith('metadata-') ? args[0] === 'status' && statuses === 2 : args[0] === 'symbolic-ref')) {
      changed = true;
      if (boundary.endsWith('Story')) writeFileSync(join(f.run.root, STORY), readFileSync(join(f.run.root, STORY), 'utf8') + '\nNew requirement.\n');
      else if (boundary.endsWith('mode')) chmodSync(join(f.run.root, PROMPT), 0o755);
      else writeFileSync(join(f.run.root, PROMPT), readFileSync(join(f.run.root, PROMPT), 'utf8').replace('Return the order:', 'Return different prices:'));
      if (boundary.startsWith('prepared-')) { f.git(f.run.root, 'add', '.'); f.git(f.run.root, 'commit', '-qm', 'Concurrent edit'); }
    }
    return original(file, args, options);
  };
  f.tick(); await stepDone({ step: 'check', summary: 'checked', cwd: f.run.root }, f.agentPorts());
  assert.equal(changed, true); assert.equal(f.prs.length, 0); assert.equal(f.pushes.length, 0);
  assert.equal(f.record().decisions.some(row => row.via === 'automatic-check-pass'), false);
  if (boundary.endsWith('Story')) assert.equal(f.record().gate.kind, 'approve-pr');
});
test('release: publication preserves peer commits and pushes the approval-bound commit to a local remote', async t => {
  const f = await storyGate(t); await approveStory(f); await writeRealCheck(f, t);
  const remote = join(f.base, 'publication.git'); f.git(f.base, 'init', '--bare', '-q', remote);
  const native = promisify(callbackExec), original = f.ports.execFile; let peer;
  f.ports.execFile = async (file, args, options) => {
    if (!peer && file === 'git' && args[0] === 'status') {
      writeFileSync(join(f.run.root, 'value.mjs'), 'export const value = 3;\n');
      f.git(f.run.root, 'add', '.'); f.git(f.run.root, 'commit', '-qm', 'Peer work'); peer = f.git(f.run.root, 'rev-parse', 'HEAD');
    }
    if (file === 'git' && args[0] === 'push') await native(file, args.map(arg => arg === 'origin' ? remote : arg), options);
    return original(file, args, options);
  };
  await f.done('check');
  const evidence = f.record().decisions.find(row => row.via === 'automatic-check-pass').evidence;
  const pushed = f.git(f.base, '--git-dir=' + remote, 'rev-parse', f.record().branch);
  assert.equal(pushed, evidence.basis.headSha);
  f.git(f.run.root, 'merge-base', '--is-ancestor', peer, pushed);
  assert.equal(f.git(f.base, '--git-dir=' + remote, 'show', `${pushed}:value.mjs`), 'export const value = 3;');
});
