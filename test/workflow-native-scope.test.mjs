// #3430: scoped workflow checks, first-class kind: native-only handling,
// workspace evidence eligibility, and explicit approve-pr progression.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { cpSync, mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { execFile as callbackExec } from 'node:child_process';
import { promisify } from 'node:util';
import { fullCheckPass } from '../src/workflow-story-card.mjs';
import * as runner from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { captureSource, renderJson } from '../src/runtime-seam.mjs';
import { storyTest } from './helpers/runtime-fake.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const {
  advanceAutomaticPr1,
  approveRun,
  associateEvidenceWorkspace,
  runStatus,
  startRun,
  stepDone,
} = runner;

const harbor = join(packageRoot, 'test', 'fixtures', 'harbor');
const STORY = 'user_stories/place-order.md';
const TEST = 'tests/place-order.json';
const PROMPT = 'prompts/place_order.prompt.md';
const NATIVE_PROMPT = 'prompts/fsync_store.prompt.md';
const NATIVE_REASON = 'Durable fsync and atomic rename guarantees cannot be faked by bound ports.';
const ASKED = 'Show my order total before I pay, so I know the price.';
const KEEP = 'The menu prices stay the same.';
const RULE = 'The total is the sum of the line totals, in whole cents; a rounded or estimated total is forbidden.';

const said = (f, words, extra = {}) => ({
  ...f.agentPorts(extra),
  stdin: (async function* () { yield words; })(),
});

function nativePromptText(reason = NATIVE_REASON, body = 'Persist durability records atomically on POSIX filesystems.') {
  return [
    '---',
    'kind: native-only',
    `reason: ${reason}`,
    '---',
    '',
    '# Durable record store',
    '',
    body,
    '',
    '## Domain decisions',
    '',
    '- Flush file bytes and parent directory metadata before acknowledging durability.',
    '',
    '## Dependencies',
    '',
    'None.',
    '',
  ].join('\n');
}

function plainMarkdownPromptText() {
  const full = readFileSync(join(harbor, PROMPT), 'utf8');
  return `${full.split('<details><summary>Runtime interface</summary>')[0].trimEnd()}\n`;
}

let batchCounter = 0;
function saveCheck(f, {
  state = 'passed',
  criteria = { passed: 3, total: 3 },
  tests = [TEST],
  batchRoot = f.run.root,
  summaryRepo = batchRoot,
  stage,
  runId,
} = {}) {
  const stamp = new Date(f.clock).toISOString().replace(/[-:]/g, '').replace('T', '-').slice(0, 15);
  const name = `${stamp}-${String(++batchCounter).padStart(4, '0')}`;
  const folder = join(f.ports.env.PDD_STATE_DIR, 'batches', name);
  const capture = captureSource(batchRoot, { tests, appMap: null, allowMissingInterfaces: true });
  mkdirSync(folder, { recursive: true });
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({
    version: 1,
    batch: name,
    root: batchRoot,
    created_at: new Date(f.clock).toISOString(),
    intent: 'check',
    ...((stage || runId) ? { association: { ...(runId ? { runId } : {}), ...(stage ? { stage } : {}) } } : {}),
    source_sha256: capture.sha256,
    files: capture.files.map(file => file.path),
    contract_snapshots: capture.stories,
    rows: tests.map(testPath => ({ test: testPath, state, request_ids: [] })),
  }));
  const storySlug = tests[0]?.split('/').at(-1)?.replace(/\.json$/, '') || 'place-order';
  const line = `Prompt tests (${storySlug}): ${state === 'passed' ? '✓' : '✗'} ${criteria ? `${criteria.passed} of ${criteria.total} criteria` : 'no verdict'}`;
  writeFileSync(join(folder, 'summary.json'), JSON.stringify(renderJson({
    batch: name,
    repo: summaryRepo,
    sourceSha256: capture.sha256,
    exitCode: state === 'passed' ? 0 : 1,
    rows: tests.map(testPath => ({ test: testPath, story: storySlug, state, criteria })),
    summaryLine: line,
  })));
  return name;
}

async function setupFeatureRun(t, { through, preSeed } = {}) {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  f.ports.skipMetricsDelivery = true;
  f.ports.env.PDD_STATE_DIR = join(f.state, 'runtime');
  const original = f.ports.execFile;
  f.ports.execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/17'
    ? {
      stdout: JSON.stringify({
        number: 17,
        html_url: 'https://github.com/example/project/issues/17',
        title: 'Show the order total',
        body: `## User request\n\n> ${ASKED}\n`,
      }),
    }
    : original(file, args, opts);
  if (preSeed) {
    preSeed(f);
    f.git(f.source, 'add', '.');
    f.git(f.source, 'commit', '-qm', 'Seed pre-existing files');
    f.git(f.source, 'update-ref', 'refs/remotes/origin/main', f.git(f.source, 'rev-parse', 'HEAD'));
  }
  const started = await startRun({
    name: 'feature',
    issue: '17',
    agent: 'codex',
    cwd: f.source,
    packageRoot,
    ...(through ? { through } : {}),
  }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  const run = f.record();
  f.run = run;
  f.done = async (step, summary = step, extra = {}) => {
    f.tick();
    const out = await stepDone({ step, summary, cwd: run.root, ...extra }, f.agentPorts());
    assert.equal(out.exitCode, 0, out.message);
    return out;
  };
  await f.done('understand');
  await f.done('visual', undefined, { skipped: 'no screen' });
  return f;
}

function writeHarborWork(f, { plainPrompt = false, boundary = false } = {}) {
  for (const dir of ['prompts', 'user_stories', 'tests']) mkdirSync(join(f.run.root, dir), { recursive: true });
  writeFileSync(join(f.run.root, PROMPT), plainPrompt ? plainMarkdownPromptText() : readFileSync(join(harbor, PROMPT), 'utf8'));
  cpSync(join(harbor, TEST), join(f.run.root, TEST));
  const boundaryBlock = boundary ? `\n\n\`\`\`pdd-boundary\n${PROMPT}\n\`\`\`` : '';
  writeFileSync(
    join(f.run.root, STORY),
    `${readFileSync(join(harbor, STORY), 'utf8').trimEnd()}${boundaryBlock}\n\n## Rules to check\n\n${RULE}\n\n## What must not change\n\n${KEEP}\n`,
  );
}

const approveStory = async (f, words = 'Yes, this matches.', extra = {}) => {
  f.tick();
  const out = await approveRun({ ref: '17', cwd: f.run.root, said: '-', ...extra }, said(f, words));
  assert.equal(out.exitCode, 0, out.message);
  return out;
};

function writeScenario(repo, name, promptPath) {
  writeFileSync(join(repo, `user_stories/${name}.md`), readFileSync(join(harbor, STORY), 'utf8'));
  const doc = JSON.parse(readFileSync(join(harbor, TEST), 'utf8'));
  doc.story_path = `user_stories/${name}.md`;
  doc.steps = doc.steps.map(step => ({ ...step, entry_path: promptPath }));
  mkdirSync(join(repo, 'tests'), { recursive: true });
  writeFileSync(join(repo, `tests/${name}.json`), JSON.stringify(doc, null, 2));
}

test('#3430-A: unrelated pre-existing Stories and tests do not block a scoped workflow run, while unscoped fullCheckPass still reports them', async t => {
  const f = await setupFeatureRun(t, {
    preSeed(fx) {
      for (const dir of ['prompts', 'user_stories', 'tests']) mkdirSync(join(fx.source, dir), { recursive: true });
      cpSync(join(harbor, PROMPT), join(fx.source, 'prompts/unrelated_billing.prompt.md'));
      writeScenario(fx.source, 'unrelated-billing', 'prompts/unrelated_billing.prompt.md');
      writeFileSync(
        join(fx.source, 'user_stories/untested-legacy.md'),
        '# Legacy Story\n\n## Acceptance criteria\n\n1. Keep legacy receipts.\n',
      );
    },
  });
  writeHarborWork(f);
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Add Harbor Story');
  await f.done('prompt-story');
  await approveStory(f);
  saveCheck(f);

  // Standalone unscoped fullCheckPass still checks the entire repository.
  const unscoped = fullCheckPass({ root: f.run.root }, { env: f.ports.env });
  assert.equal(unscoped.pass, false);
  assert.ok(unscoped.problems.some(p => p.kind === 'missing' && p.path === 'user_stories/untested-legacy.md'));
  assert.ok(unscoped.problems.some(p => p.kind === 'missing' && p.path === 'tests/unrelated-billing.json'));

  // Scoped workflow run ignores unrelated Stories and tests and opens PR 1 automatically.
  const out = await f.done('check');
  assert.equal(f.prs.length, 1, out.message);
  assert.equal(f.record().decisions.at(-1).via, 'automatic-check-pass');
});

test('#3430-A: consumer tests reaching a changed checkable prompt still block until checked, and unrelated broken tests fail open', async t => {
  const f = await setupFeatureRun(t, {
    preSeed(fx) {
      for (const dir of ['prompts', 'user_stories', 'tests']) mkdirSync(join(fx.source, dir), { recursive: true });
      cpSync(join(harbor, PROMPT), join(fx.source, PROMPT));
      // Consumer scenario whose dependency closure reaches PROMPT.
      storyTest(fx.source, 'consumer-order');
      // Unrelated broken scenario referencing a missing prompt outside the run.
      writeScenario(fx.source, 'broken-legacy', 'prompts/nonexistent_legacy.prompt.md');
    },
  });
  writeHarborWork(f);
  writeFileSync(
    join(f.run.root, PROMPT),
    readFileSync(join(f.run.root, PROMPT), 'utf8').replace('Return the order:', 'Return the priced order:'),
  );
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Update shared prompt and add new Story');
  await f.done('prompt-story');
  await approveStory(f);

  saveCheck(f, { tests: [TEST] });
  const blocked = await f.done('check');
  assert.equal(f.prs.length, 0, 'unchecked consumer reaching changed prompt must block');
  assert.match(blocked.message, /tests\/consumer-order\.json/);
  assert.doesNotMatch(blocked.message, /broken-legacy/, 'unrelated broken test must fail open');

  f.tick();
  saveCheck(f, { tests: ['tests/consumer-order.json'], criteria: { passed: 3, total: 3 } });
  const opened = await f.done('check');
  assert.equal(f.prs.length, 1, opened.message);

  // Direct scenario fallback when capture throws on a broken test that directly names a checkable prompt.
  const brokenConsumer = fullCheckPass({
    root: f.run.root,
    tests: [],
    stories: [],
    prompts: ['prompts/nonexistent_legacy.prompt.md'],
    scoped: true,
  }, { env: f.ports.env });
  assert.equal(brokenConsumer.pass, false);
  assert.ok(brokenConsumer.problems.some(p => p.path === 'tests/broken-legacy.json'));
});

test('#3430-B: mixed run with checkable prompt + valid kind: native-only prompt passes fullCheckPass and auto-opens PR 1', async t => {
  const f = await setupFeatureRun(t, { through: 'code' });
  writeHarborWork(f);
  writeFileSync(join(f.run.root, NATIVE_PROMPT), nativePromptText());
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Add checkable prompt, Story, and native-only leaf prompt');
  await f.done('prompt-story');
  await approveStory(f, 'Approve Story and native-only leaf.', { through: 'code' });

  saveCheck(f, { tests: [TEST] });
  const out = await f.done('check');
  assert.equal(f.prs.length, 1, out.message);
  assert.doesNotMatch(out.message, /prompt-not-checked/);
  assert.equal(f.record().decisions.find(d => d.stage === 'prompt-pr' && d.via === 'automatic-check-pass')?.via, 'automatic-check-pass');
  assert.equal(f.record().areas[f.record().area].name, 'code');
});

test('#3430-B: malformed kind: native-only prompt with blank reason never bypasses checks', async t => {
  const f = await setupFeatureRun(t);
  writeHarborWork(f);
  writeFileSync(join(f.run.root, NATIVE_PROMPT), nativePromptText());
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Add valid native-only prompt for Story approval');
  await f.done('prompt-story');
  await approveStory(f);

  // Corrupt the native-only frontmatter reason during the check step.
  writeFileSync(join(f.run.root, NATIVE_PROMPT), nativePromptText('   '));
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Break native-only reason');

  saveCheck(f, { tests: [TEST] });
  const out = await f.done('check');
  assert.equal(f.prs.length, 0, 'malformed native-only prompt must block automatic PR 1');
  assert.match(out.message, /Not passed \(prompt-not-checked\): prompts\/fsync_store\.prompt\.md:.*\/reason/);
});

test('#3430-B: pure kind: native-only 0-Story run reaches approve-pr cleanly without false errors and opens PR 1 on human approval', async t => {
  for (const variant of ['story-approved', 'prompt-edited', 'no-story-approval']) {
    const f = await setupFeatureRun(t, {
      preSeed(fx) {
        mkdirSync(join(fx.source, 'user_stories'), { recursive: true });
        writeFileSync(
          join(fx.source, 'user_stories/existing-untested.md'),
          '# Existing Untested Story\n\n## Acceptance criteria\n\n1. Unrelated criterion.\n',
        );
      },
    });
    mkdirSync(join(f.run.root, 'prompts'), { recursive: true });
    writeFileSync(join(f.run.root, NATIVE_PROMPT), nativePromptText());
    f.git(f.run.root, 'add', '.');
    f.git(f.run.root, 'commit', '-qm', 'Add pure native-only prompt');
    await f.done('prompt-story');
    await approveStory(f);

    if (variant === 'no-story-approval') {
      const r = f.record();
      delete r.storyApproval;
      writeRun(r);
    } else if (variant === 'prompt-edited') {
      writeFileSync(
        join(f.run.root, NATIVE_PROMPT),
        nativePromptText(NATIVE_REASON, 'Persist durability records atomically and fsync parent directory.'),
      );
      f.git(f.run.root, 'add', '.');
      f.git(f.run.root, 'commit', '-qm', 'Refine native-only prompt');
    }

    const out = await f.done('check', 'Deterministic node --test durability suite passed');
    if (!f.record().done.try) await f.done('try', 'skip try', { skipped: 'native-only module' });
    assert.equal(f.prs.length, 0, `pure native-only must wait for person approval (${variant})`);
    assert.doesNotMatch(out.message, /prompt-not-checked|Not passed/);
    assert.match(out.message, /Native-only prompt: prompts\/fsync_store\.prompt\.md/);
    assert.equal(f.record().gate?.kind, 'approve-pr');
    assert.equal(f.record().gate?.nativeOnly?.[0]?.path, NATIVE_PROMPT);

    f.herdr.idle();
    const statusJson = JSON.parse((await runStatus({ cwd: f.source, json: true }, f.ports)).message).runs[0];
    assert.doesNotMatch(statusJson.words, /agent must finish the prompt check/);
    assert.match(statusJson.words, /waiting for you: approve to open PR 1/);
    const detailOut = await runStatus({ ref: '17', cwd: f.source }, f.ports);
    assert.doesNotMatch(detailOut.message, /agent must finish the prompt check/);

    const approved = await approveRun(
      { ref: '17', cwd: f.run.root, through: 'code', said: '-' },
      said(f, 'Native-only reason is valid; open PR 1 and start code.'),
    );
    assert.equal(approved.exitCode, 0, approved.message);
    assert.equal(f.prs.length, 1, `PR 1 must open (${variant})`);
    assert.match(f.prs[0].body, /not-applicable \(native-only\): prompts\/fsync_store\.prompt\.md/);
    assert.equal(f.record().areas[f.record().area].name, 'code', `code area must start (${variant})`);
  }
});

test('#3430-B: automatic continuation holds pure native-only runs for person approval instead of auto-publishing', async t => {
  const origin = {
    repository: 'example/project',
    coordinatorId: 'coordinator-a',
    machine: 'machine-a',
    claim: { commentId: '11', labelEventId: '12' },
  };
  const f = await setupFeatureRun(t);
  mkdirSync(join(f.run.root, 'prompts'), { recursive: true });
  writeFileSync(join(f.run.root, NATIVE_PROMPT), nativePromptText());
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Native-only prompt');
  await f.done('prompt-story');
  await approveStory(f);
  await f.done('check');
  assert.equal(f.record().gate?.kind, 'approve-pr');

  const skill = join(f.base, 'skill');
  mkdirSync(join(skill, 'steps'), { recursive: true });
  writeFileSync(join(skill, 'steps/autopilot.md'), 'Synthetic scoped delegation fixture.\n');
  const run = f.record();
  run.skillDir = skill;
  run.automaticOrigin = structuredClone(origin);
  writeRun(run);
  const root = realpathSync(f.source);
  const stateRoot = join(f.state, 'autopilot');
  mkdirSync(stateRoot, { recursive: true });
  writeFileSync(
    join(stateRoot, `${createHash('sha256').update(root).digest('hex').slice(0, 20)}.json`),
    JSON.stringify({
      repo: run.repo,
      cwd: root,
      coordinatorId: origin.coordinatorId,
      machine: origin.machine,
      enabled: true,
      startAction: { command: 'pdd autopilot start', repository: run.repo, mode: 'auto' },
    }),
  );
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const fixturePath = join(f.base, 'reader.json');
  writeFileSync(fixturePath, JSON.stringify({
    labels: ['pdd:working'],
    events: [{ id: 12, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' } }],
    comments: [{
      id: 11,
      user: { login: 'example' },
      body: JSON.stringify({
        repository: origin.repository,
        coordinatorId: origin.coordinatorId,
        machine: origin.machine,
        labelEventId: '12',
      }),
    }],
  }));
  const exec = promisify(callbackExec);
  const original = f.ports.execFile;
  const execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === '--include'
    ? exec(process.execPath, [join(packageRoot, 'test/helpers/continuation-fake-gh.mjs'), ...args], {
      ...opts,
      env: { ...process.env, READER_FIXTURE_FILE: fixturePath, READER_GH_LOG: join(f.base, 'gh.log') },
    })
    : original(file, args, opts);

  const held = await advanceAutomaticPr1(
    { ref: '17', cwd: f.source, coordinatorId: origin.coordinatorId, machine: origin.machine, packageRoot },
    { ...f.agentPorts(), execFile, autopilotStateRoot: stateRoot },
  );
  assert.equal(held.exitCode, 0, held.message);
  assert.match(held.message, /PR 1 waits: native-only prompts require a person approval/);
  assert.match(f.record().gate?.automaticHold ?? '', /native-only prompts require a person approval/);
  assert.equal(f.prs.length, 0);
});

test('#3430-B: Story with acceptance criteria and 0 scenario tests never bypasses checks via a kind: native-only prompt', async t => {
  const f = await setupFeatureRun(t);
  for (const dir of ['prompts', 'user_stories']) mkdirSync(join(f.run.root, dir), { recursive: true });
  writeFileSync(join(f.run.root, NATIVE_PROMPT), nativePromptText());
  writeFileSync(
    join(f.run.root, STORY),
    `${readFileSync(join(harbor, STORY), 'utf8').trimEnd()}\n\n## Rules to check\n\n${RULE}\n\n## What must not change\n\n${KEEP}\n`,
  );
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Add Story with criteria and native-only prompt without scenario test');
  await f.done('prompt-story');
  await approveStory(f);

  const checkOut = await f.done('check');
  assert.equal(f.prs.length, 0, 'untested Story with criteria must never auto-open PR 1');
  assert.equal(f.record().gate?.nativeOnly, undefined, 'run with untested Story criteria must not be treated as pure native-only');
  assert.match(checkOut.message, /Not passed \(missing\): user_stories\/place-order\.md: Story has no scenario test for its criteria/);

  // Reopening the Story card and reapproving it must also refuse to treat the run as pure native-only!
  writeFileSync(
    join(f.run.root, STORY),
    readFileSync(join(f.run.root, STORY), 'utf8').replace('900 cents', '925 cents'),
  );
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Revise Story criterion');
  const reopened = await f.done('check');
  assert.ok(f.record().gate?.storyChanges?.length, reopened.message);

  const reapproved = await approveRun({ ref: '17', cwd: f.run.root, said: '-' }, said(f, '925 cents is approved.'));
  assert.equal(reapproved.exitCode, 0, reapproved.message);
  assert.equal(f.prs.length, 0, 'reapproving a Story with 0 scenario tests must still wait on missing scenario check');
  assert.match(reapproved.message, /Not passed \(missing\): user_stories\/place-order\.md: Story has no scenario test for its criteria/);
  assert.equal(f.record().gate?.nativeOnly, undefined);
});

test('#3430-C & #3390: evidence-associate unlocks fullCheckPass and PR 1 pddResults for plain-Markdown pdd-boundary runs while enforcing per-batch workspace eligibility', async t => {
  const f = await setupFeatureRun(t, {
    preSeed(fx) {
      for (const dir of ['prompts', 'user_stories', 'tests']) mkdirSync(join(fx.source, dir), { recursive: true });
      cpSync(join(harbor, PROMPT), join(fx.source, 'prompts/extra_order.prompt.md'));
      writeScenario(fx.source, 'extra-order', 'prompts/extra_order.prompt.md');
    },
  });
  writeHarborWork(f, { plainPrompt: true, boundary: true });
  f.git(f.run.root, 'add', '.');
  f.git(f.run.root, 'commit', '-qm', 'Add plain-Markdown prompt with Story pdd-boundary');
  await f.done('prompt-story');
  await approveStory(f);

  // Clone the worktree to an external producer workspace where checks ran.
  const producer = join(f.base, 'associated-producer');
  const unassociated = join(f.base, 'unassociated-producer');
  f.git(f.base, 'clone', '-q', f.run.root, producer);
  f.git(f.base, 'clone', '-q', f.run.root, unassociated);

  // 1. Unassociated workspace batch does not satisfy fullCheckPass.
  f.tick();
  saveCheck(f, { batchRoot: producer, summaryRepo: producer });
  const beforeAssoc = await f.done('check');
  assert.equal(f.prs.length, 0);
  assert.match(beforeAssoc.message, /Not passed \(missing\)/);

  // Remove the pre-registration batch test by advancing to unregistered/invalid batch variants first.
  const fUnreg = await setupFeatureRun(t, {
    preSeed(fx) {
      for (const dir of ['prompts', 'user_stories', 'tests']) mkdirSync(join(fx.source, dir), { recursive: true });
      cpSync(join(harbor, PROMPT), join(fx.source, 'prompts/extra_order.prompt.md'));
      writeScenario(fx.source, 'extra-order', 'prompts/extra_order.prompt.md');
    },
  });
  writeHarborWork(fUnreg, { plainPrompt: true, boundary: true });
  fUnreg.git(fUnreg.run.root, 'add', '.');
  fUnreg.git(fUnreg.run.root, 'commit', '-qm', 'Add plain-Markdown prompt with Story pdd-boundary');
  await fUnreg.done('prompt-story');
  await approveStory(fUnreg);
  const producerUnreg = join(fUnreg.base, 'producer-unreg');
  fUnreg.git(fUnreg.base, 'clone', '-q', fUnreg.run.root, producerUnreg);
  assert.equal(
    (await associateEvidenceWorkspace({ ref: '17', workspace: producerUnreg, stage: 'current', tests: [TEST], cwd: fUnreg.run.root }, fUnreg.ports)).exitCode,
    0,
  );

  // 2a. Unregistered test selection ([TEST, 'tests/extra-order.json'] when only [TEST] was associated) is rejected!
  fUnreg.tick();
  saveCheck(fUnreg, { batchRoot: producerUnreg, summaryRepo: producerUnreg, tests: [TEST, 'tests/extra-order.json'] });
  // 2b. Foreign runId in batch.association is rejected!
  fUnreg.tick();
  saveCheck(fUnreg, { batchRoot: producerUnreg, summaryRepo: producerUnreg, tests: [TEST], runId: 'foreign-run-id', stage: 'current' });
  // 2c. Historical stage: 'pr1' and stage: 'before' batches (both in producer and same-root) are rejected!
  fUnreg.tick();
  saveCheck(fUnreg, { batchRoot: producerUnreg, summaryRepo: producerUnreg, tests: [TEST], runId: fUnreg.run.runId, stage: 'pr1' });
  fUnreg.tick();
  saveCheck(fUnreg, { batchRoot: fUnreg.run.root, summaryRepo: fUnreg.run.root, tests: [TEST], runId: fUnreg.run.runId, stage: 'pr1' });
  fUnreg.tick();
  saveCheck(fUnreg, { batchRoot: producerUnreg, summaryRepo: producerUnreg, tests: [TEST], runId: fUnreg.run.runId, stage: 'before' });
  const rejectedOut = await fUnreg.done('check');
  assert.equal(fUnreg.prs.length, 0, 'unregistered selection, foreign runId, pr1 stage, and before stage must all be rejected');
  assert.match(rejectedOut.message, /Not passed \(missing\): tests\/place-order\.json/);

  // Also verify direct ports.workspace returning stage: 'pr1' is rejected by fullCheckPass.
  const pr1Check = fullCheckPass(
    { root: fUnreg.run.root, tests: [TEST], stories: [STORY], prompts: [PROMPT], scoped: true },
    {
      env: fUnreg.ports.env,
      workspace: () => ({ state: 'eligible', reason: null, stage: 'pr1', producerRoot: realpathSync(producerUnreg), tests: [TEST] }),
    },
  );
  assert.equal(pr1Check.pass, false);

  // 3. Register producer on `f` via associateEvidenceWorkspace (stage: 'current') — recaptures plain-Markdown prompt cleanly!
  const associated = await associateEvidenceWorkspace(
    { ref: '17', workspace: producer, stage: 'current', tests: [TEST], cwd: f.run.root },
    f.ports,
  );
  assert.equal(associated.exitCode, 0, associated.message);

  // Mismatched summary.repo is rejected as unavailable.
  f.tick();
  saveCheck(f, { batchRoot: producer, summaryRepo: unassociated });
  const mismatchedOut = await f.done('check');
  assert.equal(f.prs.length, 0);
  assert.match(mismatchedOut.message, /Not passed \(unavailable\)/);

  // 4. Valid current-stage associated batch passes fullCheckPass, records current pddResults, and opens PR 1 without pdd:no-verdict!
  f.tick();
  saveCheck(f, { batchRoot: producer, summaryRepo: producer });
  const opened = await f.done('check');
  assert.equal(f.prs.length, 1, opened.message);
  assert.equal(f.record().decisions.at(-1).via, 'automatic-check-pass');
  assert.ok(f.record().done.check.pddResults.length > 0, 'done.check.pddResults must include the associated check batch');
  assert.equal(f.record().done.check.pddResults[0].source, 'current');
  assert.match(f.prs[0].body, /Prompt tests \(place-order\): ✓ 3 of 3 criteria/);
  assert.doesNotMatch(f.prs[0].body, /pdd:no-verdict/);
});

test('#3430: 3-prompt real-repo layout (Runtime Story prompt + native-only module + plain-Markdown unreferenced module) passes with and without pdd-workspace.json', async t => {
  for (const withWorkspace of [false, true]) {
    const f = await setupFeatureRun(t, {
      preSeed: withWorkspace
        ? fx => { writeFileSync(join(fx.source, 'pdd-workspace.json'), `${JSON.stringify({ allowed_paths: ['runtime/'] }, null, 2)}\n`); }
        : undefined,
    });
    const rtPrompt = 'runtime/prompts/order-review.prompt.md';
    const rtStory = 'runtime/user_stories/order-review.md';
    const rtTest = 'runtime/tests/order-review.json';
    const nativeMod = 'prompts/modules/auth/key_check.prompt.md';
    const plainMod = 'prompts/modules/auth/session.prompt.md';

    for (const dir of ['runtime/prompts', 'runtime/user_stories', 'runtime/tests', 'prompts/modules/auth']) {
      mkdirSync(join(f.run.root, dir), { recursive: true });
    }
    writeFileSync(join(f.run.root, rtPrompt), readFileSync(join(harbor, PROMPT), 'utf8'));
    writeFileSync(
      join(f.run.root, rtStory),
      `${readFileSync(join(harbor, STORY), 'utf8').trimEnd()}\n\n## Rules to check\n\n${RULE}\n\n## What must not change\n\n${KEEP}\n`,
    );
    const doc = JSON.parse(readFileSync(join(harbor, TEST), 'utf8'));
    doc.story_path = rtStory;
    doc.steps = doc.steps.map(step => ({ ...step, entry_path: rtPrompt }));
    writeFileSync(join(f.run.root, rtTest), JSON.stringify(doc, null, 2));
    writeFileSync(join(f.run.root, nativeMod), nativePromptText('Constant-time HMAC key verification primitive with 0 Runtime Stories.'));
    writeFileSync(
      join(f.run.root, plainMod),
      '# Session state\n\nOwn `src/auth/session.mjs`.\n\n## Domain decisions\n\n- Parse and format internal session records.\n\n## Dependencies\n\nNone.\n',
    );

    f.git(f.run.root, 'add', '.');
    f.git(f.run.root, 'commit', '-qm', 'Add runtime Story prompt, native-only module, and plain-Markdown module');
    await f.done('prompt-story');
    await approveStory(f);

    saveCheck(f, { tests: [rtTest] });
    const out = await f.done('check');
    assert.equal(f.prs.length, 1, `expected PR 1 to open (withWorkspace=${withWorkspace}): ${out.message}`);
    assert.doesNotMatch(out.message, /prompt-not-checked|Not passed/);
    assert.equal(f.record().decisions.at(-1).via, 'automatic-check-pass');
    assert.match(f.prs[0].body, /Prompt tests \(order-review\): ✓ 3 of 3 criteria/);
    assert.doesNotMatch(f.prs[0].body, /pdd:no-verdict/);
  }
});

test('#3430: pure native-only prompt outside pdd-workspace.json allowed_paths reaches approve-pr cleanly while malformed frontmatter still blocks, and negative controls hold for plain-Markdown prompts', async t => {
  // 1. Pure native-only prompt outside pdd-workspace.json allowed_paths + malformed reason check.
  const fNative = await setupFeatureRun(t, {
    preSeed(fx) {
      writeFileSync(join(fx.source, 'pdd-workspace.json'), `${JSON.stringify({ allowed_paths: ['runtime/'] }, null, 2)}\n`);
    },
  });
  const nativeMod = 'prompts/modules/auth/key_check.prompt.md';
  mkdirSync(join(fNative.run.root, 'prompts/modules/auth'), { recursive: true });
  writeFileSync(join(fNative.run.root, nativeMod), nativePromptText());
  fNative.git(fNative.run.root, 'add', '.');
  fNative.git(fNative.run.root, 'commit', '-qm', 'Add out-of-workspace native-only prompt');
  await fNative.done('prompt-story');
  await approveStory(fNative);

  // Corrupt reason outside allowed_paths -> still blocks!
  writeFileSync(join(fNative.run.root, nativeMod), nativePromptText('   '));
  fNative.git(fNative.run.root, 'add', '.');
  fNative.git(fNative.run.root, 'commit', '-qm', 'Blank native-only reason');
  const badNative = await fNative.done('check');
  assert.equal(fNative.prs.length, 0);
  assert.match(badNative.message, /Not passed \(prompt-not-checked\): prompts\/modules\/auth\/key_check\.prompt\.md:.*\/reason/);

  // Restore valid reason -> reaches approve-pr as pure native-only and opens PR 1 with not-applicable (native-only)!
  writeFileSync(join(fNative.run.root, nativeMod), nativePromptText());
  fNative.git(fNative.run.root, 'add', '.');
  fNative.git(fNative.run.root, 'commit', '-qm', 'Restore valid native-only reason');
  const cleanNative = await fNative.done('check');
  assert.doesNotMatch(cleanNative.message, /Not passed/);
  assert.match(cleanNative.message, /Native-only prompt: prompts\/modules\/auth\/key_check\.prompt\.md/);
  assert.equal(fNative.record().gate?.nativeOnly?.[0]?.path, nativeMod);
  const approvedNative = await approveRun({ ref: '17', cwd: fNative.run.root, said: '-' }, said(fNative, 'Approve native-only module.'));
  assert.equal(approvedNative.exitCode, 0, approvedNative.message);
  assert.equal(fNative.prs.length, 1);
  assert.match(fNative.prs[0].body, /not-applicable \(native-only\): prompts\/modules\/auth\/key_check\.prompt\.md/);
  assert.doesNotMatch(fNative.prs[0].body, /pdd:no-verdict/);

  // 2. Negative control A: unchecked prompt WITH an embedded Runtime interface block still blocks with prompt-not-checked!
  const fIface = await setupFeatureRun(t);
  writeHarborWork(fIface);
  cpSync(join(harbor, PROMPT), join(fIface.run.root, 'prompts/unchecked_runtime.prompt.md'));
  fIface.git(fIface.run.root, 'add', '.');
  fIface.git(fIface.run.root, 'commit', '-qm', 'Add unchecked prompt with Runtime interface');
  await fIface.done('prompt-story');
  await approveStory(fIface);
  saveCheck(fIface, { tests: [TEST] });
  const blockedIface = await fIface.done('check');
  assert.equal(fIface.prs.length, 0, 'unchecked prompt with Runtime interface must block');
  assert.match(blockedIface.message, /Not passed \(prompt-not-checked\): prompts\/unchecked_runtime\.prompt\.md/);

  // 3. Negative control B: 0-test run with a plain-Markdown prompt (not kind: native-only) still blocks with prompt-not-checked!
  const fZero = await setupFeatureRun(t);
  mkdirSync(join(fZero.run.root, 'prompts/modules/auth'), { recursive: true });
  writeFileSync(
    join(fZero.run.root, 'prompts/modules/auth/session.prompt.md'),
    '# Session state\n\nOwn `src/auth/session.mjs`.\n\n## Domain decisions\n\n- Keep session tokens opaque.\n\n## Dependencies\n\nNone.\n',
  );
  fZero.git(fZero.run.root, 'add', '.');
  fZero.git(fZero.run.root, 'commit', '-qm', 'Add plain-Markdown prompt with 0 tests');
  await fZero.done('prompt-story');
  await approveStory(fZero);
  const blockedZero = await fZero.done('check');
  assert.equal(fZero.prs.length, 0, '0-test plain-Markdown prompt run must block');
  assert.equal(fZero.record().gate?.nativeOnly, undefined);
  assert.match(blockedZero.message, /Not passed \(prompt-not-checked\): prompts\/modules\/auth\/session\.prompt\.md/);
});

test('#3430-D: explicit human approve at approve-pr opens PR 1 after no-verdict instead of deadlocking, and honors saved --through code', async t => {
  for (const route of ['said', 'terminal']) {
    const f = await setupFeatureRun(t, { through: 'code' });
    writeHarborWork(f);
    f.git(f.run.root, 'add', '.');
    f.git(f.run.root, 'commit', '-qm', 'Story and prompt');
    await f.done('prompt-story');
    await approveStory(f, 'Approve Story and code.', { through: 'code' });

    // Simulate Runtime outage (no-verdict) leaving the run at approve-pr.
    saveCheck(f, { state: 'error', criteria: null });
    const checkOut = await f.done('check');
    assert.equal(f.prs.length, 0);
    assert.match(checkOut.message, /Not passed \(no-verdict\)/);
    assert.equal(f.record().gate?.kind, 'approve-pr');

    // Explicit human approval (--said or terminal) opens PR 1 without deadlocking and advances through code!
    f.tick();
    const approved = route === 'said'
      ? await approveRun({ ref: '17', cwd: f.run.root, said: '-' }, said(f, 'Runtime is down; open PR 1 and start code.'))
      : await approveRun({ ref: '17', cwd: f.source }, f.ports);
    assert.equal(approved.exitCode, 0, approved.message);
    assert.equal(f.prs.length, 1, `explicit human approve (${route}) at approve-pr must open PR 1`);
    assert.equal(f.record().areas[f.record().area].name, 'code', `code area must start (${route})`);
  }
});

test('#3430-D: explicit approve at approve-pr never approves unseen Story or expected-value edits and reopens the Story card', async t => {
  for (const timing of ['before-approve', 'during-confirm']) {
    const f = await setupFeatureRun(t);
    writeHarborWork(f);
    f.git(f.run.root, 'add', '.');
    f.git(f.run.root, 'commit', '-qm', 'Story and prompt');
    await f.done('prompt-story');
    await approveStory(f);

    // Move run to approve-pr without storyChanges (e.g., manual/native-only gate).
    const r = f.record();
    r.state = 'waiting';
    r.gate = { id: `gate-${timing}`, area: 'prompt-pr', at: f.clock, kind: 'approve-pr' };
    writeRun(r);

    const mutateStory = () => {
      writeFileSync(
        join(f.run.root, STORY),
        readFileSync(join(f.run.root, STORY), 'utf8').replace('900 cents', '975 cents'),
      );
      const doc = JSON.parse(readFileSync(join(f.run.root, TEST), 'utf8'));
      doc.steps[0].checks.find(c => c.path === '/totalCents').value = 975;
      writeFileSync(join(f.run.root, TEST), JSON.stringify(doc));
    };

    if (timing === 'before-approve') mutateStory();
    f.tick();
    const refused = await approveRun(
      { ref: '17', cwd: f.source },
      timing === 'during-confirm'
        ? { ...f.ports, confirm: async () => { mutateStory(); return true; } }
        : f.ports,
    );
    assert.equal(refused.exitCode, 1, `unseen Story change (${timing}) must be refused`);
    assert.equal(f.prs.length, 0, `PR 1 must not open on unseen Story change (${timing})`);
    assert.ok(f.record().gate?.storyChanges?.length, `Story gate must reopen (${timing})`);
    assert.notEqual(f.record().gate?.id, `gate-${timing}`);
    assert.ok(refused.message.includes(join(f.run.root, STORY)), 'refusal must show the updated Story card');
  }
});
