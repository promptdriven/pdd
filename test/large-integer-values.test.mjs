import './helpers/test-home.mjs';
// Whole numbers above 2^53 in Runtime scenario files: Story cards, fingerprints and replay anchors keep exact digits.
import assert from 'node:assert/strict';
import test from 'node:test';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fingerprintChanges, storyCard, storyFingerprint } from '../src/workflow-story-card.mjs';
import { formatReplayEvidence, pinReplayVectors, readReplayEvidence } from '../src/workflow-replay.mjs';

const ABOVE = '9007199254740993', ROUNDED = '9007199254740992', LARGE = '4250129834582680692326400';
const STORY = 'user_stories/format-duration.md', TEST = 'tests/format-duration.json', PROMPT = 'prompts/duration.prompt.md';
const CRITERIA = ['A duration of 3600 x 2^70 seconds shows its exact whole hours.', 'A duration just above 2^53 seconds is refused.'];

// The test file text: `seconds` values are written as raw JSON tokens, never through a Number.
function scenarioText({ large = LARGE, above = ABOVE, expected = ABOVE } = {}) {
  return `{
  "schema_version": "prompt-runtime.program-scenario.v1",
  "story_path": "${STORY}",
  "criteria": [{"id": "AC1", "text": "${CRITERIA[0]}"}, {"id": "AC2", "text": "${CRITERIA[1]}"}],
  "initial_world": {}, "simulation": {}, "context": [],
  "steps": [
    {"step_id": "large", "entry_path": "${PROMPT}", "operation": "formatDuration", "input": {"seconds": ${large}},
     "checks": [{"criterion_id": "AC1", "target": "result", "path": "/hours", "op": "equals", "value": 1180591620717411303424}]},
    {"step_id": "above", "entry_path": "${PROMPT}", "operation": "formatDuration", "input": {"seconds": ${above}},
     "checks": [{"criterion_id": "AC2", "target": "result", "path": "/seconds", "op": "equals", "value": ${expected}}]}
  ]
}
`;
}
const promptText = maximum => `# Duration

Show whole hours for a duration in seconds.

## Dependencies

None.

<details>
<summary>Runtime interface</summary>

\`\`\`json
{"status":"draft","prose_sha256":"","entries":[{"operation":"formatDuration","input_schema":{"type":"object","properties":{"seconds":{"type":"integer","minimum":0,"maximum":${maximum}}},"required":["seconds"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"hours":{"type":"integer"},"seconds":{"type":"integer"}},"required":[],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":2,"max_model_calls":2},"conventions":[]}
\`\`\`

</details>
`;

function repo(t, { scenario = scenarioText(), maximum = '1e30' } = {}) {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-large-integers-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  for (const dir of ['prompts', 'tests', 'user_stories']) mkdirSync(join(root, dir));
  writeFileSync(join(root, STORY), `# Format duration\n\nAs a reader, I want exact hours, so that large durations keep their digits.\n\n## Acceptance criteria\n\n1. ${CRITERIA[0]}\n2. ${CRITERIA[1]}\n`);
  writeFileSync(join(root, PROMPT), promptText(maximum));
  writeFileSync(join(root, TEST), scenario);
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
  git('init', '-q'); git('add', '.');
  git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture');
  return { root, git, write: text => writeFileSync(join(root, TEST), text) };
}
const card = root => storyCard({ run: { repo: 'example/project', number: 19, issue: { title: 'Large durations' } }, root, changed: [STORY, TEST] });

test('LI1: the Story card shows the exact digits that the test file holds', t => {
  const f = repo(t), text = card(f.root);
  assert.ok(text.includes(`{"seconds":${LARGE}}`), text);
  assert.ok(text.includes(`{"seconds":${ABOVE}}`), text);
  assert.ok(text.includes(`AC2 /seconds equals ${ABOVE}`), text);
  assert.ok(!text.includes('e+24') && !text.includes(`{"seconds":${ROUNDED}}`), 'no rounded value is shown to the person');
});

test('LI2: a change in the last digit above 2^53 is a changed expected value', t => {
  const f = repo(t), saved = storyFingerprint({ root: f.root, changed: [STORY, TEST] });
  f.write(scenarioText({ expected: ROUNDED }));
  const changes = fingerprintChanges(saved, storyFingerprint({ root: f.root, changed: [STORY, TEST] }));
  assert.deepEqual(changes, [`Test changed: ${TEST}`, `  case above: expected was AC2 /seconds equals ${ABOVE}; now AC2 /seconds equals ${ROUNDED}`]);
  // An input-only change is not an expected-value change, at any size.
  const again = storyFingerprint({ root: f.root, changed: [STORY, TEST] });
  f.write(scenarioText({ expected: ROUNDED, above: '9007199254740995' }));
  assert.deepEqual(fingerprintChanges(again, storyFingerprint({ root: f.root, changed: [STORY, TEST] })), []);
});

test('LI3: the saved replay anchor keeps exact digits and reports a last-digit change', t => {
  const f = repo(t), anchor = pinReplayVectors(f.root, [TEST]);
  assert.equal(anchor.outcome, undefined, anchor.reason);
  assert.deepEqual(anchor.vectors[0].exact_integers.map(row => row.value), [LARGE, '1180591620717411303424', ABOVE, ABOVE]);
  // status.json is plain JSON: the anchor survives a save and a read.
  const saved = JSON.parse(JSON.stringify(anchor));
  assert.equal(saved.vectors[0].snapshot.steps[1].checks[0].value, Number(ROUNDED), 'the ordinary snapshot keeps its JSON value');
  f.write(scenarioText({ expected: ROUNDED }));
  const runDir = join(f.root, '.run'); mkdirSync(runDir);
  const result = readReplayEvidence({ root: f.root, runDir, runId: 'synthetic', replayBaseline: saved });
  const changed = result.warnings.filter(row => row.path);
  assert.equal(changed.length, 1, JSON.stringify(result.warnings));
  assert.equal(changed[0].path, '/steps/1/checks/0/value');
  assert.deepEqual(changed[0].exact, { before: ABOVE, after: ROUNDED });
  assert.ok(!result.warnings.some(row => /JSON values unchanged/.test(row.reason ?? '')));
  assert.doesNotThrow(() => JSON.stringify(result), 'the saved warnings stay plain JSON');
  const report = formatReplayEvidence(result).replaceAll('&#47;', '/');
  assert.ok(report.includes(`${ABOVE} -> ${ROUNDED}`), report);
  // An anchor of a vector without large numbers has no new field.
  const small = repo(t, { scenario: scenarioText({ large: '7200', above: '90000', expected: '90000' }).replace('1180591620717411303424', '2') });
  assert.equal(Object.hasOwn(pinReplayVectors(small.root, [TEST]).vectors[0], 'exact_integers'), false);
});
