import './helpers/test-home.mjs';
// Whole numbers above 2^53 in Runtime scenario files: pdd shows, checks, saves, compares and sends their exact digits.
import assert from 'node:assert/strict';
import test from 'node:test';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { captureSource, checkInput, fillHashes, findTests, preflight, readPrompt } from '../src/runtime-preflight.mjs';
import { parseScenarioJson } from '../src/scenario-json.mjs';
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

test('LI4: local preflight refuses what the interpreter refuses today, with a clear exact message', t => {
  const rows = root => { fillHashes({ root }); const found = findTests({ root }); return preflight({ root, found, selected: found.tests }); };
  // Plain digits outside the range: the interpreter's code and section, and the exact Number spelling that works today.
  let f = repo(t), result = rows(f.root), refusals = result.rows[0].refusals;
  assert.equal(refusals.length, 1, JSON.stringify(refusals));
  assert.deepEqual({ code: refusals[0].code, section: refusals[0].section, step: refusals[0].step },
    { code: 'scenario-integer-out-of-range', section: 'steps[0].input.seconds', step: 1 });
  assert.equal(refusals[0].message, `steps[0].input.seconds is ${LARGE}, outside the PDD interpreter's integer range -9007199254740991 through 9007199254740991. `
    + 'pdd keeps the exact digits, but the interpreter cannot check this test yet (nothing sent, 0 AI calls). '
    + 'If the parameter takes a Number, write its exact Number spelling 4.2501298345826807e+24; the interpreter accepts it. '
    + "Check the exact value in the repository's own vector test (RUNBOOK §17); do not change the input type or the expected value to fit the interpreter.");
  // 2^53 + 1 has no exact Number: no spelling is offered.
  f = repo(t, { scenario: scenarioText({ large: '4.2501298345826807e+24' }).replace('1180591620717411303424', '1.1805916207174113e+21') });
  refusals = rows(f.root).rows[0].refusals;
  assert.equal(refusals[0].section, 'steps[1].input.seconds');
  assert.ok(refusals[0].message.includes(`is ${ABOVE},`) && refusals[0].message.includes('No JavaScript Number holds this value.'), refusals[0].message);
  // The exact Number spellings that the interpreter admitted in a real lint pass the local check too.
  f = repo(t, { scenario: scenarioText({ large: '4.2501298345826807e+24', above: '4.2501298345826807e+24', expected: '1.1805916207174113e+21' }).replace('1180591620717411303424', '1.1805916207174113e+21') });
  result = rows(f.root);
  assert.deepEqual(result.rows[0].refusals, []);
  assert.deepEqual(result.warnings.filter(line => /reads as the Number/.test(line)), []);
});

test('LI6: a token that loses digits is a warning, and a schema bound outside the range is refused locally', t => {
  const rows = root => { fillHashes({ root }); const found = findTests({ root }); return preflight({ root, found, selected: found.tests }); };
  let f = repo(t, { scenario: scenarioText({ large: '7200', above: '9007199254740993.0', expected: '90000' }).replace('1180591620717411303424', '2') });
  let result = rows(f.root);
  assert.deepEqual(result.rows[0].refusals, []);
  assert.ok(result.warnings.includes(`Warning: ${TEST} steps[1].input.seconds is 9007199254740993.0, which reads as the Number 9007199254740992. Write the value you mean: plain digits for an exact whole number, or the exact Number spelling.`), result.warnings.join('\n'));
  f = repo(t, { maximum: ROUNDED, scenario: scenarioText({ large: '7200', above: '90000', expected: '90000' }).replace('1180591620717411303424', '2') });
  const refusals = rows(f.root).rows[0].refusals;
  assert.equal(refusals.length, 1, JSON.stringify(refusals));
  assert.equal(refusals[0].code, 'graph-schema-invalid');
  assert.equal(refusals[0].message, `${PROMPT} /entries/0/input_schema/properties/seconds/maximum is ${ROUNDED}, outside the PDD interpreter's integer range -9007199254740991 through 9007199254740991 (bound_text ${ROUNDED}).`);
});

test('LI7: P9 compares an exact input with an exact schema bound', t => {
  // A schema read with its own tokens: 2^53 + 1 is above a maximum of 2^53, although JSON.parse rounds both alike.
  const f = repo(t, { maximum: ROUNDED });
  const found = findTests({ root: f.root }), prompt = readPrompt(f.root, found.visible, PROMPT), schema = prompt.interface.entries[0].input_schema;
  const input = parseScenarioJson(`{"seconds": ${ABOVE}}`);
  assert.deepEqual(checkInput(input, schema, 1).refusals.map(row => row.message), [`steps[1] input /seconds is ${ABOVE}. The prompt allows 0 to ${ROUNDED}.`]);
  assert.deepEqual(checkInput(parseScenarioJson(`{"seconds": ${ROUNDED}}`), schema, 1).refusals, []);
  assert.deepEqual(checkInput(parseScenarioJson(`{"seconds": ${LARGE}}`), { ...schema, properties: { seconds: { type: 'integer', minimum: 0 } } }, 0).refusals, []);
  // The bound token decides: a maximum of 2^53 + 1 admits 2^53 + 1, although its Number is 2^53.
  const above = repo(t, { maximum: ABOVE });
  const exactBound = readPrompt(above.root, findTests({ root: above.root }).visible, PROMPT).interface.entries[0].input_schema;
  assert.deepEqual(checkInput(input, exactBound, 1).refusals, []);
  assert.equal(checkInput(parseScenarioJson('{"seconds": 9007199254740995}'), exactBound, 1).refusals.length, 1);
});

test('LI8: P9 reads const and enum objects with their own tokens at every depth', t => {
  const BIG = '12345678901234567890', OTHER = '12345678901234567891';
  const object = extra => `{"type":"object","properties":{"o":{"type":"object","properties":{"id":{"type":"integer"}},"required":["id"],"additionalProperties":false,${extra}}},"required":["o"],"additionalProperties":false}`;
  for (const [label, schemaText] of [['nested const', object(`"const":{"id":${BIG}}`)], ['enum of objects', object(`"enum":[{"id":1},{"id":${BIG}}]`)]]) {
    const f = repo(t);
    writeFileSync(join(f.root, PROMPT), promptText('1e30').replace(/"input_schema":\{[\s\S]*?\},"result_schema"/, `"input_schema":${schemaText},"result_schema"`));
    const schema = readPrompt(f.root, findTests({ root: f.root }).visible, PROMPT).interface.entries[0].input_schema;
    // The same value as the schema: no refusal, as JSON.parse on both sides also gives (the behavior of main stays).
    assert.deepEqual(checkInput(parseScenarioJson(`{"o":{"id":${BIG}}}`), schema, 0).refusals, [], label);
    // A different last digit is a difference, and the message shows exact digits.
    const refused = checkInput(parseScenarioJson(`{"o":{"id":${OTHER}}}`), schema, 0).refusals;
    assert.equal(refused.length, 1, label);
    assert.ok(refused[0].message.includes(OTHER) && refused[0].message.includes(BIG) && !refused[0].message.includes('12345678901234567000'), refused[0].message);
  }
});

test('LI5: an upload rewrite keeps exact digits in the bytes that pdd sends', t => {
  // A Story criterion that the test does not check makes pdd rewrite the uploaded test with check exemptions.
  const f = repo(t);
  writeFileSync(join(f.root, STORY), readFileSync(join(f.root, STORY), 'utf8') + '3. The display never uses scientific notation.\n');
  f.git('add', '.');
  const captured = captureSource(f.root, { tests: [TEST], appMap: null });
  const sent = captured.sources.find(file => file.path === TEST).bytes.toString('utf8');
  assert.ok(sent.includes('check_exemptions'), 'the test was rewritten for upload');
  for (const digits of [LARGE, ABOVE, '1180591620717411303424']) assert.ok(sent.includes(digits), `${digits} is sent exactly`);
  assert.ok(!sent.includes('e+'), sent);
});
