import '../helpers/test-home.mjs';
// Whole numbers above 2^53 in Runtime scenario files: preflight, P9, source capture and check runs keep exact digits.
import assert from 'node:assert/strict';
import test from 'node:test';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { checkInput, interfaceBlocks, proseSha256 } from '../../src/runtime/runtime-preflight.mjs';
import { parseScenarioJson, roundedNumberTokens } from '../../src/runtime/scenario-json.mjs';
import { captureSource, fillHashes, findTests, preflight, readPrompt, runCheck } from '../../src/runtime-seam.mjs';
import { harbor, PLACE, sink } from './runtime-fake.mjs';

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

test('LI4: local preflight warns about what the interpreter refuses today, and still sends the test', t => {
  const rows = root => { fillHashes({ root }); const found = findTests({ root }); return preflight({ root, found, selected: found.tests }); };
  const range = result => result.warnings.filter(line => line.includes('scenario-integer-out-of-range'));
  // Plain digits outside the range: no local refusal; one warning with the interpreter's code, section and the spelling that works.
  let f = repo(t), result = rows(f.root);
  assert.deepEqual(result.rows[0].refusals, []);
  assert.deepEqual(range(result), [`Warning: ${TEST} scenario-integer-out-of-range: steps[0].input.seconds is ${LARGE}, outside the PDD interpreter's integer range -9007199254740991 through 9007199254740991, so the interpreter refuses this test before execution (0 AI calls). `
    + 'If the parameter takes a Number, write its exact Number spelling 4.2501298345826807e+24; the interpreter accepts it. '
    + "Check the exact value in the repository's own vector test (RUNBOOK §17); do not change the input type or the expected value to fit the interpreter."]);
  // 2^53 + 1 has no exact Number: no spelling is offered.
  f = repo(t, { scenario: scenarioText({ large: '4.2501298345826807e+24' }).replace('1180591620717411303424', '1.1805916207174113e+21') });
  result = rows(f.root);
  assert.deepEqual(result.rows[0].refusals, []);
  assert.equal(range(result).length, 1);
  assert.ok(range(result)[0].includes(`steps[1].input.seconds is ${ABOVE},`) && range(result)[0].includes('No JavaScript Number holds this value.'), range(result)[0]);
  // The exact Number spellings that the interpreter admitted in a real lint give no range warning.
  f = repo(t, { scenario: scenarioText({ large: '4.2501298345826807e+24', above: '4.2501298345826807e+24', expected: '1.1805916207174113e+21' }).replace('1180591620717411303424', '1.1805916207174113e+21') });
  result = rows(f.root);
  assert.deepEqual(result.rows[0].refusals, []);
  assert.deepEqual(range(result), []);
  assert.deepEqual(result.warnings.filter(line => /reads as the Number/.test(line)), []);
});

test('LI6: a token that loses digits and a schema bound outside the range are warnings, never refusals', t => {
  const rows = root => { fillHashes({ root }); const found = findTests({ root }); return preflight({ root, found, selected: found.tests }); };
  let f = repo(t, { scenario: scenarioText({ large: '7200', above: '9007199254740993.0', expected: '90000' }).replace('1180591620717411303424', '2') });
  let result = rows(f.root);
  assert.deepEqual(result.rows[0].refusals, []);
  assert.ok(result.warnings.includes(`Warning: ${TEST} steps[1].input.seconds is 9007199254740993.0, which reads as the Number 9007199254740992. Write the value you mean: plain digits for an exact whole number, or the exact Number spelling.`), result.warnings.join('\n'));
  f = repo(t, { maximum: ROUNDED, scenario: scenarioText({ large: '7200', above: '90000', expected: '90000' }).replace('1180591620717411303424', '2') });
  result = rows(f.root);
  assert.deepEqual(result.rows[0].refusals, []);
  assert.deepEqual(result.warnings.filter(line => line.includes('graph-schema-invalid')),
    [`Warning: ${PROMPT} /entries/0/input_schema/properties/seconds/maximum is ${ROUNDED}, outside the PDD interpreter's integer range -9007199254740991 through 9007199254740991, so the interpreter refuses this bound (graph-schema-invalid, bound_text ${ROUNDED}).`]);
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

test('LI9: with no local range refusal, a test equal to a nested const above 2^53 passes local preflight', t => {
  const BIG = '12345678901234567890', f = repo(t);
  const schema = `{"type":"object","properties":{"seconds":{"type":"integer"},"o":{"type":"object","properties":{"id":{"type":"integer"}},"required":["id"],"additionalProperties":false,"const":{"id":${BIG}}}},"required":["seconds","o"],"additionalProperties":false}`;
  writeFileSync(join(f.root, PROMPT), promptText('1e30').replace(/"input_schema":\{[\s\S]*?\},"result_schema"/, `"input_schema":${schema},"result_schema"`));
  const one = id => scenarioText().replaceAll(/"input": \{"seconds": ([^}]*)\}/g, `"input": {"seconds": $1, "o": {"id": ${id}}}`);
  const run = text => { f.write(text); fillHashes({ root: f.root }); const found = findTests({ root: f.root }); return preflight({ root: f.root, found, selected: found.tests }).rows[0].refusals; };
  assert.deepEqual(run(one(BIG)), []);
  const refused = run(one('12345678901234567891'));
  assert.equal(refused.length, 2);
  assert.ok(refused.every(row => row.code === 'invalid-input' && row.message.includes(BIG) && !row.message.includes('12345678901234567000')), JSON.stringify(refused));
});

test('LI10: a native-only test with a whole number above 2^53 keeps the state and text it has without one', async t => {
  // Probe p7: the test is never sent to the interpreter, so no number advice may change what pdd reports.
  const report = async big => {
    const setup = harbor(t, repo => {
      const file = join(repo, PLACE), old = readFileSync(file, 'utf8'), block = interfaceBlocks(old)[0];
      let text = old.replace(block[0], `<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({ status: 'draft', prose_sha256: '', kind: 'native-only', reason: 'Exact BigInt arithmetic is checked by the repository vector test.' })}\n\`\`\`\n</details>`);
      writeFileSync(file, text.replace('"prose_sha256":""', `"prose_sha256":"${proseSha256(text)}"`));
      if (big) { const test = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(test, 'utf8')); doc.initial_world.big = '__BIG__'; writeFileSync(test, JSON.stringify(doc, null, 2).replace('"__BIG__"', LARGE)); }
    });
    const out = { stdout: sink(), stderr: sink(), env: { HOME: setup.home, PDD_RUNTIME_STATE_DIR: setup.state }, gh() { throw Error('must not sign in'); } };
    const exitCode = await runCheck({ cwd: setup.repo, options: { '--json': true } }, out), result = JSON.parse(out.stdout.text);
    assert.equal(readFileSync(join(setup.repo, 'tests/place-order.json'), 'utf8').includes(LARGE), big);
    return { exitCode, warnings: result.warnings, rows: result.rows.map(row => ({ test: row.test, state: row.state, reason: row.reason ?? null, refusals: row.refusals ?? null })),
      summary: result.summary_line, stderr: out.stderr.text };
  };
  const plain = await report(false), large = await report(true);
  assert.equal(large.rows[0].state, 'not run');
  assert.equal(large.rows[0].reason.code, 'native-only');
  assert.deepEqual(large, plain);
});

test('T02 (#3150 advice): for 2^53 <= n < 1e21 the advice offers an exponent spelling that reads back as n and that today\'s refusal rule admits', async t => {
  const { exactNumberSpelling } = await import('../../src/runtime/runtime-preflight.mjs');
  // Today's interpreter rule (prompt_runtime/program_scenario.py _validate_scenario_integers): an integer literal (no
  // fraction, no exponent) outside +-(2^53 - 1) is refused; a token with a fraction or exponent is a float and passes.
  const refusedToday = token => /^-?(?:0|[1-9][0-9]*)$/.test(token) && (BigInt(token) > 2n ** 53n - 1n || BigInt(token) < -(2n ** 53n - 1n));
  for (const n of [2 ** 53, 2 ** 60, 2 ** 69, 1e20, 999999999999999900000, 1e21, 2 ** 80, Number(LARGE), -(2 ** 60)]) {
    const spelling = exactNumberSpelling(n);
    assert.ok(spelling, `a spelling for ${n}`);
    assert.equal(Number(spelling), n, `${spelling} reads back as ${n}`);
    assert.equal(refusedToday(spelling), false, `${spelling} is admitted today`);
    assert.match(spelling, /e/, 'never plain digits');
    assert.deepEqual(roundedNumberTokens(`{"v": ${spelling}}`), [], `${spelling} gives no rounding warning`);
  }
  assert.equal(exactNumberSpelling(2 ** 60), '1.152921504606847e+18');
  assert.equal(String(2 ** 60), '1152921504606847000', 'the old advice: plain digits, refused today');
  assert.equal(refusedToday(String(2 ** 60)), true);
  // The warning itself offers the exponent spelling for 2^60.
  const two60 = '1152921504606846976';
  const f = repo(t, { scenario: scenarioText({ large: two60 }) });
  fillHashes({ root: f.root }); const found = findTests({ root: f.root });
  const warning = preflight({ root: f.root, found, selected: found.tests }).warnings.find(line => line.includes(`steps[0].input.seconds is ${two60},`));
  assert.ok(warning?.includes('write its exact Number spelling 1.152921504606847e+18;'), warning);
  assert.doesNotMatch(warning, /spelling 1152921504606847000/);
});
