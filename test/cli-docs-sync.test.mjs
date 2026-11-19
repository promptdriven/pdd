import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  CLI_DOCS_END_MARKER,
  CLI_DOCS_GROUP_ORDER,
  CLI_DOCS_NOTICE,
  CLI_DOCS_START_MARKER,
  checkCliDocs,
  renderCommandTables,
  syncCliDocs,
} from '../src/cli-docs-sync.mjs';
import { compileScenarioText } from '../src/scenario-compile.mjs';
import { runSyncCliDocsCli } from '../scripts/sync-cli-docs.mjs';

function pointerValue(root, pointer) {
  if (!pointer || pointer === '/') return root;
  const parts = pointer.slice(1).split('/').map(p => p.replaceAll('~1', '/').replaceAll('~0', '~'));
  let current = root;
  for (const part of parts) {
    current = current?.[part];
  }
  return current;
}

function createBufferStream() {
  let text = '';
  return {
    write(chunk) {
      text += String(chunk);
    },
    toString() {
      return text;
    },
  };
}

test('cli-docs-sync replays all 12 runtime scenario vectors against native code', () => {
  const scenarioRaw = readFileSync(new URL('./runtime/cli-docs-sync.json', import.meta.url), 'utf8');
  const storyText = readFileSync(new URL('../user_stories/cli-docs-sync.md', import.meta.url), 'utf8');
  const compiled = compileScenarioText(scenarioRaw, {
    path: 'test/runtime/cli-docs-sync.json',
    storySource: storyText,
    storyPath: 'user_stories/cli-docs-sync.md',
  });
  assert.equal(compiled.refusal, null);
  const steps = compiled.doc.steps;
  const ops = { syncCliDocs, checkCliDocs, renderCommandTables };

  assert.equal(steps.length, 12);

  for (const step of steps) {
    const fn = ops[step.operation];
    assert.equal(typeof fn, 'function', `Unknown operation ${step.operation}`);
    let result = null;
    let error = null;
    try {
      result = fn(step.input);
    } catch (err) {
      error = { code: err?.code ?? '', message: err?.message ?? String(err) };
    }

    const expectsError = step.checks.some(c => c.target === 'error') || Boolean(step.expected_error);
    if (expectsError) {
      assert.ok(error, `${step.step_id}: expected error but got result`);
      if (step.expected_error) {
        assert.equal(error.code, step.expected_error, `${step.step_id}: wrong error code`);
      }
    } else {
      assert.equal(error, null, `${step.step_id}: unexpected error ${error?.code}: ${error?.message}`);
    }

    for (const check of step.checks) {
      const target = check.target === 'error' ? error : result;
      const actual = pointerValue(target, check.path);
      if (check.op === 'equals') {
        assert.deepEqual(actual, check.value, `${step.step_id} ${check.path}`);
      } else if (check.op === 'contains') {
        assert.equal(typeof actual, 'string', `${step.step_id} ${check.path} should be string`);
        assert.ok(actual.includes(check.value), `${step.step_id} ${check.path} should contain ${check.value}`);
      } else if (check.op === 'not_contains') {
        assert.equal(typeof actual, 'string', `${step.step_id} ${check.path} should be string`);
        assert.ok(!actual.includes(check.value), `${step.step_id} ${check.path} should not contain ${check.value}`);
      } else {
        assert.fail(`Unhandled check op ${check.op} in ${step.step_id}`);
      }
    }
  }
});

test('renderCommandTables orders all 5 canonical groups, appends custom groups, and cleans descriptions', () => {
  const routes = [
    { id: 'custom.z', group: '  Extensions  ', forms: [{ form: 'pdd ext z', description: 'Run\tcustom\x07\x00ext.' }] },
    { id: 'metrics.stages', forms: [{ form: 'pdd metrics stages', description: '   \n\t  ' }] },
    { id: 'workflow.run', forms: [{ form: 'pdd workflow run NAME ISSUE', description: 'Run\r\nworkflow | fast.' }] },
    { id: 'autopilot.status', forms: [{ form: 'pdd autopilot status', description: 'Show status.' }] },
    { id: 'accounts', forms: [{ form: 'pdd accounts', description: 'List accounts.' }] },
    { id: 'setup', group: '   ', forms: [{ form: '  pdd setup [--yes]  ', description: 'Setup repo.' }] },
    { id: 'graph', forms: [{ form: 'pdd graph', description: 'Show graph.' }] },
    { id: 'dependencies.prepare', forms: [{ form: 'pdd dependencies prepare', description: 'Prepare packet.' }] },
    { id: 'version.detailed', forms: [{ form: 'pdd -VV', description: 'Show version.' }] },
    { id: 'empty.route', forms: [] },
  ];

  const snapshot = structuredClone(routes);
  const rendered = renderCommandTables({ routes });

  assert.deepEqual(routes, snapshot, 'renderCommandTables must not mutate caller routes');
  assert.equal(rendered.formCount, 9);
  assert.deepEqual(rendered.groups, [...CLI_DOCS_GROUP_ORDER, 'Extensions']);
  assert.deepEqual(Object.keys(rendered).sort(), ['formCount', 'groups', 'markdown']);
  assert.ok(rendered.markdown.startsWith(`${CLI_DOCS_NOTICE}\n\n### Core PDD workflow\n`));
  assert.ok(rendered.markdown.includes('| `pdd setup [--yes]` | Setup repo. |'));
  assert.ok(rendered.markdown.includes('| `pdd workflow run NAME ISSUE` | Run workflow \\| fast. |'));
  assert.ok(rendered.markdown.includes('| `pdd metrics stages` | - |'));
  assert.ok(rendered.markdown.includes('| `pdd ext z` | Run customext. |'));
  assert.ok(rendered.markdown.indexOf('### Workflows & product') < rendered.markdown.indexOf('### Autopilot'));
  assert.ok(rendered.markdown.indexOf('pdd workflow run NAME ISSUE') < rendered.markdown.indexOf('pdd graph'));
  assert.ok(rendered.markdown.indexOf('pdd graph') < rendered.markdown.indexOf('pdd dependencies prepare'));
});

test('renderCommandTables handles empty route sets with notice only', () => {
  const rendered = renderCommandTables({ routes: [{ id: 'noop', forms: [] }] });
  assert.deepEqual(rendered, {
    markdown: CLI_DOCS_NOTICE,
    formCount: 0,
    groups: [],
  });

  const doc = `# CLI\n${CLI_DOCS_START_MARKER}\nold\n${CLI_DOCS_END_MARKER}`;
  const synced = syncCliDocs({ document: doc, routes: [] });
  assert.equal(synced.document, `# CLI\n${CLI_DOCS_START_MARKER}\n${CLI_DOCS_NOTICE}\n${CLI_DOCS_END_MARKER}`);
  assert.equal(checkCliDocs({ document: synced.document, routes: [] }).status, 'current');
});

test('renderCommandTables refuses malformed routes and duplicate forms with invalid-route', () => {
  const badInputs = [
    null,
    { routes: 'not-an-array' },
    { routes: [{ id: '   ', forms: [] }] },
    { routes: [{ id: 'setup', group: 42, forms: [] }] },
    { routes: [{ id: 'setup', forms: 'nope' }] },
    { routes: [{ id: 'setup', forms: [{ form: '   ', description: 'x' }] }] },
    { routes: [{ id: 'setup', forms: [{ form: 'pdd setup\n', description: 'x' }] }] },
    { routes: [{ id: 'setup', forms: [{ form: 'pdd `setup`', description: 'x' }] }] },
    { routes: [{ id: 'setup', forms: [{ form: 'pdd setup', description: null }] }] },
    {
      routes: [
        { id: 'a', forms: [{ form: 'pdd setup', description: 'one' }] },
        { id: 'b', forms: [{ form: '  pdd setup  ', description: 'two' }] },
      ],
    },
  ];

  for (const input of badInputs) {
    assert.throws(() => renderCommandTables(input), err => err?.code === 'invalid-route');
  }
});

test('syncCliDocs and checkCliDocs preserve CRLF, trailing spaces on markers, and EOF without newline', () => {
  const routes = [{ id: 'setup', forms: [{ form: 'pdd setup', description: 'Setup repo.' }] }];
  const doc = [
    '# CLI',
    `${CLI_DOCS_START_MARKER}   `,
    'stale',
    `${CLI_DOCS_END_MARKER}\t`,
    'Footer without trailing newline',
  ].join('\r\n');

  const synced = syncCliDocs({ document: doc, routes });
  assert.equal(synced.changed, true);
  assert.ok(synced.document.includes('\r\n'));
  assert.ok(synced.document.startsWith(`# CLI\r\n${CLI_DOCS_START_MARKER}   \r\n`));
  assert.ok(synced.document.endsWith(`${CLI_DOCS_END_MARKER}\t\r\nFooter without trailing newline`));
  assert.equal(checkCliDocs({ document: synced.document, routes }).status, 'current');
});

test('checkCliDocs reports stale on description-only drift with empty missing/extra lists', () => {
  const routes = [{ id: 'setup', forms: [{ form: 'pdd setup', description: 'Updated text.' }] }];
  const synced = syncCliDocs({
    document: `${CLI_DOCS_START_MARKER}\n${CLI_DOCS_END_MARKER}\n`,
    routes: [{ id: 'setup', forms: [{ form: 'pdd setup', description: 'Old text.' }] }],
  });

  const checked = checkCliDocs({ document: synced.document, routes });
  assert.deepEqual(checked, {
    ok: false,
    status: 'stale',
    missingForms: [],
    extraForms: [],
    formCount: 1,
  });
});

test('guard precedence enforces invalid-route, markers, prose-conflict (including diff3 base), then inside conflict', () => {
  const validRoutes = [{ id: 'setup', forms: [{ form: 'pdd setup', description: 'Setup.' }] }];

  assert.throws(
    () => syncCliDocs({ document: 'no markers', routes: [{ id: '', forms: [] }] }),
    err => err?.code === 'invalid-route',
  );

  // Conflict both outside and inside markers must still report prose-conflict even with allowInsideConflicts: true.
  const mixedConflict = [
    '||||||| base',
    CLI_DOCS_START_MARKER,
    '<<<<<<< HEAD',
    '=======',
    '>>>>>>> branch',
    CLI_DOCS_END_MARKER,
  ].join('\n');
  assert.throws(
    () => syncCliDocs({ document: mixedConflict, routes: validRoutes, allowInsideConflicts: true }),
    err => err?.code === 'prose-conflict',
  );
  assert.throws(
    () => checkCliDocs({ document: mixedConflict, routes: validRoutes }),
    err => err?.code === 'prose-conflict',
  );

  // Conflict marker strictly after end marker is also prose-conflict.
  const trailingConflict = `${CLI_DOCS_START_MARKER}\n${CLI_DOCS_END_MARKER}\n>>>>>>> branch\n`;
  assert.throws(
    () => syncCliDocs({ document: trailingConflict, routes: validRoutes, allowInsideConflicts: true }),
    err => err?.code === 'prose-conflict',
  );
});

test('runSyncCliDocsCli supports --help, --check, --write, --resolve-conflicts, and refuses unsafe states', () => {
  const routes = [{ id: 'setup', forms: [{ form: 'pdd setup', description: 'Setup repo.' }] }];
  const staleDoc = `# CLI\n\n${CLI_DOCS_START_MARKER}\n| \`pdd old\` | Old |\n${CLI_DOCS_END_MARKER}\n`;
  const conflictDoc = `# CLI\n\n${CLI_DOCS_START_MARKER}\n<<<<<<< HEAD\n| \`pdd old\` | A |\n=======\n| \`pdd old\` | B |\n>>>>>>> feat\n${CLI_DOCS_END_MARKER}\n`;
  const proseConflictDoc = `<<<<<<< HEAD\n# A\n=======\n# B\n>>>>>>> feat\n${CLI_DOCS_START_MARKER}\n${CLI_DOCS_END_MARKER}\n`;

  // --help
  {
    const stdout = createBufferStream();
    const stderr = createBufferStream();
    assert.equal(runSyncCliDocsCli(['--help'], { stdout, stderr, routes }), 0);
    assert.match(stdout.toString(), /--resolve-conflicts/);
    assert.equal(stderr.toString(), '');
  }

  // Bad option combinations
  {
    const stderr = createBufferStream();
    assert.equal(runSyncCliDocsCli(['--check', '--write'], { stderr, routes }), 2);
    assert.equal(runSyncCliDocsCli(['--resolve-conflicts'], { stderr, routes }), 2);
    assert.equal(runSyncCliDocsCli(['--bogus'], { stderr, routes }), 2);
    assert.equal(runSyncCliDocsCli(['--file'], { stderr, routes }), 2);
  }

  // Real temp file write -> idempotent write -> check
  const dir = mkdtempSync(join(tmpdir(), 'pdd-cli-docs-sync-'));
  try {
    const file = join(dir, 'cli.md');
    writeFileSync(file, staleDoc, 'utf8');

    const checkStaleErr = createBufferStream();
    assert.equal(runSyncCliDocsCli(['--check', '--file', file], { stderr: checkStaleErr, routes }), 1);
    assert.match(checkStaleErr.toString(), /missing 1: pdd setup/);
    assert.match(checkStaleErr.toString(), /extra 1: pdd old/);

    const writeOut = createBufferStream();
    assert.equal(runSyncCliDocsCli(['--write', '--file', file], { stdout: writeOut, routes }), 0);
    assert.match(writeOut.toString(), /Updated CLI reference tables/);

    let writeCalls = 0;
    const currentText = readFileSync(file, 'utf8');
    const noopOut = createBufferStream();
    assert.equal(
      runSyncCliDocsCli(['--write', '--file', file], {
        stdout: noopOut,
        routes,
        readFile: () => currentText,
        writeFile: () => { writeCalls += 1; },
      }),
      0,
    );
    assert.equal(writeCalls, 0);
    assert.match(noopOut.toString(), /already current/);

    const checkOkOut = createBufferStream();
    assert.equal(runSyncCliDocsCli(['--check', '--file', file], { stdout: checkOkOut, routes }), 0);
    assert.match(checkOkOut.toString(), /current \(1 forms\)/);

    // Inside conflict: default --write refuses without writing; --write --resolve-conflicts succeeds.
    writeFileSync(file, conflictDoc, 'utf8');
    const conflictErr = createBufferStream();
    assert.equal(runSyncCliDocsCli(['--write', '--file', file], { stderr: conflictErr, routes }), 1);
    assert.match(conflictErr.toString(), /--resolve-conflicts/);
    assert.equal(readFileSync(file, 'utf8'), conflictDoc);

    const resolveOut = createBufferStream();
    assert.equal(runSyncCliDocsCli(['--write', '--resolve-conflicts', '--file', file], { stdout: resolveOut, routes }), 0);
    assert.match(resolveOut.toString(), /resolved generated-block conflicts/);
    assert.equal(runSyncCliDocsCli(['--check', '--file', file], { stdout: createBufferStream(), routes }), 0);

    // Prose conflict: refused with exit 2 even with --resolve-conflicts, leaving file untouched.
    writeFileSync(file, proseConflictDoc, 'utf8');
    const proseErr = createBufferStream();
    assert.equal(runSyncCliDocsCli(['--write', '--resolve-conflicts', '--file', file], { stderr: proseErr, routes }), 2);
    assert.match(proseErr.toString(), /\[prose-conflict\]/);
    assert.equal(readFileSync(file, 'utf8'), proseConflictDoc);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
