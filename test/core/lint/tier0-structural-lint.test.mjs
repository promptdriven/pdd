import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { validateSvgViewBox } from '../../../src/core/ui/svg-xml.mjs';
import { lintSvgLayouts } from '../../../src/core/ui/svg-layout.mjs';
import { collectMarkdownIntegrityFindings, collectOperationsTableIntegrityFindings, collectPromptDependencyFindings } from '../../../src/core/lint/prompt-rules.mjs';
import { collectAppMapWholeEventRefFindings } from '../../../src/core/ui/app-map-lint.mjs';
import { collectStoryUnboundCriteriaFindings } from '../../../src/core/lint/story-criteria-parity.mjs';
import { lintRepoProject } from '../../../src/core/lint/project-lint.mjs';
import { runLocalLint } from '../../../src/core/lint/run-local-lint.mjs';

function makeSink() {
  let text = '';
  return { write(s) { text += String(s); }, get text() { return text; } };
}

function initRepo(t, files = {}) {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-tier0-structural-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  mkdirSync(repo, { recursive: true });
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: repo });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: repo });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: repo });
  for (const [rel, content] of Object.entries(files)) {
    const abs = join(repo, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, typeof content === 'string' ? content : `${JSON.stringify(content, null, 2)}\n`);
  }
  execFileSync('git', ['add', '-A'], { cwd: repo });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: repo });
  return repo;
}

test('Improvement 1: finite & sane .ui.svg viewBox check catches bad dimensions/ratios and allows normal SVGs + complex CSS', t => {
  assert.equal(validateSvgViewBox('0 0 800 600'), null);
  assert.equal(validateSvgViewBox('-10 -10 400 300'), null);
  assert.match(validateSvgViewBox(''), /empty|4/);
  assert.match(validateSvgViewBox('0 0 100'), /4/);
  assert.match(validateSvgViewBox('0 0 NaN 100'), /finite|number/i);
  assert.match(validateSvgViewBox('0 0 Infinity 100'), /finite|number/i);
  assert.match(validateSvgViewBox('0 0 0 100'), /positive/i);
  assert.match(validateSvgViewBox('0 0 100 -20'), /positive/i);
  assert.match(validateSvgViewBox('0 0 3 55000000000'), /extreme|aspect ratio|magnitude/i);
  assert.match(validateSvgViewBox('0 0 10000 10'), /aspect ratio/i);
  assert.match(validateSvgViewBox('0 0 0.0001 0.0001'), /hairline|small|dimension/i);
  assert.match(validateSvgViewBox('0 0 5000000 5000000'), /extreme|magnitude|large/i);

  const repo = initRepo(t, {
    'prompts/bad.prompt.md': '# Bad UI\n\n![Bad](bad.ui.svg)\n\n## Dependencies\nNone.\n',
    'prompts/bad.ui.svg': '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 3 55000000000"><rect width="3" height="10"/></svg>\n',
    'prompts/good.prompt.md': '# Good UI\n\n![Good](good.ui.svg)\n\n## Dependencies\nNone.\n',
    'prompts/good.ui.svg': '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 360"><style>g.card > rect:first-child { fill: #fff; }</style><g class="card"><rect width="100" height="40"/></g></svg>\n',
  });
  const warnings = lintSvgLayouts({
    root: repo,
    files: ['prompts/bad.prompt.md', 'prompts/bad.ui.svg', 'prompts/good.prompt.md', 'prompts/good.ui.svg'],
  });
  assert.equal(warnings.length, 1, warnings.join('\n'));
  assert.match(warnings[0], /prompts\/bad\.prompt\.md -> prompts\/bad\.ui\.svg: viewBox:/);
});

test('Improvement 2: exact-case relative CommonMark link check catches missing targets and case mismatches while skipping code spans/fences/comments', t => {
  const repo = initRepo(t, {
    'docs/Guide.md': '# Guide\n',
    'prompts/Helper.prompt.md': '# Helper\n\n## Dependencies\nNone.\n',
    'prompts/main.prompt.md': [
      '# Main',
      '',
      'See [valid guide](../docs/Guide.md#intro) and [wrong case](../docs/guide.md) and [missing](../docs/ghost.md).',
      'Inline code `[ignored](../docs/no-such-inline.md)` and multi-line code span:',
      'Use `foo [also ignored](../docs/no-such-multiline.md)',
      'bar` safely.',
      '<!-- [comment ignored](../docs/no-such-comment.md) -->',
      '```markdown',
      '[fenced ignored](../docs/no-such-fence.md)',
      '```',
      '',
      '## Dependencies',
      '- [helper exact](Helper.prompt.md)',
      '- [helper wrong case](helper.prompt.md)',
    ].join('\n') + '\n',
  });

  const allFiles = ['docs/Guide.md', 'prompts/Helper.prompt.md', 'prompts/main.prompt.md'];
  const texts = new Map([
    ['prompts/main.prompt.md', readFileSync(join(repo, 'prompts/main.prompt.md'), 'utf8')],
    ['prompts/Helper.prompt.md', '# Helper\n\n## Dependencies\nNone.\n'],
  ]);
  const findings = collectPromptDependencyFindings({
    targetPrompts: ['prompts/main.prompt.md'],
    allVisibleFiles: allFiles,
    getPromptText: path => texts.get(path) ?? null,
    realRoot: repo,
  });

  const brokenDeps = findings.filter(f => f.code === 'broken-dependency-link');
  assert.equal(brokenDeps.length, 1, JSON.stringify(brokenDeps));
  assert.match(brokenDeps[0].detail, /actual path on disk is "prompts\/Helper\.prompt\.md"/);

  const brokenRels = findings.filter(f => f.code === 'broken-relative-link');
  assert.equal(brokenRels.length, 2, JSON.stringify(brokenRels));
  assert.ok(brokenRels.some(f => f.detail.includes('docs/guide.md') && f.detail.includes('actual path on disk is "docs/Guide.md"')));
  assert.ok(brokenRels.some(f => f.detail.includes('docs/ghost.md') && /does not exist|missing|not found|no such|broken/i.test(f.detail)));
  assert.equal(findings.some(f => f.detail.includes('no-such-')), false, 'code spans, fences, and comments must never false-positive');
});

test('Improvement 3: truncated Markdown fence and truncated pipe table row detector catches CLI timeouts without false positives on valid tables', t => {
  const unclosedFence = [
    '# Broken fence',
    '',
    '```json',
    '{ "ok": true',
  ].join('\n');
  const fenceFindings = collectMarkdownIntegrityFindings(unclosedFence, { path: 'prompts/cut.prompt.md', category: 'prompt structure' });
  assert.equal(fenceFindings.length, 1);
  assert.equal(fenceFindings[0].code, 'truncated-markdown-fence');
  assert.equal(fenceFindings[0].defaultSeverity, 'error');
  assert.equal(fenceFindings[0].line, 3);

  const truncatedTable = [
    '# Truncated table',
    '',
    '| Operation | Input | Output |',
    '| --- | --- | --- |',
    '| create | `{ id }` | `{ ok: true }` |',
    '| delete | `{ id }` | O',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  const tableFindings = collectMarkdownIntegrityFindings(truncatedTable, { path: 'prompts/cut-table.prompt.md', category: 'prompt structure' });
  assert.equal(tableFindings.length, 1, JSON.stringify(tableFindings));
  assert.equal(tableFindings[0].code, 'truncated-markdown-table');
  assert.equal(tableFindings[0].defaultSeverity, 'error');
  assert.equal(tableFindings[0].line, 6);

  const validTable = [
    '# Valid table',
    '',
    '| Operation | Pattern | Result |',
    '| --- | --- | --- |',
    '| match | `a \\| b` | `true` |',
    '| reset | `none` | `false` |',
    '',
    '```markdown',
    '| Ignored | Inside | Fence |',
    '| --- | --- | --- |',
    '| cut',
    '```',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  assert.deepEqual(collectMarkdownIntegrityFindings(validTable, { path: 'prompts/ok-table.prompt.md', category: 'prompt structure' }), []);

  const repo = initRepo(t, {
    'prompts/cut.prompt.md': unclosedFence + '\n',
    'user_stories/cut.md': '# Story\n\n## Acceptance criteria\n\n1. Shows table.\n\n| Col A | Col B |\n| --- | --- |\n| ok | cut\n',
  });
  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, false);
  assert.ok(report.findings.some(f => f.path === 'prompts/cut.prompt.md' && f.code === 'truncated-markdown-fence'));
  assert.ok(report.findings.some(f => f.path === 'user_stories/cut.md' && f.code === 'truncated-markdown-table'));
});

test('Improvement 4: story-criteria-parity populates byExplicitStory so non-stem scenarios linked via story_path are audited', t => {
  const repo = initRepo(t, {
    'user_stories/checkout.md': [
      '# Checkout',
      '',
      'As a buyer, I want checkout totals verified, so that charges stay exact.',
      '',
      '## Acceptance criteria',
      '',
      '1. Valid cart prints total.',
      '2. Empty cart prints error.',
    ].join('\n') + '\n',
    'tests/custom-alias.json': {
      schema_version: 'pdd.scenario.short.v1',
      story_path: 'user_stories/checkout.md',
      entry_path: 'prompts/checkout.prompt.md',
      steps: [{
        id: 's1',
        op: 'checkout',
        input: {},
        checks: { '1': [['result', '/ok', '=', true]] },
      }],
    },
  });

  const missingAc2 = collectStoryUnboundCriteriaFindings({
    realRoot: repo,
    scopedFiles: ['user_stories/checkout.md', 'tests/custom-alias.json'],
    storyPaths: ['user_stories/checkout.md'],
  });
  assert.equal(missingAc2.length, 1, JSON.stringify(missingAc2));
  assert.equal(missingAc2[0].code, 'story-unbound-criteria');
  assert.match(missingAc2[0].detail, /#2|criterion 2|2\b/i);
  assert.match(missingAc2[0].detail, /tests\/custom-alias\.json/);

  writeFileSync(
    join(repo, 'tests/custom-alias.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/checkout.md',
      criteria: [
        { id: 'AC1', text: 'Valid cart prints total.' },
        { id: 'AC2', text: 'Empty cart prints error.' },
      ],
      initial_world: {},
      steps: [{
        step_id: 's1',
        entry_path: 'prompts/checkout.prompt.md',
        operation: 'checkout',
        input: {},
        checks: [
          { criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', value: true },
          { criterion_id: 'AC2', target: 'result', path: '/err', op: 'equals', value: 'empty' },
        ],
      }],
    }, null, 2) + '\n',
  );
  const boundClean = collectStoryUnboundCriteriaFindings({
    realRoot: repo,
    scopedFiles: ['user_stories/checkout.md', 'tests/custom-alias.json'],
    storyPaths: ['user_stories/checkout.md'],
  });
  assert.deepEqual(boundClean, []);
});

test('Improvement 5: unmistakable 1-line offline summary reports exact validated artifact counts for OK and FAILED runs', t => {
  const repo = initRepo(t, {
    'prompts/app.prompt.md': '# App\n\n![Screen](app.ui.svg)\n\n## Dependencies\nNone.\n',
    'prompts/app.ui.svg': '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 200"><rect width="400" height="200"/></svg>\n',
    'user_stories/app.md': '# App story\n\nAs a visitor, I want the screen rendered.\n\n## Acceptance criteria\n\n1. Renders app.\n',
    'tests/app.json': {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/app.md',
      criteria: [{ id: 'AC1', text: 'Renders app.' }],
      initial_world: {},
      steps: [{ step_id: 's1', entry_path: 'prompts/app.prompt.md', operation: 'render', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', value: true }] }],
    },
    'app-map.json': {
      schema_version: 'prompt-runtime.app-map.v1',
      name: 'App',
      screens: [{ id: 'home', prompt_path: 'prompts/app.prompt.md' }],
    },
  });

  const out = makeSink(), err = makeSink();
  const code = runLocalLint({ cwd: repo }, { stdout: out, stderr: err });
  assert.equal(code, 0, err.text);
  assert.equal(err.text, '');
  assert.equal(
    out.text,
    'Lint OK: 1 prompt(s), 2 story/scenario(s), 1 app-map(s), 1 drawing(s) validated offline (0 errors, 0 warnings)\n',
  );

  writeFileSync(join(repo, 'prompts/app.prompt.md'), '# App\n\n```json\n{"cut": true\n');
  const failOut = makeSink(), failErr = makeSink();
  const failCode = runLocalLint({ cwd: repo }, { stdout: failOut, stderr: failErr });
  assert.equal(failCode, 1);
  assert.match(failErr.text, /\[truncated-markdown-fence\]/);
  assert.match(failOut.text, /Lint FAILED: 1 prompt\(s\), 2 story\/scenario\(s\), 1 app-map\(s\), 0 drawing\(s\) validated offline \(1 error, 0 warnings\)/);
});

test('Wave 2 Check 1 (#3648): app-map-whole-event-ref fails closed on {"$ref": "/event"} and allows specific /event/* field pointers', t => {
  const repo = initRepo(t, {
    'prompts/game.prompt.md': '# Game\n\n## Dependencies\nNone.\n',
    'app-map.json': {
      schema_version: 'prompt-runtime.app-map.v1',
      name: 'Snake',
      initial_screen: 'game',
      screens: [{ id: 'game', prompt_path: 'prompts/game.prompt.md', operation: 'render', source: 'operation', format: 'html', input: {}, result_pointer: '/html' }],
      handlers: [{
        id: 'primary-click',
        screen: 'game',
        kind: 'region',
        match: { region_id: 'primary' },
        handler: { prompt_path: 'prompts/game.prompt.md', operation: 'transition' },
        input: { state: { $ref: '/state' }, event: { $ref: '/event' } },
        state: {},
        next: { kind: 'stay' },
      }],
    },
  });

  const direct = collectAppMapWholeEventRefFindings({
    appMapPaths: ['app-map.json'],
    readFile: rel => readFileSync(join(repo, rel), 'utf8'),
  });
  assert.equal(direct.length, 1);
  assert.equal(direct[0].code, 'app-map-whole-event-ref');
  assert.equal(direct[0].defaultSeverity, 'error');
  assert.match(direct[0].detail, /whole-event.*\$ref.*\/event/);
  assert.match(direct[0].fix, /\/event\/value.*\/event\/key/);

  const out = makeSink(), err = makeSink();
  assert.equal(runLocalLint({ cwd: repo }, { stdout: out, stderr: err }), 1);
  assert.match(err.text, /app-map\.json:1 \[app-map-whole-event-ref\]/);

  // Replacing {"$ref": "/event"} with {"$ref": "/event/value"} clears the error cleanly.
  writeFileSync(
    join(repo, 'app-map.json'),
    readFileSync(join(repo, 'app-map.json'), 'utf8').replace('"$ref": "/event"', '"$ref": "/event/value"'),
  );
  const okOut = makeSink(), okErr = makeSink();
  assert.equal(runLocalLint({ cwd: repo }, { stdout: okOut, stderr: okErr }), 0, okErr.text);
  assert.equal(okErr.text, '');
});

test('Wave 2 Check 2 (#3725): prompt-level checkable -> native-only layering inversion caught without needing a scenario', t => {
  const repo = initRepo(t, {
    'prompts/ledger/state.prompt.md': '---\nkind: native-only\nreason: Opens SQLite database transaction.\n---\n\n# Ledger state\n\n## Dependencies\nNone.\n',
    'prompts/ledger/posting.prompt.md': '# Ledger posting\n\nPost issuances.\n\n## Dependencies\n- [Ledger state](state.prompt.md)\n',
    'prompts/ledger/adapter.prompt.md': '---\nkind: native-only\nreason: Thin DB adapter.\n---\n\n# Ledger adapter\n\n## Dependencies\n- [Ledger posting](posting.prompt.md)\n',
  });

  const report = lintRepoProject({ root: repo });
  const inv = report.findings.filter(f => f.code === 'inverted-native-only-dependency');
  assert.equal(inv.length, 1, JSON.stringify(inv));
  assert.equal(inv[0].path, 'prompts/ledger/posting.prompt.md');
  assert.match(inv[0].message, /prompts\/ledger\/state\.prompt\.md/);
  assert.match(inv[0].message, /native-only/);
  assert.match(inv[0].message, /layering inversion/i);
  // Reverse direction (native-only adapter -> checkable posting) must NOT warn.
  assert.equal(inv.some(f => f.path === 'prompts/ledger/adapter.prompt.md'), false);
});

test('Wave 2 Check 3 (#3725): inline Markdown relative-link cycles caught while ignoring ## Caller navigation', t => {
  const repo = initRepo(t, {
    'prompts/continuity/intake.prompt.md': '# Intake\n\n## Ports\n- For the Document shape see [review](intake-review.prompt.md).\n\n## Dependencies\nNone.\n',
    'prompts/continuity/intake-review.prompt.md': '# Intake review\n\n## Dependencies\n- [Intake](intake.prompt.md)\n',
    'prompts/leaf.prompt.md': '# Leaf\n\n## Dependencies\nNone.\n\n## Caller navigation\nUsed by [Caller](caller.prompt.md).\n',
    'prompts/caller.prompt.md': '# Caller\n\n## Dependencies\n- [Leaf](leaf.prompt.md)\n',
  });

  const report = lintRepoProject({ root: repo });
  const cycles = report.findings.filter(f => f.code === 'prompt-dependency-cycle');
  assert.equal(cycles.length, 1, JSON.stringify(cycles));
  assert.match(cycles[0].message, /intake\.prompt\.md/);
  assert.match(cycles[0].message, /intake-review\.prompt\.md/);
  // Leaf <-> Caller only links back inside ## Caller navigation, so it must NOT trigger a cycle.
  assert.equal(cycles.some(f => f.message.includes('leaf.prompt.md')), false);
});

test('Wave 2 Check 4 (#3661): malformed Operations Calls/Error-codes trailing parenthetical prose fails closed while clean cells pass', t => {
  const badDelivery = [
    '# Reply delivery',
    '',
    '## Operations',
    '',
    '| Operation | Input | Output | Error codes |',
    '|---|---|---|---|',
    '| `label` | `status` | `control` | None (unknown inputs fail closed with `control: null`, `keepDraft: true`) |',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  const badCallsCol = [
    '# Ledger',
    '',
    '## Operations and ports',
    '',
    '| Operation | Calls |',
    '|---|---|',
    '| `post` | `store.save` (persists to disk) |',
    '| `read` | None (pure lookup) |',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  const cleanDelivery = [
    '# Reply delivery',
    '',
    '## Operations',
    '',
    '| Operation | Input | Output | Error codes | Calls |',
    '|---|---|---|---|---|',
    '| `label` | `status` (text) | `control` (text) | None | None |',
    '| `sync` | `id` (text) | `ok` (boolean) | `unavailable` | `store.load`, `ports.atomic_operation()` |',
    '',
    '',
    '- Calls: `ports.call("release.verify", {"id": inp["id"]})`.',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');

  const f1 = collectOperationsTableIntegrityFindings(badDelivery, { path: 'prompts/delivery.prompt.md' });
  assert.equal(f1.length, 1, JSON.stringify(f1));
  assert.equal(f1[0].code, 'prompt-malformed-operations-cell');
  assert.equal(f1[0].defaultSeverity, 'error');
  assert.equal(f1[0].line, 7);
  assert.match(f1[0].detail, /parenthetical prose/i);

  const f2 = collectOperationsTableIntegrityFindings(badCallsCol, { path: 'prompts/ledger.prompt.md' });
  assert.equal(f2.length, 2, JSON.stringify(f2));

  assert.deepEqual(collectOperationsTableIntegrityFindings(cleanDelivery, { path: 'prompts/clean.prompt.md' }), []);
});
