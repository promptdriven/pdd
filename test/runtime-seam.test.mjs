import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import { join, posix } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('..', import.meta.url));

function walk(dir, prefix = dir) {
  const entries = readdirSync(join(root, dir), { withFileTypes: true });
  const out = [];
  for (const entry of entries) {
    const rel = posix.join(prefix, entry.name);
    if (entry.isDirectory()) out.push(...walk(rel, rel));
    else if (entry.isFile()) out.push(rel);
  }
  return out.sort();
}

// Extract string and template-chunk literals while skipping JS comments and regex literals.
function stringLiterals(source) {
  const out = [];
  const stack = [];
  let i = 0;
  let prev = '';
  const regexAllowed = () => !prev || ['(', ',', '=', ':', '[', '!', '&', '|', '?', '{', '}', ';', '+', '-', '*', '%', '<', '>', '^', '~', 'return', 'throw', 'case', 'in', 'of', 'typeof', 'void', 'delete', 'await', 'yield'].includes(prev);

  const lineAt = index => source.slice(0, index).split('\n').length;

  while (i < source.length) {
    const c = source[i];
    const next = source[i + 1];
    if (c === '/' && next === '/') {
      const end = source.indexOf('\n', i + 2);
      i = end < 0 ? source.length : end + 1;
      continue;
    }
    if (c === '/' && next === '*') {
      const end = source.indexOf('*/', i + 2);
      i = end < 0 ? source.length : end + 2;
      continue;
    }
    if (c === "'" || c === '"') {
      const start = i;
      let j = i + 1;
      let value = '';
      while (j < source.length && source[j] !== c) {
        if (source[j] === '\\') {
          value += source.slice(j, j + 2);
          j += 2;
        } else {
          value += source[j++];
        }
      }
      out.push({ value, raw: source.slice(start, j + 1), line: lineAt(start) });
      prev = 'string';
      i = j + 1;
      continue;
    }
    if (c === '`') {
      const start = i;
      let j = i + 1;
      let chunkStart = i + 1;
      while (j < source.length && source[j] !== '`') {
        if (source[j] === '\\') { j += 2; continue; }
        if (source[j] === '$' && source[j + 1] === '{') {
          out.push({ value: source.slice(chunkStart, j), raw: source.slice(start, j + 2), line: lineAt(start) });
          stack.push({ depth: 1, tickStart: start });
          prev = '${';
          j += 2;
          break;
        }
        j++;
      }
      if (prev !== '${') {
        out.push({ value: source.slice(chunkStart, j), raw: source.slice(start, j + 1), line: lineAt(start) });
        prev = 'string';
        i = j + 1;
      } else {
        i = j;
      }
      continue;
    }
    if (c === '{' && stack.length) { stack.at(-1).depth++; prev = c; i++; continue; }
    if (c === '}' && stack.length && --stack.at(-1).depth === 0) {
      stack.pop();
      const resume = i;
      let j = i + 1;
      const chunkStart = i + 1;
      prev = '';
      while (j < source.length && source[j] !== '`') {
        if (source[j] === '\\') { j += 2; continue; }
        if (source[j] === '$' && source[j + 1] === '{') {
          out.push({ value: source.slice(chunkStart, j), raw: source.slice(resume, j + 2), line: lineAt(resume) });
          stack.push({ depth: 1, tickStart: resume });
          prev = '${';
          j += 2;
          break;
        }
        j++;
      }
      if (prev !== '${') {
        out.push({ value: source.slice(chunkStart, j), raw: source.slice(resume, j + 1), line: lineAt(resume) });
        prev = 'string';
        i = j + 1;
      } else {
        i = j;
      }
      continue;
    }
    if (c === '/' && next !== '/' && next !== '*' && regexAllowed()) {
      let j = i + 1;
      let inClass = false;
      while (j < source.length && (inClass || source[j] !== '/')) {
        if (source[j] === '\\') j += 2;
        else {
          if (source[j] === '[') inClass = true;
          else if (source[j] === ']') inClass = false;
          j++;
        }
      }
      while (/[a-z]/i.test(source[j + 1] ?? '')) j++;
      prev = 'regex';
      i = j + 1;
      continue;
    }
    if (/\s/.test(c)) { i++; continue; }
    if (/[A-Za-z0-9_$]/.test(c)) {
      let j = i;
      while (/[A-Za-z0-9_$]/.test(source[j] ?? '')) j++;
      prev = source.slice(i, j);
      i = j;
      continue;
    }
    prev = c;
    i++;
  }
  return out;
}

function referencesRuntimeDir(relPath, candidate) {
  const clean = candidate.split('?')[0].split('#')[0].trim();
  if (!clean) return false;
  if (/(?:^|[^A-Za-z0-9_.-])src\/runtime(?:\/|$)/.test(clean)) return true;
  if (clean.startsWith('./') || clean.startsWith('../')) {
    const resolved = posix.normalize(posix.join(posix.dirname(relPath), clean));
    if (resolved === 'src/runtime' || resolved.startsWith('src/runtime/')) return true;
  }
  if (posix.dirname(relPath) === 'src' && /^runtime\/[^'"]*\.(?:mjs|cjs|js)$/.test(clean)) return true;
  return false;
}

export function findSeamViolations(relPath, source) {
  if (relPath === 'src/runtime-seam.mjs' || relPath.startsWith('src/runtime/')) return [];
  const hits = [];
  if (/\.(?:mjs|cjs|js)$/.test(relPath)) {
    for (const token of stringLiterals(source)) {
      if (referencesRuntimeDir(relPath, token.value)) {
        hits.push(`${relPath}:${token.line}: ${token.raw}`);
      }
    }
    return hits;
  }
  const lines = source.split('\n');
  lines.forEach((line, index) => {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) return;
    if (/(?:^|[^A-Za-z0-9_.-])src\/runtime(?:\/|$)/.test(line)) {
      hits.push(`${relPath}:${index + 1}: ${trimmed}`);
    }
  });
  return hits;
}

test('SEAM1: only src/runtime-seam.mjs imports or addresses src/runtime/ across src, bin and scripts', () => {
  const files = [...walk('src'), ...walk('bin'), ...walk('scripts')]
    .filter(rel => !rel.startsWith('src/runtime/') && rel !== 'src/runtime-seam.mjs');
  assert.ok(files.length >= 75, `expected full pdd file scan, got ${files.length}`);
  const violations = files.flatMap(rel => findSeamViolations(rel, readFileSync(join(root, rel), 'utf8')));
  assert.deepEqual(violations, [], `Files outside src/runtime-seam.mjs must not import src/runtime/:\n${violations.join('\n')}`);
});

test('SEAM2: src/runtime-seam.mjs imports only src/runtime/index.mjs from src/runtime/ and exposes its surface', async () => {
  const seamSource = readFileSync(join(root, 'src/runtime-seam.mjs'), 'utf8');
  const runtimeSpecifiers = stringLiterals(seamSource)
    .map(item => item.value)
    .filter(specifier => referencesRuntimeDir('src/runtime-seam.mjs', specifier));
  assert.deepEqual([...new Set(runtimeSpecifiers)], ['./runtime/index.mjs']);
  const seam = await import('../src/runtime-seam.mjs');
  const entry = await import('../src/runtime/index.mjs');
  assert.deepEqual(Object.keys(seam).sort(), Object.keys(entry).sort());
  for (const key of Object.keys(entry)) {
    assert.equal(typeof seam[key], typeof entry[key], `seam export ${key} must match typeof src/runtime/index.mjs`);
  }
});

test('SEAM4: Try CLI launcher names stable pdd-owned src/try-doors.mjs entry', async t => {
  const { pathToFileURL } = await import('node:url');
  const { Readable } = await import('node:stream');
  const { rmSync, writeFileSync } = await import('node:fs');
  const { harbor, fakeRuntime, portsFor, PLACE } = await import('./runtime-fake.mjs');
  const seam = await import('../src/runtime-seam.mjs');
  const stableEntry = await import('../src/try-doors.mjs');
  assert.equal(stableEntry.runShim, seam.runShim);
  const setup = harbor(t, repo => {
    rmSync(join(repo, 'tests/unknown-item.json'));
    const input = { type: 'object', properties: { argv: { type: 'array', items: { type: 'string' } } }, required: ['argv'], additionalProperties: false };
    const result = { type: 'object', properties: { stdout: { type: 'string' }, stderr: { type: 'string' }, exit_code: { type: 'integer' } }, required: ['stdout', 'stderr', 'exit_code'], additionalProperties: false };
    const iface = { status: 'draft', prose_sha256: '', entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 }, conventions: ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' })) };
    const content = () => `# paperclip\n\nPrint each argument.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
    iface.prose_sha256 = seam.proseSha256(content());
    writeFileSync(join(repo, PLACE), content());
    writeFileSync(join(repo, 'user_stories/place-order.md'), '# Arguments\n\nI can pass words.\n\n## Acceptance criteria\n\n1. Each argument prints.\n');
    const doc = { schema_version: 'prompt-runtime.program-scenario.v1', story_path: 'user_stories/place-order.md', criteria: [{ id: 'AC1', text: 'Each argument prints.' }], initial_world: {}, simulation: {}, context: [], steps: [{ step_id: 'one', entry_path: PLACE, operation: 'main', input: { argv: ['hi'] }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'hi\n' }] }] };
    writeFileSync(join(repo, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
  });
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.url.endsWith('/model')) return { status: 200, json: { calls: { cap: 40, remaining: 40 } } };
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    return { status: 200, json: f.tryJob(entry.url.split('/').at(-1)) };
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { stdin: Readable.from([]), openUrl: async () => false });
  const code = await seam.runTry({ cwd: setup.repo, words: ['place-order'], options: { '--cli': true } }, ports);
  assert.equal(code, 0, ports.stderr.text);
  const launcherText = readFileSync(join(setup.repo, '.pdd/try/bin/paperclip'), 'utf8');
  const expectedUrl = pathToFileURL(join(root, 'src/try-doors.mjs')).href;
  assert.ok(launcherText.includes(expectedUrl), `expected launcher to include ${expectedUrl}, got:\n${launcherText}`);
  assert.ok(!launcherText.includes('/src/runtime/try-doors.mjs'), launcherText);
});

test('SEAM3: detector catches static, dynamic, re-export, URL and child-process imports of src/runtime/', () => {
  const cases = [
    ['src/pdd-cli.mjs', "import { runCheck } from './runtime/runtime-client.mjs';\n"],
    ['src/pdd-cli.mjs', "export * from './runtime/index.mjs';\n"],
    ['src/autopilot-launcher.mjs', "const m = await import('./runtime/runtime-client.mjs');\n"],
    ['src/workflow-replay.mjs', "const u = new URL('./runtime/runtime-preflight.mjs', import.meta.url);\n"],
    ['src/workflow-replay.mjs', "const script = `import {captureSource} from ${JSON.stringify(new URL('./runtime/runtime-preflight.mjs', import.meta.url).href)};`;\n"],
    ['bin/pdd.mjs', "import '../src/runtime/index.mjs';\n"],
    ['scripts/autopilot-smoke.mjs', "const p = 'src/runtime/runtime-client.mjs';\n"],
    ['scripts/vm-suite.sh', "node src/runtime/runtime-client.mjs\n"],
  ];
  for (const [file, code] of cases) {
    assert.ok(findSeamViolations(file, code).length > 0, `expected violation for ${file}: ${code.trim()}`);
  }
  // Comments, .pdd/runtime, test/runtime/ and prompts/cli/runtime-entry.prompt.md are allowed.
  assert.deepEqual(findSeamViolations('src/workflow-view.mjs', "// Moved to src/runtime/runtime-preflight.mjs\nimport { findTests } from './runtime-seam.mjs';\nconst a = '.pdd/runtime';\nconst b = 'test/runtime/foo.json';\nconst c = 'prompts/cli/runtime-entry.prompt.md';\n"), []);
});

const BASE_HELP_MODULES = [
  'src/agent-adapters.mjs',
  'src/agent-config.mjs',
  'src/agent-packet.mjs',
  'src/argument-parser.mjs',
  'src/command-catalog.mjs',
  'src/completion.mjs',
  'src/contract-refs.mjs',
  'src/path-diagnostic.mjs',
  'src/pdd-cli.mjs',
  'src/project-setup.mjs',
  'src/runtime-binding-plan.mjs',
  'src/runtime-markdown.mjs',
  'src/runtime-outcome.mjs',
  'src/runtime-output.mjs',
  'src/runtime-preflight.mjs',
  'src/runtime-workspace.mjs',
  'src/scenario-json.mjs',
  'src/secret-redaction.mjs',
  'src/setup-interaction.mjs',
  'src/skills-install.mjs',
  'src/workflow-agents.mjs',
  'src/workflow-areas.mjs',
  'src/workflow-setup.mjs',
];

async function loadedSrcModules(args) {
  const { spawnSync } = await import('node:child_process');
  const { pathToFileURL } = await import('node:url');
  const rootPrefix = pathToFileURL(join(root, 'src/')).href;
  const loaderSource = `
    export async function resolve(specifier, context, nextResolve) {
      const resolved = await nextResolve(specifier, context);
      if (resolved.url.startsWith(${JSON.stringify(rootPrefix)})) {
        process.stderr.write('PDD_LOADED:' + resolved.url.slice(${JSON.stringify(rootPrefix)}.length) + '\\n');
      }
      return resolved;
    }
  `;
  const registerHook = `import { register } from 'node:module'; register(${JSON.stringify(`data:text/javascript,${encodeURIComponent(loaderSource)}`)});`;
  const registerUrl = `data:text/javascript,${encodeURIComponent(registerHook)}`;
  const run = spawnSync(process.execPath, ['--import', registerUrl, join(root, 'bin/pdd.mjs'), ...args], {
    cwd: root,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  assert.equal(run.status, 0, run.stderr);
  assert.ok(run.stdout.length > 0);
  return [...new Set(
    run.stderr
      .split('\n')
      .filter(line => line.startsWith('PDD_LOADED:'))
      .map(line => `src/${line.slice('PDD_LOADED:'.length)}`)
  )].sort();
}

test('SEAM5: pdd --help and pdd owner load the exact base src/ module set without loading runtime-client', async () => {
  for (const [args, expectedBase] of [
    [['--help'], BASE_HELP_MODULES],
    [['owner', 'bin/pdd.mjs'], [...BASE_HELP_MODULES, 'src/file-owner.mjs'].sort()],
  ]) {
    const loaded = await loadedSrcModules(args);
    for (const forbidden of [
      'src/runtime/runtime-client.mjs',
      'src/runtime/try-mcp.mjs',
      'src/runtime/try-doors.mjs',
      'src/runtime/interface-draft.mjs',
      'src/runtime/contracts.mjs',
      'src/runtime/runtime-slots.mjs',
      'src/runtime/runtime-check-plan.mjs',
    ]) {
      assert.ok(!loaded.includes(forbidden), `${forbidden} must not load for pdd ${args.join(' ')}`);
    }
    const normalized = loaded
      .filter(rel => rel !== 'src/runtime-seam.mjs' && rel !== 'src/runtime/index.mjs')
      .map(rel => rel.startsWith('src/runtime/') ? `src/${rel.slice('src/runtime/'.length)}` : rel)
      .sort();
    assert.deepEqual(normalized, expectedBase, `loaded modules mismatch for pdd ${args.join(' ')}`);
  }
});
