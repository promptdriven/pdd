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

// Decode JavaScript string and template escape sequences before resolving module/file paths.
function decodeJsEscapes(raw) {
  let out = '';
  for (let i = 0; i < raw.length; i++) {
    if (raw[i] !== '\\') {
      out += raw[i];
      continue;
    }
    i++;
    if (i >= raw.length) break;
    const c = raw[i];
    if (c === '\r') {
      if (raw[i + 1] === '\n') i++;
      continue;
    }
    if (c === '\n' || c === '\u2028' || c === '\u2029') continue;
    if (c === 'x' && /^[0-9a-fA-F]{2}$/.test(raw.slice(i + 1, i + 3))) {
      out += String.fromCharCode(Number.parseInt(raw.slice(i + 1, i + 3), 16));
      i += 2;
      continue;
    }
    if (c === 'u' && raw[i + 1] === '{') {
      const close = raw.indexOf('}', i + 2);
      const hex = close > i + 2 ? raw.slice(i + 2, close) : '';
      if (/^[0-9a-fA-F]{1,6}$/.test(hex)) {
        const cp = Number.parseInt(hex, 16);
        if (cp <= 0x10ffff) {
          out += String.fromCodePoint(cp);
          i = close;
          continue;
        }
      }
    }
    if (c === 'u' && /^[0-9a-fA-F]{4}$/.test(raw.slice(i + 1, i + 5))) {
      out += String.fromCharCode(Number.parseInt(raw.slice(i + 1, i + 5), 16));
      i += 4;
      continue;
    }
    if (/[0-7]/.test(c)) {
      const oct = raw.slice(i, i + 3).match(/^[0-7]{1,3}/)[0];
      out += String.fromCharCode(Number.parseInt(oct, 8));
      i += oct.length - 1;
      continue;
    }
    const single = { n: '\n', r: '\r', t: '\t', b: '\b', f: '\f', v: '\v' };
    out += single[c] ?? c;
  }
  return out;
}

// Extract embedded JS module specifiers (import/export ... from, import(), require(), new URL()) inside string/template text.
function embeddedModuleSpecifiers(text) {
  const specs = [];
  const patterns = [
    /\bimport\s+(?:[^;]*?\bfrom\s*)?(['"`])((?:\\[\s\S]|(?!\1)[\s\S])*)\1/g,
    /\bexport\s+[^;]*?\bfrom\s*(['"`])((?:\\[\s\S]|(?!\1)[\s\S])*)\1/g,
    /\b(?:import|require|req)\s*\(\s*(['"`])((?:\\[\s\S]|(?!\1)[\s\S])*)\1/g,
    /\bnew\s+URL\s*\(\s*(['"`])((?:\\[\s\S]|(?!\1)[\s\S])*)\1/g,
  ];
  for (const pattern of patterns) {
    let match;
    while ((match = pattern.exec(text)) !== null) {
      specs.push(decodeJsEscapes(match[2]));
    }
  }
  return specs;
}

// Extract string and template-chunk literals while skipping JS comments and regex literals.
function stringLiterals(source) {
  const out = [];
  const stack = [];
  let i = 0;
  let prev = '';
  const history = [];
  const pushToken = token => {
    prev = token;
    history.push(token);
    if (history.length > 4) history.shift();
  };
  const isSpecifierContext = () => (
    prev === 'import'
    || prev === 'from'
    || (prev === '(' && ['import', 'require', 'req'].includes(history.at(-2)))
    || (prev === '(' && history.at(-2) === 'URL' && history.at(-3) === 'new')
  );
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
      const isModuleSpecifier = isSpecifierContext();
      let j = i + 1;
      while (j < source.length && source[j] !== c) {
        if (source[j] === '\\') j += 2;
        else j++;
      }
      const rawBody = source.slice(i + 1, j);
      out.push({ value: decodeJsEscapes(rawBody), raw: source.slice(start, j + 1), line: lineAt(start), isModuleSpecifier });
      pushToken('string');
      i = j + 1;
      continue;
    }
    if (c === '`') {
      const start = i;
      const isModuleSpecifier = isSpecifierContext();
      let j = i + 1;
      const chunkStart = i + 1;
      let interpolated = false;
      while (j < source.length && source[j] !== '`') {
        if (source[j] === '\\') { j += 2; continue; }
        if (source[j] === '$' && source[j + 1] === '{') {
          out.push({ value: decodeJsEscapes(source.slice(chunkStart, j)), raw: source.slice(start, j + 2), line: lineAt(start), isModuleSpecifier });
          stack.push({ depth: 1, tickStart: start });
          pushToken('${');
          j += 2;
          interpolated = true;
          break;
        }
        j++;
      }
      if (!interpolated) {
        out.push({ value: decodeJsEscapes(source.slice(chunkStart, j)), raw: source.slice(start, j + 1), line: lineAt(start), isModuleSpecifier });
        pushToken('string');
        i = j + 1;
      } else {
        i = j;
      }
      continue;
    }
    if (c === '{' && stack.length) { stack.at(-1).depth++; pushToken(c); i++; continue; }
    if (c === '}' && stack.length && --stack.at(-1).depth === 0) {
      stack.pop();
      const resume = i;
      let j = i + 1;
      const chunkStart = i + 1;
      prev = '';
      let interpolated = false;
      while (j < source.length && source[j] !== '`') {
        if (source[j] === '\\') { j += 2; continue; }
        if (source[j] === '$' && source[j + 1] === '{') {
          out.push({ value: decodeJsEscapes(source.slice(chunkStart, j)), raw: source.slice(resume, j + 2), line: lineAt(resume), isModuleSpecifier: false });
          stack.push({ depth: 1, tickStart: resume });
          pushToken('${');
          j += 2;
          interpolated = true;
          break;
        }
        j++;
      }
      if (!interpolated) {
        out.push({ value: decodeJsEscapes(source.slice(chunkStart, j)), raw: source.slice(resume, j + 1), line: lineAt(resume), isModuleSpecifier: false });
        pushToken('string');
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
      pushToken('regex');
      i = j + 1;
      continue;
    }
    if (/\s/.test(c)) { i++; continue; }
    if (/[A-Za-z0-9_$]/.test(c)) {
      let j = i;
      while (/[A-Za-z0-9_$]/.test(source[j] ?? '')) j++;
      pushToken(source.slice(i, j));
      i = j;
      continue;
    }
    pushToken(c);
    i++;
  }
  return out;
}

function scannedCandidates(source) {
  const candidates = [];
  for (const token of stringLiterals(source)) {
    candidates.push({ value: token.value, raw: token.raw, line: token.line, isModuleSpecifier: token.isModuleSpecifier });
    for (const embedded of embeddedModuleSpecifiers(token.value)) {
      candidates.push({ value: embedded, raw: token.raw, line: token.line, isModuleSpecifier: true });
    }
  }
  return candidates;
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
    for (const item of scannedCandidates(source)) {
      if (referencesRuntimeDir(relPath, item.value)) {
        hits.push(`${relPath}:${item.line}: ${item.raw}`);
      }
    }
    return [...new Set(hits)];
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

function referencesOutsideRuntime(relPath, candidate, { isModuleSpecifier = false } = {}) {
  const clean = candidate.split('?')[0].split('#')[0].trim();
  if (!clean) return false;
  if (isModuleSpecifier && (clean === '..' || clean === '../')) return true;
  if ((clean.startsWith('./') || clean.startsWith('../')) && clean !== './' && clean !== '../') {
    const resolved = posix.normalize(posix.join(posix.dirname(relPath), clean));
    if (resolved !== 'src/runtime' && !resolved.startsWith('src/runtime/')) return true;
  }
  if (/(?:^|[^A-Za-z0-9_.-])(?:src\/(?!runtime(?:\/|$))[A-Za-z0-9_./-]+\.(?:mjs|cjs|js)|bin\/pdd\.mjs)(?:$|[^A-Za-z0-9_.-])/.test(clean)) {
    return true;
  }
  return false;
}

export function findInwardViolations(relPath, source) {
  if (!relPath.startsWith('src/runtime/')) return [];
  const hits = [];
  for (const item of scannedCandidates(source)) {
    if (referencesOutsideRuntime(relPath, item.value, { isModuleSpecifier: item.isModuleSpecifier })) {
      hits.push(`${relPath}:${item.line}: ${item.raw}`);
    }
  }
  return [...new Set(hits)];
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
  const runtimeSpecifiers = scannedCandidates(seamSource)
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

test('SEAM3: detector catches static, dynamic, re-export, URL, escaped and child-process imports of src/runtime/', () => {
  const cases = [
    ['src/pdd-cli.mjs', "import { runCheck } from './runtime/runtime-client.mjs';\n"],
    ['src/pdd-cli.mjs', "export * from './runtime/index.mjs';\n"],
    ['src/autopilot-launcher.mjs', "const m = await import('./runtime/runtime-client.mjs');\n"],
    ['src/workflow-replay.mjs', "const u = new URL('./runtime/runtime-preflight.mjs', import.meta.url);\n"],
    ['src/workflow-replay.mjs', "const script = `import {captureSource} from ${JSON.stringify(new URL('./runtime/runtime-preflight.mjs', import.meta.url).href)};`;\n"],
    ['src/pdd-cli.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"import {runCheck} from './runtime/runtime-client.mjs';\"], {cwd: new URL('.', import.meta.url)});\n"],
    ['src/pdd-cli.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', `export { runCheck } from './runtime/runtime-client.mjs';`]);\n"],
    ['src/pdd-cli.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"await import('./runtime/runtime-client.mjs');\"]);\n"],
    ['src/pdd-cli.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"new URL('./runtime/runtime-client.mjs', import.meta.url);\"]);\n"],
    ['src/pdd-cli.mjs', "import './\\x72untime/runtime-client.mjs';\n"],
    ['src/pdd-cli.mjs', "import './\\u0072untime/runtime-client.mjs';\n"],
    ['src/pdd-cli.mjs', "const m = await import(`./\\u{72}untime/runtime-client.mjs`);\n"],
    ['src/pdd-cli.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"import './\\\\x72untime/runtime-client.mjs';\"]);\n"],
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
      'src/runtime/product-composition.mjs',
      'src/runtime/agent-chat.mjs',
      'src/runtime/runtime-workspace-migration.mjs',
      'src/runtime/secret-redaction.mjs',
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

test('SEAM6: no file in src/runtime/ imports or addresses a path outside src/runtime/', () => {
  const files = walk('src/runtime');
  assert.ok(files.length >= 25, `expected full src/runtime/ file scan, got ${files.length}`);
  const violations = files.flatMap(rel => findInwardViolations(rel, readFileSync(join(root, rel), 'utf8')));
  assert.deepEqual(violations, [], `Files in src/runtime/ must not import outside src/runtime/:\n${violations.join('\n')}`);
});

test('SEAM7: inward detector catches static, dynamic, require, package.json URL, escaped, child-process and string paths outside src/runtime/', () => {
  const cases = [
    ['src/runtime/runtime-slots.mjs', "import { NAMES } from '../command-catalog.mjs';\n"],
    ['src/runtime/index.mjs', "export * from '../runtime-seam.mjs';\n"],
    ['src/runtime/interface-draft.mjs', "const m = await import('../approval-policy.mjs');\n"],
    ['src/runtime/runtime-check-plan.mjs', "const { headerPrompts } = req('../file-owner.mjs');\n"],
    ['src/runtime/runtime-client.mjs', "const pkg = new URL('../../package.json', import.meta.url);\n"],
    ['src/runtime/try-doors.mjs', "const script = `import ${JSON.stringify('../try-doors.mjs')}`;\n"],
    ['src/runtime/runtime-client.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"import { NAMES } from '../command-catalog.mjs';\"], {cwd: new URL('.', import.meta.url)});\n"],
    ['src/runtime/runtime-client.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"export * from '../product.mjs';\"]);\n"],
    ['src/runtime/runtime-client.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"await import('../workflow-runner.mjs');\"]);\n"],
    ['src/runtime/runtime-client.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"new URL('../../package.json', import.meta.url);\"]);\n"],
    ['src/runtime/runtime-slots.mjs', "import { NAMES } from '../\\x63ommand-catalog.mjs';\n"],
    ['src/runtime/runtime-slots.mjs', "import { NAMES } from '\\u002e\\u002e/command-catalog.mjs';\n"],
    ['src/runtime/runtime-client.mjs', "const u = new URL(`..\\u{2f}..\\u{2f}package.json`, import.meta.url);\n"],
    ['src/runtime/runtime-client.mjs', "import '\\x2e\\x2e';\n"],
    ['src/runtime/runtime-client.mjs', "const p = 'src/workflow-runner.mjs';\n"],
    ['src/runtime/runtime-client.mjs', "import '..';\n"],
  ];
  for (const [file, code] of cases) {
    assert.ok(findInwardViolations(file, code).length > 0, `expected inward violation for ${file}: ${code.trim()}`);
  }
  assert.deepEqual(
    findInwardViolations(
      'src/runtime/runtime-preflight.mjs',
      "// Generated from prompts/cli/runtime-preflight.prompt.md\nimport { cleanText } from './runtime-output.mjs';\nconst ok = !word.startsWith('../') && word !== '..';\nconst pkg = `${head}:package.json`;\n",
    ),
    [],
  );
});
