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

test('SEAM8 (R2-1): host and Runtime share one secret-redaction registry through the seam without touching fallback copy', async t => {
  const { mkdtempSync, rmSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const hostRedaction = await import('../src/secret-redaction.mjs');
  const packageFallback = await import('../src/runtime/secret-redaction.mjs');
  const { createTryGuide: createStandaloneGuide } = await import('../src/runtime/agent-guide.mjs');
  const seam = await import('../src/runtime-seam.mjs');

  const dir = mkdtempSync(join(tmpdir(), 'pdd-r2-1-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));

  const markerBefore = 'zzOpaqueHostBefore987654321';
  const markerAfter = 'zzOpaqueHostAfter987654321';
  const markerFromRuntime = 'zzOpaqueRuntimeToken987654321';
  const markerStandalone = 'zzOpaqueStandalone987654321';

  hostRedaction.rememberSecrets(markerBefore);
  const guide = seam.createTryGuide({
    root: dir,
    env: {},
    model: { entries: [], stories: [] },
    test: {},
    features: [],
    secrets: [],
    ports: {
      readAgentScenarios: () => [],
      buildProjectCard: () => ({ fingerprint: 'fp', sourceFingerprint: 'fp', text: 'Card', productRules: [] }),
    },
  });
  assert.equal(guide.wire({ say: `the agent said ${markerBefore}`, fill: null }).say, 'the agent said [redacted]');

  // Values remembered on the host after guide creation are immediately redacted too.
  hostRedaction.rememberSecrets(markerAfter);
  assert.equal(guide.wire({ say: `later ${markerAfter}`, fill: null }).say, 'later [redacted]');

  // Values remembered by Runtime through the seam reach the host registry.
  await seam.checkRuntimeHealth(
    { env: { PDD_RUNTIME_URL: 'https://runtime.example.test' } },
    {
      gh: () => ({ status: 0, stdout: `${markerFromRuntime}\n`, stderr: '' }),
      fetch: async () => { throw new Error('network disabled'); },
      timeoutMs: 50,
    },
  );
  assert.ok(hostRedaction.knownSecretValues({}).includes(markerFromRuntime));
  assert.equal(hostRedaction.redactSecrets(`echo ${markerFromRuntime}`), 'echo [redacted]');
  assert.equal(guide.wire({ say: `runtime ${markerFromRuntime}`, fill: null }).say, 'runtime [redacted]');

  // Seam calls never populate the standalone fallback Set in src/runtime/secret-redaction.mjs.
  const fallbackKnown = packageFallback.knownSecretValues({});
  assert.ok(!fallbackKnown.includes(markerBefore));
  assert.ok(!fallbackKnown.includes(markerAfter));
  assert.ok(!fallbackKnown.includes(markerFromRuntime));

  // Direct standalone callers without ports.redaction still get the package fallback copy.
  packageFallback.rememberSecrets(markerStandalone);
  const standaloneGuide = createStandaloneGuide({
    root: dir,
    env: {},
    model: { entries: [], stories: [] },
    test: {},
    features: [],
    secrets: [],
    ports: {
      readAgentScenarios: () => [],
      buildProjectCard: () => ({ fingerprint: 'fp', sourceFingerprint: 'fp', text: 'Card', productRules: [] }),
    },
  });
  assert.equal(standaloneGuide.wire({ say: `standalone ${markerStandalone}`, fill: null }).say, 'standalone [redacted]');
});

test('SEAM9 (R2-2): seam preserves legacy port overrides and ignores own undefined port values across added ports', async t => {
  const { execFileSync } = await import('node:child_process');
  const { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const hostRedaction = await import('../src/secret-redaction.mjs');
  const seam = await import('../src/runtime-seam.mjs');

  const tmp = mkdtempSync(join(tmpdir(), 'pdd-r2-2-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));

  // 1. Legacy readEvidenceEligibility override wins on migrateRuntimeWorkspace.
  const projRoot = join(tmp, 'proj');
  const dstRoot = join(tmp, 'dst');
  for (const dir of [projRoot, dstRoot]) {
    mkdirSync(join(dir, 'prompts'), { recursive: true });
    mkdirSync(join(dir, 'user_stories'), { recursive: true });
    mkdirSync(join(dir, 'tests'), { recursive: true });
    execFileSync('git', ['init', '-q'], { cwd: dir });
    const iface = {
      status: 'draft',
      prose_sha256: '',
      entries: [{
        operation: 'main',
        input_schema: { type: 'object', properties: { argv: { type: 'array', items: { type: 'string' } } }, required: ['argv'], additionalProperties: false },
        result_schema: { type: 'object', properties: { stdout: { type: 'string' } }, required: ['stdout'], additionalProperties: false },
        errors: [],
      }],
      calls: [],
      resources: [],
      limits: { max_steps: 1, max_model_calls: 1 },
    };
    const promptBody = () => `# Tool\n\nEcho.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
    iface.prose_sha256 = seam.proseSha256(promptBody());
    writeFileSync(join(dir, 'prompts/tool.prompt.md'), promptBody());
    writeFileSync(join(dir, 'user_stories/tool.md'), '# Tool\n\nI can echo.\n\n## Acceptance criteria\n\n1. Echo works.\n');
    writeFileSync(
      join(dir, 'tests/tool.json'),
      JSON.stringify({
        schema_version: 'prompt-runtime.program-scenario.v1',
        story_path: 'user_stories/tool.md',
        criteria: [{ id: 'AC1', text: 'Echo works.' }],
        initial_world: {},
        steps: [{ step_id: 's1', entry_path: 'prompts/tool.prompt.md', operation: 'main', input: { argv: [] }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'ok' }] }],
      }, null, 2) + '\n',
    );
    execFileSync('git', ['add', '.'], { cwd: dir });
  }
  const captured = seam.captureSource(realpathSync(projRoot), { tests: ['tests/tool.json'], appMap: null });
  let legacyEligibilityCalls = 0;
  const migrationPreview = await seam.migrateRuntimeWorkspace(
    {
      root: dstRoot,
      projectionRoot: projRoot,
      mappings: [
        { from: 'prompts/tool.prompt.md', to: 'prompts/tool.prompt.md' },
        { from: 'user_stories/tool.md', to: 'user_stories/tool.md' },
        { from: 'tests/tool.json', to: 'tests/tool.json' },
      ],
      write: false,
    },
    {
      evidenceEligibility: undefined,
      readEvidenceEligibility: () => {
        legacyEligibilityCalls += 1;
        return { state: 'eligible', reason: null };
      },
      store: {
        inventory: async () => [{
          id: 'batch-1',
          kind: 'batch',
          raw: '{}',
          record: { batch: 'batch-1', rows: [{ test: 'tests/tool.json' }], source_sha256: captured.sha256 },
        }],
      },
    },
  );
  assert.equal(legacyEligibilityCalls, 1);
  assert.equal(migrationPreview.state, 'preview');
  assert.deepEqual(migrationPreview.unresolved, []);
  assert.equal(migrationPreview.items[0]?.state, 'ready');

  // 2. Legacy readEvidenceEligibility & redactSecrets overrides win on createTryGuide; synchronous runContracts works.
  let guideLegacyCalls = 0;
  const customGuide = seam.createTryGuide({
    root: dstRoot,
    env: {},
    model: { entries: [], stories: [] },
    test: { path: 'tests/tool.json' },
    features: [],
    secrets: [],
    ports: {
      evidenceEligibility: undefined,
      readEvidenceEligibility: () => {
        guideLegacyCalls += 1;
        return { state: 'eligible', reason: null };
      },
      redaction: undefined,
      redactSecrets: text => String(text).replaceAll('CUSTOM_SECRET_TOKEN', '[custom-redacted]'),
    },
  });
  assert.equal(customGuide.wire({ say: 'hi CUSTOM_SECRET_TOKEN', fill: null }).say, 'hi [custom-redacted]');
  const syncCode = seam.runContracts(
    { cwd: dstRoot, words: [], options: {} },
    {
      stdout: { write() {} },
      stderr: { write() {} },
      evidenceEligibility: undefined,
      readEvidenceEligibility: () => ({ state: 'eligible', reason: null }),
    },
  );
  assert.equal(typeof syncCode, 'number');
  assert.equal(syncCode, 0);

  // 3. Own undefined port values never erase seam defaults (SVG --lint --local --json warning + headerPrompts + product + jobs + redaction).
  const svgRepo = join(tmp, 'svg-repo');
  mkdirSync(join(svgRepo, 'prompts/views'), { recursive: true });
  mkdirSync(join(svgRepo, 'user_stories'), { recursive: true });
  mkdirSync(join(svgRepo, 'tests'), { recursive: true });
  mkdirSync(join(svgRepo, 'src'), { recursive: true });
  execFileSync('git', ['init', '-q'], { cwd: svgRepo });
  writeFileSync(join(svgRepo, 'prompts/views/card.ui.svg'), '<svg viewBox="0 0 100 40"><text>Visible</text></svg>\n');
  writeFileSync(join(svgRepo, 'prompts/card.prompt.md'), '# Card\n\n![Card](views/card.ui.svg)\n\nRender the card.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(svgRepo, 'src/card.mjs'), '// Generated from prompts/card.prompt.md\nexport const card = 1;\n');
  writeFileSync(join(svgRepo, 'user_stories/card.md'), '# Card\n\nI can view card.\n\n## Acceptance criteria\n\n1. Card renders.\n');
  writeFileSync(
    join(svgRepo, 'tests/card.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/card.md',
      criteria: [{ id: 'AC1', text: 'Card renders.' }],
      initial_world: {},
      steps: [{ step_id: 's1', entry_path: 'prompts/card.prompt.md', operation: 'render', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', value: true }] }],
    }, null, 2) + '\n',
  );
  execFileSync('git', ['add', '.'], { cwd: svgRepo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: svgRepo });
  writeFileSync(join(svgRepo, 'src/card.mjs'), '// Generated from prompts/card.prompt.md\nexport const card = 2;\n');

  let outJson = '';
  let errText = '';
  const checkCode = await seam.runCheck(
    { cwd: svgRepo, words: [], options: { '--lint': true, '--local': true, '--json': true }, client: { version: undefined } },
    {
      stdout: { write: chunk => { outJson += chunk; } },
      stderr: { write: chunk => { errText += chunk; } },
      gh: () => { throw new Error('gh forbidden in --local'); },
      fetch: async () => { throw new Error('fetch forbidden in --local'); },
      lintSvgLayouts: undefined,
      headerPrompts: undefined,
      evidenceEligibility: undefined,
      readEvidenceEligibility: undefined,
      allRuns: undefined,
      assessNativeEvidence: undefined,
      usableResult: undefined,
      resultLines: undefined,
      compareScreen: undefined,
      formatScreenComparison: undefined,
      redaction: undefined,
      rememberSecrets: undefined,
      redactSecrets: undefined,
    },
  );
  assert.equal(checkCode, 4, errText);
  const parsedCheck = JSON.parse(outJson);
  assert.ok(
    Array.isArray(parsedCheck.warnings) && parsedCheck.warnings.some(w => w.includes('Visible')),
    `expected SVG Visible warning with lintSvgLayouts: undefined, got: ${JSON.stringify(parsedCheck.warnings)}`,
  );

  // buildCheckPlan with { headerPrompts: undefined } still classifies changed code via Generated-from header (not conservative fallback).
  const foundSvg = seam.findTests({ root: svgRepo });
  const plan = seam.buildCheckPlan(
    {
      root: svgRepo,
      found: foundSvg,
      selected: foundSvg.tests,
      rows: [{ test: 'tests/card.json', state: 'refused', steps: [] }],
      full: true,
      base: 'HEAD',
    },
    { headerPrompts: undefined },
  );
  assert.equal(plan.stories[0]?.role, 'target');
  assert.deepEqual(plan.stories[0]?.affected_paths, ['src/card.mjs']);

  // runJobs with { client: { commands: undefined } } keeps default command catalog names.
  let jobsOut = '';
  const jobsCode = await seam.runJobs(
    { cwd: svgRepo, words: [], options: {}, client: { commands: undefined } },
    { env: { HOME: tmp, PDD_STATE_DIR: join(tmp, 'state') }, stdout: { write: c => { jobsOut += c; } }, stderr: { write() {} } },
  );
  assert.equal(jobsCode, 0);
  assert.match(jobsOut, /No local interpreter jobs/);

  // composeProductTry with own undefined product parser ports keeps host product.mjs defaults.
  assert.throws(
    () => seam.composeProductTry(
      { root: svgRepo, found: foundSvg, words: [], options: { '--product': true } },
      { parseProductDocuments: undefined, parseProductWorldWriters: undefined },
    ),
    error => !(error instanceof TypeError),
  );

  // createAgentBridge honors nested agents.{loadDefinitions,list,ask} alias and ignores undefined seamPorts.
  let nestedLoadCalled = 0;
  await assert.rejects(
    () => seam.createAgentBridge(
      {
        root: dstRoot,
        ports: {
          env: {},
          stderr: { write() {} },
          agents: {
            loadDefinitions: () => {
              nestedLoadCalled += 1;
              return [];
            },
          },
        },
      },
      { path: 'tests/tool.json' },
      'try-1',
      {},
      'https://runtime.example.test/s/abc/',
      {
        loadAgentDefinitions: undefined,
        discoverAgents: undefined,
        askAgent: undefined,
        evidenceEligibility: undefined,
        readEvidenceEligibility: undefined,
        redaction: undefined,
      },
    ),
    /No agents are configured/,
  );
  assert.equal(nestedLoadCalled, 1);

  // createTryGuide with own undefined redaction still redacts host-remembered secrets.
  const undefMarker = 'zzOpaqueUndefPort987654321';
  hostRedaction.rememberSecrets(undefMarker);
  const undefGuide = seam.createTryGuide({
    root: dstRoot,
    env: {},
    model: { entries: [], stories: [] },
    test: {},
    features: [],
    secrets: [],
    ports: {
      redaction: undefined,
      redactSecrets: undefined,
      evidenceEligibility: undefined,
      readEvidenceEligibility: undefined,
      readAgentScenarios: () => [],
      buildProjectCard: () => ({ fingerprint: 'fp', sourceFingerprint: 'fp', text: 'Card', productRules: [] }),
    },
  });
  assert.equal(undefGuide.wire({ say: `v=${undefMarker}`, fill: null }).say, 'v=[redacted]');
});

test('SEAM10 (R2-4): workflow base SHA is observed inside runBatch after discovery/cache/preflight and honors explicit workflow or workflowBaseSha', async t => {
  const { execFileSync } = await import('node:child_process');
  const { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const seam = await import('../src/runtime-seam.mjs');

  const tmp = mkdtempSync(join(tmpdir(), 'pdd-r2-4-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));

  const repo = join(tmp, 'repo');
  const home = join(tmp, 'home');
  const stateDir = join(home, '.local/state/pdd');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  execFileSync('git', ['init', '-q'], { cwd: repo });

  const makePrompt = (title, bodyText) => {
    const input = { type: 'object', properties: { argv: { type: 'array', items: { type: 'string' } } }, required: ['argv'], additionalProperties: false };
    const result = { type: 'object', properties: { stdout: { type: 'string' }, stderr: { type: 'string' }, exit_code: { type: 'integer' } }, required: ['stdout', 'stderr', 'exit_code'], additionalProperties: false };
    const iface = {
      status: 'draft',
      prose_sha256: '',
      entries: [{
        operation: 'main',
        input_schema: input,
        result_schema: result,
        errors: [],
      }],
      calls: [],
      resources: [],
      limits: { max_steps: 1, max_model_calls: 1 },
      conventions: ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' })),
    };
    const render = () => `# ${title}\n\n${bodyText}\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
    iface.prose_sha256 = seam.proseSha256(render());
    return render();
  };

  for (const name of ['one', 'two']) {
    writeFileSync(join(repo, `prompts/${name}.prompt.md`), makePrompt(name, `Behavior v1 for ${name}.`));
    writeFileSync(join(repo, `user_stories/${name}.md`), `# ${name}\n\nI can run ${name}.\n\n## Acceptance criteria\n\n1. ${name} works.\n`);
    writeFileSync(
      join(repo, `tests/${name}.json`),
      JSON.stringify({
        schema_version: 'prompt-runtime.program-scenario.v1',
        story_path: `user_stories/${name}.md`,
        criteria: [{ id: 'AC1', text: `${name} works.` }],
        initial_world: {},
        simulation: {},
        context: [],
        steps: [{ step_id: 's1', entry_path: `prompts/${name}.prompt.md`, operation: 'main', input: { argv: ['hi'] }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'hi\n' }] }],
      }, null, 2) + '\n',
    );
  }
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'commit A'], { cwd: repo });
  const shaA = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: repo, encoding: 'utf8' }).trim();

  // Commit B modifies two.prompt.md; uncommitted edit modifies one.prompt.md after B.
  writeFileSync(join(repo, 'prompts/two.prompt.md'), makePrompt('two', 'Behavior v2 for two.'));
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'commit B'], { cwd: repo });
  const shaB = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: repo, encoding: 'utf8' }).trim();
  writeFileSync(join(repo, 'prompts/one.prompt.md'), makePrompt('one', 'Behavior v2 uncommitted for one.'));

  const realRepo = realpathSync(repo);
  const commonDir = realpathSync(execFileSync('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'], { cwd: repo, encoding: 'utf8' }).trim());
  const runDir = join(commonDir, 'pdd/runs/1');
  mkdirSync(runDir, { recursive: true });
  const writeRunBase = baseSha => {
    writeFileSync(
      join(runDir, 'status.json'),
      JSON.stringify({
        v: 1,
        number: 1,
        runId: 'run-r2-4',
        repo: 'example/repo',
        workflow: 'feature',
        state: 'active',
        root: realRepo,
        commonDir,
        runDir,
        baseSha,
        startedAt: '2026-11-11T00:00:00Z',
        updatedAt: '2026-11-11T00:00:00Z',
      }, null, 2) + '\n',
    );
  };
  writeFileSync(
    join(stateDir, 'runs.json'),
    JSON.stringify({
      version: 1,
      runs: [{ repo: 'example/repo', number: 1, workflow: 'feature', state: 'active', runDir, root: realRepo, updatedAt: '2026-11-11T00:00:00Z' }],
    }, null, 2) + '\n',
  );

  // 1. Race check: status.json starts at shaA before runCheck entry, and updates to shaB after discovery/cache-open (before preflight and buildCheckPlan).
  writeRunBase(shaA);
  let mutatedDuringStartup = false;
  let stderrRace = '';
  const raceCode = await seam.runCheck(
    { cwd: repo, words: [], options: { '--cache-clear': true }, cache: true },
    {
      env: { HOME: home, PDD_STATE_DIR: stateDir, PDD_RUNTIME_URL: 'https://runtime.example.test' },
      stdout: { write() {} },
      stderr: {
        write: c => {
          stderrRace += c;
          if (!mutatedDuringStartup && String(c).includes('pdd: test cache')) {
            mutatedDuringStartup = true;
            writeRunBase(shaB);
          }
        },
      },
      gh: () => ({ status: 1, stdout: '', stderr: '' }),
      fetch: async () => { throw new Error('network disabled'); },
    },
  );
  assert.equal(raceCode, 5, stderrRace);
  assert.equal(mutatedDuringStartup, true);
  assert.match(stderrRace, /target: user_stories\/one\.md/);
  assert.match(stderrRace, /baseline: user_stories\/two\.md/);

  // 2. Explicit input.workflow snapshot wins even when on-disk run points to shaB.
  let stderrExplicitWorkflow = '';
  const explicitWorkflowCode = await seam.runCheck(
    { cwd: repo, words: [], options: {}, workflow: { base_sha: shaA } },
    {
      env: { HOME: home, PDD_STATE_DIR: stateDir, PDD_RUNTIME_URL: 'https://runtime.example.test' },
      stdout: { write() {} },
      stderr: { write: c => { stderrExplicitWorkflow += c; } },
      gh: () => ({ status: 1, stdout: '', stderr: '' }),
      fetch: async () => { throw new Error('network disabled'); },
    },
  );
  assert.equal(explicitWorkflowCode, 5);
  assert.match(stderrExplicitWorkflow, /target: user_stories\/one\.md/);
  assert.match(stderrExplicitWorkflow, /target: user_stories\/two\.md/);

  // 3. Explicit ports.workflowBaseSha (string and function) overrides default lookup.
  let stderrPortString = '';
  await seam.runCheck(
    { cwd: repo, words: [], options: {} },
    {
      env: { HOME: home, PDD_STATE_DIR: stateDir, PDD_RUNTIME_URL: 'https://runtime.example.test' },
      stdout: { write() {} },
      stderr: { write: c => { stderrPortString += c; } },
      workflowBaseSha: shaA,
      gh: () => ({ status: 1, stdout: '', stderr: '' }),
      fetch: async () => { throw new Error('network disabled'); },
    },
  );
  assert.match(stderrPortString, /target: user_stories\/two\.md/);

  // 4. Conflicting-mode usage error (--read + --retry) and --local do not invoke workflowBaseSha / allRuns.
  let earlyReads = 0;
  const bogusCode = await seam.runCheck(
    { cwd: repo, words: ['batch-1'], options: { '--read': true, '--retry': true } },
    {
      env: { HOME: home, PDD_STATE_DIR: stateDir },
      stdout: { write() {} },
      stderr: { write() {} },
      allRuns: () => { earlyReads += 1; return []; },
    },
  );
  assert.equal(bogusCode, 2);
  assert.equal(earlyReads, 0);

  await seam.runCheck(
    { cwd: repo, words: [], options: { '--local': true } },
    {
      env: { HOME: home, PDD_STATE_DIR: stateDir },
      stdout: { write() {} },
      stderr: { write() {} },
      allRuns: () => { earlyReads += 1; return []; },
    },
  );
  assert.equal(earlyReads, 0);
});
