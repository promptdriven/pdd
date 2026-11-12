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
      out.push({ value: decodeJsEscapes(rawBody), raw: source.slice(start, j + 1), start, end: j + 1, standalone: true, line: lineAt(start), isModuleSpecifier });
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
          out.push({ value: decodeJsEscapes(source.slice(chunkStart, j)), raw: source.slice(start, j + 2), start, end: j + 2, standalone: false, line: lineAt(start), isModuleSpecifier });
          stack.push({ depth: 1, tickStart: start });
          pushToken('${');
          j += 2;
          interpolated = true;
          break;
        }
        j++;
      }
      if (!interpolated) {
        out.push({ value: decodeJsEscapes(source.slice(chunkStart, j)), raw: source.slice(start, j + 1), start, end: j + 1, standalone: true, line: lineAt(start), isModuleSpecifier });
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
          out.push({ value: decodeJsEscapes(source.slice(chunkStart, j)), raw: source.slice(resume, j + 2), start: resume, end: j + 2, standalone: false, line: lineAt(resume), isModuleSpecifier: false });
          stack.push({ depth: 1, tickStart: resume });
          pushToken('${');
          j += 2;
          interpolated = true;
          break;
        }
        j++;
      }
      if (!interpolated) {
        out.push({ value: decodeJsEscapes(source.slice(chunkStart, j)), raw: source.slice(resume, j + 1), start: resume, end: j + 1, standalone: false, line: lineAt(resume), isModuleSpecifier: false });
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

function stripCommentsPreservingLines(text) {
  let out = '';
  let i = 0;
  while (i < text.length) {
    const c = text[i];
    const next = text[i + 1];
    if (c === "'" || c === '"' || c === '`') {
      out += c;
      i++;
      while (i < text.length && text[i] !== c) {
        if (text[i] === '\\') {
          out += text.slice(i, i + 2);
          i += 2;
        } else {
          out += text[i];
          i++;
        }
      }
      if (i < text.length) { out += text[i]; i++; }
      continue;
    }
    if (c === '/' && next === '/') {
      const end = text.indexOf('\n', i + 2);
      if (end < 0) break;
      out += '\n';
      i = end + 1;
      continue;
    }
    if (c === '/' && next === '*') {
      const end = text.indexOf('*/', i + 2);
      const body = end < 0 ? text.slice(i + 2) : text.slice(i + 2, end);
      out += body.replace(/[^\n]/g, ' ');
      i = end < 0 ? text.length : end + 2;
      continue;
    }
    out += c;
    i++;
  }
  return out;
}

function isPlusSeparator(between) {
  return stripCommentsPreservingLines(between).trim() === '+';
}

function evalStaticStringExpr(expr) {
  const trimmed = stripCommentsPreservingLines(expr).trim();
  if (!trimmed) return null;
  const tokens = stringLiterals(trimmed);
  if (!tokens.length || !tokens.every(t => t.standalone)) return null;
  if (trimmed.slice(0, tokens[0].start).trim() !== '' || trimmed.slice(tokens.at(-1).end).trim() !== '') return null;
  for (let i = 0; i < tokens.length - 1; i++) {
    if (trimmed.slice(tokens[i].end, tokens[i + 1].start).trim() !== '+') return null;
  }
  return tokens.map(t => t.value).join('');
}

function parsePathBuilderCalls(clean) {
  const calls = [];
  const callStart = /\b(?:join|resolve)\s*\(/g;
  let match;
  while ((match = callStart.exec(clean)) !== null) {
    const openIdx = clean.indexOf('(', match.index);
    let depth = 1;
    let k = openIdx + 1;
    const args = [];
    let argStart = k;
    while (k < clean.length && depth > 0) {
      const ch = clean[k];
      if (ch === "'" || ch === '"' || ch === '`') {
        k++;
        while (k < clean.length && clean[k] !== ch) {
          if (clean[k] === '\\') k += 2;
          else k++;
        }
        k++;
        continue;
      }
      if (ch === '(') depth++;
      else if (ch === ')') {
        depth--;
        if (depth === 0) {
          args.push(clean.slice(argStart, k));
          break;
        }
      } else if (ch === ',' && depth === 1) {
        args.push(clean.slice(argStart, k));
        argStart = k + 1;
      }
      k++;
    }
    if (depth === 0) {
      calls.push({ index: match.index, raw: clean.slice(match.index, k + 1).trim(), args });
    }
  }
  return calls;
}

function inwardPathCallViolations(relPath, codeText, baseLine = null) {
  const clean = stripCommentsPreservingLines(codeText);
  const hits = [];
  const lineAt = index => baseLine ?? clean.slice(0, index).split('\n').length;

  const doubleDirname = /\bdirname\s*\(\s*dirname\s*\([^;]*?\bimport\.meta\b|\bdirname\s*\(\s*import\.meta\.dirname\b/g;
  let match;
  while ((match = doubleDirname.exec(clean)) !== null) {
    hits.push(`${relPath}:${lineAt(match.index)}: ${match[0].trim()}`);
  }

  for (const call of parsePathBuilderCalls(clean)) {
    const evaluated = call.args.map(evalStaticStringExpr);
    for (let idx = 0; idx < evaluated.length; idx++) {
      const val = evaluated[idx];
      if (val === null) continue;
      const isParent = val === '..' || val === '../' || val.startsWith('../');
      if (!isParent) continue;
      const earlierMentionsImportMeta = call.args.slice(0, idx).some(a => /\bimport\.meta\b/.test(a));
      if (idx < call.args.length - 1 || (val.startsWith('../') && val.length > 3) || earlierMentionsImportMeta) {
        hits.push(`${relPath}:${lineAt(call.index)}: ${call.raw}`);
        break;
      }
    }
  }
  return hits;
}

function outwardPathCallViolations(relPath, codeText, baseLine = null) {
  const clean = stripCommentsPreservingLines(codeText);
  const hits = [];
  const lineAt = index => baseLine ?? clean.slice(0, index).split('\n').length;

  const evalOutwardSegment = argExpr => {
    const literal = evalStaticStringExpr(argExpr);
    if (literal !== null) return literal;
    if (!/\bimport\.meta\b/.test(argExpr)) return null;
    let dir = posix.dirname(relPath);
    if (
      /\bdirname\s*\(\s*import\.meta\.dirname\b/.test(argExpr)
      || /\bdirname\s*\(\s*dirname\s*\([^)]*\bimport\.meta\.url\b/.test(argExpr)
    ) {
      dir = posix.dirname(dir);
    }
    return dir;
  };

  for (const call of parsePathBuilderCalls(clean)) {
    const segs = call.args.map(evalOutwardSegment);
    let run = [];
    const flushRun = () => {
      if (run.length === 0) return false;
      const joined = posix.normalize(posix.join(...run));
      run = [];
      return (
        joined === 'src/runtime'
        || joined.startsWith('src/runtime/')
        || referencesRuntimeDir(relPath, joined)
      );
    };
    let flagged = false;
    for (const seg of segs) {
      if (seg !== null && seg !== '') {
        run.push(seg);
      } else if (flushRun()) {
        flagged = true;
        break;
      }
    }
    if (!flagged && flushRun()) flagged = true;
    if (flagged) hits.push(`${relPath}:${lineAt(call.index)}: ${call.raw}`);
  }
  return hits;
}

function scannedCandidates(source) {
  const candidates = [];
  const tokens = stringLiterals(source);
  for (const token of tokens) {
    candidates.push({ value: token.value, raw: token.raw, line: token.line, isModuleSpecifier: token.isModuleSpecifier });
    for (const embedded of embeddedModuleSpecifiers(token.value)) {
      candidates.push({ value: embedded, raw: token.raw, line: token.line, isModuleSpecifier: true });
    }
  }
  for (let i = 0; i < tokens.length; i++) {
    if (!tokens[i].standalone) continue;
    let endIdx = i;
    while (
      endIdx + 1 < tokens.length
      && tokens[endIdx + 1].standalone
      && isPlusSeparator(source.slice(tokens[endIdx].end, tokens[endIdx + 1].start))
    ) {
      endIdx++;
    }
    if (endIdx > i) {
      const folded = tokens.slice(i, endIdx + 1).map(t => t.value).join('');
      const raw = source.slice(tokens[i].start, tokens[endIdx].end);
      candidates.push({ value: folded, raw, line: tokens[i].line, isModuleSpecifier: tokens[i].isModuleSpecifier });
      for (const embedded of embeddedModuleSpecifiers(folded)) {
        candidates.push({ value: embedded, raw, line: tokens[i].line, isModuleSpecifier: true });
      }
      i = endIdx;
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
    hits.push(...outwardPathCallViolations(relPath, source));
    for (const item of scannedCandidates(source)) {
      if (referencesRuntimeDir(relPath, item.value)) {
        hits.push(`${relPath}:${item.line}: ${item.raw}`);
      }
      hits.push(...outwardPathCallViolations(relPath, item.value, item.line));
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
  const hits = [...inwardPathCallViolations(relPath, source)];
  for (const item of scannedCandidates(source)) {
    if (referencesOutsideRuntime(relPath, item.value, { isModuleSpecifier: item.isModuleSpecifier })) {
      hits.push(`${relPath}:${item.line}: ${item.raw}`);
    }
    hits.push(...inwardPathCallViolations(relPath, item.value, item.line));
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
  const seamOnlyHostExports = [
    'COMMAND_EXIT_CODE',
    'NO_TESTS',
    'PROMPT_TESTS_LABEL',
    'PROMPT_TESTS_WORDS',
    'STATE_EXIT_CODES',
    'exitCodeFor',
    'exitFor',
    'expectedTestPath',
    'hasAcceptance',
    'isStoryPath',
    'matchTests',
    'orphanSummary',
    'outcomeExitCode',
    'selectTests',
    'whyNoTests',
  ];
  assert.deepEqual(Object.keys(seam).sort(), [...Object.keys(entry), ...seamOnlyHostExports].sort());
  for (const key of seamOnlyHostExports) {
    assert.equal(Object.hasOwn(entry, key), false, `cut host symbol ${key} must not remain on src/runtime/index.mjs`);
  }
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
    ['src/pdd-cli.mjs', "const m = await import('./run' + 'time/runtime-client.mjs');\n"],
    ['src/pdd-cli.mjs', "import(pathToFileURL(join(import.meta.dirname, 'runtime', 'runtime-client.mjs')).href);\n"],
    ['src/pdd-cli.mjs', "import(pathToFileURL(join(dirname(fileURLToPath(import.meta.url)), 'runtime', 'index.mjs')).href);\n"],
    ['src/pdd-cli.mjs', "const p = join(here, 'runtime', 'runtime-client.mjs');\n"],
    ['src/pdd-cli.mjs', "const p = resolve(packageRoot, 'src', 'runtime', 'index.mjs');\n"],
    ['src/pdd-cli.mjs', "execFileSync(process.execPath, ['--input-type=module', '-e', \"import(pathToFileURL(join(import.meta.dirname, 'runtime', 'runtime-client.mjs')).href);\"]);\n"],
    ['bin/pdd.mjs', "import '../src/runtime/index.mjs';\n"],
    ['bin/pdd.mjs', "import(pathToFileURL(join(import.meta.dirname, '..', 'src', 'runtime', 'index.mjs')).href);\n"],
    ['scripts/autopilot-smoke.mjs', "const p = 'src/runtime/runtime-client.mjs';\n"],
    ['scripts/vm-suite.sh', "node src/runtime/runtime-client.mjs\n"],
  ];
  for (const [file, code] of cases) {
    assert.ok(findSeamViolations(file, code).length > 0, `expected violation for ${file}: ${code.trim()}`);
  }
  // Comments, .pdd/runtime, test/runtime/ and prompts/cli/runtime-entry.prompt.md are allowed.
  assert.deepEqual(findSeamViolations('src/workflow-view.mjs', "// Moved to src/runtime/runtime-preflight.mjs\nimport { findTests } from './runtime-seam.mjs';\nconst a = '.pdd/runtime';\nconst b = 'test/runtime/foo.json';\nconst c = 'prompts/cli/runtime-entry.prompt.md';\nconst d = join(env.HOME, '.pdd', 'runtime');\n"), []);
});

const BASE_SRC_CATALOG = [
  'src/agent-adapters.mjs', 'src/agent-config.mjs', 'src/agent-job.mjs', 'src/agent-judge.mjs', 'src/agent-mcp-setup.mjs',
  'src/agent-packet.mjs', 'src/approval-evidence.mjs', 'src/approval-policy.mjs', 'src/argument-parser.mjs', 'src/autopilot-alerts.mjs',
  'src/autopilot-areas.mjs', 'src/autopilot-audit.mjs', 'src/autopilot-base.mjs', 'src/autopilot-cleanup.mjs', 'src/autopilot-core.mjs',
  'src/autopilot-doctor.mjs', 'src/autopilot-environment.mjs', 'src/autopilot-intake.mjs', 'src/autopilot-launcher.mjs', 'src/autopilot-parking.mjs',
  'src/autopilot-regressions.mjs', 'src/autopilot-reports.mjs', 'src/autopilot.mjs', 'src/codex-limits.mjs', 'src/command-catalog.mjs',
  'src/completion.mjs', 'src/contract-refs.mjs', 'src/contracts.mjs', 'src/cost-ledger.mjs', 'src/file-owner.mjs',
  'src/github-calls.mjs', 'src/interface-draft.mjs', 'src/issue-dependencies-github.mjs', 'src/issue-dependencies-intake.mjs', 'src/issue-dependencies.mjs',
  'src/issue-dependency-graph-view.mjs', 'src/issue-dependency-graph.mjs', 'src/issue-mixed.mjs', 'src/issue-sort-github.mjs', 'src/issue-sort.mjs',
  'src/lint-call-preflight.mjs', 'src/machine-resources.mjs', 'src/metrics-capture.mjs', 'src/metrics-command.mjs', 'src/metrics-gap.mjs',
  'src/metrics-hooks.mjs', 'src/metrics-model.mjs', 'src/metrics-store.mjs', 'src/path-diagnostic.mjs', 'src/pdd-cli.mjs',
  'src/product-composition.mjs', 'src/product.mjs', 'src/project-files.mjs', 'src/project-setup.mjs', 'src/prompt-approve.mjs',
  'src/runtime-binding-plan.mjs', 'src/runtime-bindings.mjs', 'src/runtime-check-plan.mjs', 'src/runtime-client.mjs', 'src/runtime-lint-receipt.mjs',
  'src/runtime-markdown.mjs', 'src/runtime-outcome.mjs', 'src/runtime-output.mjs', 'src/runtime-preflight.mjs', 'src/runtime-slots.mjs',
  'src/runtime-workspace.mjs', 'src/scenario-json.mjs', 'src/screen-compare.mjs', 'src/setup-interaction.mjs', 'src/skills-install.mjs',
  'src/svg-layout.mjs', 'src/test-suite-queue.mjs', 'src/toml-string.mjs', 'src/try-doors.mjs', 'src/try-mcp.mjs',
  'src/validation-evidence.mjs', 'src/workflow-agents.mjs', 'src/workflow-areas.mjs', 'src/workflow-chat.mjs', 'src/workflow-github.mjs',
  'src/workflow-herdr-layout.mjs', 'src/workflow-inventory.mjs', 'src/workflow-launch-profile.mjs', 'src/workflow-pr-body.mjs', 'src/workflow-pr-evidence.mjs',
  'src/workflow-prove.mjs', 'src/workflow-replay.mjs', 'src/workflow-results.mjs', 'src/workflow-runner.mjs', 'src/workflow-runs.mjs',
  'src/workflow-setup.mjs', 'src/workflow-small-change.mjs', 'src/workflow-story-card.mjs', 'src/workflow-view.mjs', 'src/workflow-worker-completion.mjs',
  'src/workflow-worktree.mjs',
];

// Recorded base entries from origin/main bce70f621, updated only for the M3 step 2b agent-adapters split
// (moving askAgent to src/runtime/agent-ask.mjs drops agent-packet [5] and preflight [26,55,60,63,66] from entries
// that previously loaded them solely via src/agent-adapters.mjs).
const RECORDED_BASE_ENTRIES = {
  'cli:--help': [0,1,8,24,25,48,49,53,55,61,62,65,68,69,76,77,90],
  'cli:help-topic': [0,1,8,24,25,48,49,53,55,61,62,65,68,69,76,77,90],
  'cli:--version': [0,1,8,24,25,48,49,53,55,61,62,65,68,69,76,77,90],
  'cli:completion': [0,1,8,24,25,48,49,53,55,61,62,65,68,69,76,77,90],
  'cli:setup': [0,1,4,6,8,22,24,25,26,28,30,31,42,44,45,47,48,49,53,55,60,61,62,63,65,66,68,69,72,76,77,78,80,82,89,90,95],
  'cli:files': [0,1,8,24,25,26,48,49,52,53,55,60,61,62,63,65,66,68,69,76,77,90],
  'cli:owner': [0,1,8,24,25,26,29,48,49,53,55,60,61,62,63,65,66,68,69,76,77,90],
  'cli:interface-draft': [0,1,8,24,25,26,31,48,49,53,55,60,61,62,63,65,66,68,69,76,77,90],
  'cli:approve': [0,1,7,8,24,25,26,48,49,53,54,55,60,61,62,63,65,66,68,69,76,77,90],
  'cli:approve-automatic': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:approve-automatic-tests': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:test': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:lint': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:simulate': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:contracts': [0,1,6,7,8,10,12,16,19,22,24,25,26,27,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:contracts-sync': [0,1,6,7,8,10,12,16,19,22,24,25,26,27,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:jobs': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:mcp': [0,1,3,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:metrics': [0,1,6,8,24,25,28,30,42,43,44,45,46,47,48,49,53,55,61,62,65,68,69,72,76,77,78,80,82,89,90,95],
  'cli:graph': [0,1,6,8,10,16,19,22,24,25,28,30,32,34,35,36,37,38,39,41,42,44,45,47,48,49,53,55,61,62,65,68,69,71,72,75,76,77,78,79,80,82,89,90,95],
  'cli:dependencies-prepare': [0,1,6,8,10,16,19,22,24,25,28,30,32,33,34,37,38,39,41,42,44,45,47,48,49,53,55,61,62,65,68,69,71,72,75,76,77,78,79,80,82,89,90,95],
  'cli:dependencies-complete': [0,1,6,8,10,16,19,22,24,25,28,30,32,33,34,37,38,39,41,42,44,45,47,48,49,53,55,61,62,65,68,69,71,72,75,76,77,78,79,80,82,89,90,95],
  'cli:product-status': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:product-next': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:product-start': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:workflow-list': [0,1,8,24,25,48,49,53,55,61,62,65,68,69,76,77,90],
  'cli:workflow-status': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,32,34,37,38,39,41,42,44,45,47,48,49,53,54,55,57,60,61,62,63,65,66,68,69,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:workflow-run': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,32,34,37,38,39,41,42,44,45,47,48,49,53,54,55,57,60,61,62,63,65,66,68,69,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:workflow-done': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,32,34,37,38,39,41,42,44,45,47,48,49,53,54,55,57,60,61,62,63,65,66,68,69,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:workflow-view': [0,1,6,7,8,24,25,26,28,29,42,44,45,47,48,49,53,55,57,60,61,62,63,65,66,68,69,72,76,77,78,80,82,84,85,87,89,90,93,95],
  'cli:workflow-cost': [0,1,6,7,8,10,12,16,19,22,24,25,26,28,29,30,32,34,37,38,39,41,42,44,45,47,48,49,53,54,55,57,60,61,62,63,65,66,68,69,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:workflow-prove': [0,1,6,8,24,25,28,42,44,45,47,48,49,53,55,61,62,65,68,69,72,76,77,78,80,82,85,89,90,95],
  'cli:autopilot-status': [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,21,22,23,24,25,26,28,29,30,31,32,33,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:autopilot-doctor': [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,21,22,23,24,25,26,28,29,30,31,32,33,34,37,38,39,40,41,42,44,45,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:autopilot-regressions': [0,1,8,20,24,25,28,30,48,49,53,55,61,62,65,68,69,76,77,90,95],
  'cli:autopilot-alerts': [0,1,6,7,8,9,10,12,16,19,22,24,25,26,28,29,30,32,34,37,38,39,41,42,44,45,47,48,49,53,54,55,57,60,61,62,63,65,66,68,69,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,94,95],
  'cli:autopilot-off': [0,1,8,22,24,25,28,30,48,49,53,55,61,62,65,68,69,76,77,90],
  'child:workflow-worker-completion': [0,1,6,28,42,44,45,47,65,72,76,78,80,82,89,94,95],
  'child:workflow-replay-selector': [26,55,60,63,65,66],
  'child:try-doors-launcher': [0,1,6,7,10,12,16,19,22,24,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,50,51,54,55,56,57,58,59,60,61,62,63,64,65,66,67,70,71,72,73,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,91,92,94,95],
  'child:scripts/autopilot-smoke.mjs': [],
  'child:scripts/route-runtime-issues.mjs': [],
  'tick:autopilot-launcher': [0,1,2,6,7,9,10,11,12,13,14,15,16,17,18,19,21,22,23,24,26,28,29,30,31,32,33,34,37,38,39,40,41,42,44,45,47,48,50,51,54,55,56,57,58,59,60,61,62,63,64,65,66,67,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,91,92,94,95],
  'lib:svg-layout.mjs': [65,70],
  'lib:prompt-approve.mjs': [7,26,54,55,60,63,65,66],
  'lib:file-owner.mjs': [26,29,55,60,63,65,66],
  'lib:agent-adapters.mjs': [0,1,65],
  'lib:product.mjs': [0,1,6,7,10,12,16,19,22,24,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,50,51,54,55,56,57,58,59,60,61,62,63,64,65,66,67,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,91,92,94,95],
  'lib:autopilot-doctor.mjs': [0,1,6,7,10,12,15,16,19,22,23,24,26,28,29,30,31,32,34,37,38,39,40,41,42,44,45,47,50,51,54,55,56,57,58,59,60,61,62,63,64,65,66,67,70,71,72,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,91,92,94,95],
};

test('SEAM5 (R2-3): every CLI command family, child entry, Autopilot tick and library entry matches recorded base module sets, cycles and guarded load failures', async t => {
  const { execFile, execFileSync, spawnSync } = await import('node:child_process');
  const { chmodSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const { relative, sep } = await import('node:path');
  const { pathToFileURL } = await import('node:url');
  const { promisify } = await import('node:util');
  const { PUBLIC_COMMAND_ROUTES } = await import('../src/command-catalog.mjs');

  const execFileAsync = promisify(execFile);
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-seam5-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));

  const home = join(scratch, 'home');
  const stateDir = join(scratch, 'state');
  const nonGit = join(scratch, 'nongit');
  const repo = join(scratch, 'repo');
  const fakeBin = join(scratch, 'bin');
  for (const d of [home, stateDir, nonGit, join(repo, 'prompts'), join(repo, 'user_stories'), join(repo, 'tests'), fakeBin]) {
    mkdirSync(d, { recursive: true });
  }
  for (const tool of ['gh', 'claude', 'gemini', 'agy', 'herdr']) {
    const p = join(fakeBin, tool);
    writeFileSync(p, '#!/bin/sh\nexit 1\n');
    chmodSync(p, 0o755);
  }
  writeFileSync(join(fakeBin, 'codex'), '#!/bin/sh\nif [ "$1" = "login" ]; then echo "Logged in"; exit 0; fi\nexit 1\n');
  chmodSync(join(fakeBin, 'codex'), 0o755);
  writeFileSync(join(repo, 'prompts/a.prompt.md'), '# A\n\nDo a.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'user_stories/a.md'), '# A\n\nI can a.\n\n## Acceptance criteria\n\n1. A.\n');
  writeFileSync(
    join(repo, 'tests/a.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/a.md',
      criteria: [{ id: 'AC1', text: 'A.' }],
      initial_world: {},
      steps: [{ step_id: 's1', entry_path: 'prompts/a.prompt.md', operation: 'a', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 1 }] }],
    }) + '\n',
  );
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=T', '-c', 'user.email=t@e.c', 'commit', '-q', '-m', 'init'], { cwd: repo });

  const preload = join(scratch, 'hook.mjs');
  writeFileSync(
    preload,
    `import { registerHooks } from 'node:module';
import { appendFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
const out = process.env.PROBE_OUT;
registerHooks({
  resolve(specifier, context, nextResolve) {
    const res = nextResolve(specifier, context);
    if (res.url && res.url.startsWith('file://')) {
      const parent = context.parentURL && context.parentURL.startsWith('file://') ? fileURLToPath(context.parentURL) : '';
      appendFileSync(out, parent + '\\t' + fileURLToPath(res.url) + '\\n');
    }
    return res;
  }
});\n`,
  );

  const ALLOWED_BASE_CYCLES = new Set([
    'src/issue-sort-github.mjs <-> src/issue-sort.mjs',
    'src/issue-mixed.mjs <-> src/issue-sort-github.mjs <-> src/issue-sort.mjs',
    'src/runtime/runtime-client.mjs <-> src/runtime/runtime-slots.mjs',
    'src/runtime/interface-draft.mjs <-> src/runtime/runtime-bindings.mjs <-> src/runtime/runtime-client.mjs <-> src/runtime/runtime-slots.mjs',
    'src/toml-string.mjs <-> src/workflow-herdr-layout.mjs',
  ]);

  const findTarjanCycles = adj => {
    let idx = 0;
    const indices = new Map();
    const low = new Map();
    const stack = [];
    const onStack = new Set();
    const cycles = [];
    const strong = v => {
      indices.set(v, idx);
      low.set(v, idx);
      idx++;
      stack.push(v);
      onStack.add(v);
      for (const w of adj.get(v) ?? []) {
        if (!indices.has(w)) {
          strong(w);
          low.set(v, Math.min(low.get(v), low.get(w)));
        } else if (onStack.has(w)) {
          low.set(v, Math.min(low.get(v), indices.get(w)));
        }
      }
      if (low.get(v) === indices.get(v)) {
        const scc = [];
        let w;
        do {
          w = stack.pop();
          onStack.delete(w);
          scc.push(w);
        } while (w !== v);
        if (scc.length > 1) cycles.push(scc.sort().join(' <-> '));
      }
    };
    for (const v of adj.keys()) {
      if (!indices.has(v)) strong(v);
    }
    return cycles.sort();
  };

  // 1. Static ESM import/re-export graph across all src/ and src/runtime/ files (including src/runtime-seam.mjs and src/runtime/index.mjs).
  const staticAdj = new Map();
  for (const rel of walk('src').filter(f => f.endsWith('.mjs'))) {
    const clean = stripCommentsPreservingLines(readFileSync(join(root, rel), 'utf8'));
    const edges = new Set();
    const staticRe = /\b(?:import|export)\s+(?:[^'"]*?\bfrom\s*)?(['"])([^'"]+)\1/g;
    let m;
    while ((m = staticRe.exec(clean)) !== null) {
      const spec = decodeJsEscapes(m[2]);
      if (!spec.startsWith('./') && !spec.startsWith('../')) continue;
      const target = posix.normalize(posix.join(posix.dirname(rel), spec));
      if (target.startsWith('src/') && target.endsWith('.mjs') && target !== rel) edges.add(target);
    }
    staticAdj.set(rel, edges);
  }
  const novelStaticCycles = findTarjanCycles(staticAdj).filter(c => !ALLOWED_BASE_CYCLES.has(c));
  assert.deepEqual(novelStaticCycles, [], `unexpected new static import cycle: ${novelStaticCycles.join('; ')}`);

  const ASYNC_SEAM_BRIDGE_PROBES = new Set([
    'cli:approve-automatic', 'cli:approve-automatic-tests',
    'cli:test', 'cli:lint', 'cli:simulate', 'cli:contracts', 'cli:contracts-sync',
    'cli:jobs', 'cli:mcp', 'child:try-doors-launcher',
  ]);

  const analyzeProbeLines = (lines, { ignoreAsyncSeamOutgoing = false } = {}) => {
    const out = new Set();
    const adj = new Map();
    const toRel = full => {
      if (!full) return null;
      const rel = relative(root, full).split(sep).join('/');
      return rel.startsWith('src/') && rel.endsWith('.mjs') ? rel : null;
    };
    for (const line of lines) {
      const tab = line.indexOf('\t');
      const parentRel = tab >= 0 ? toRel(line.slice(0, tab)) : null;
      const targetFull = tab >= 0 ? line.slice(tab + 1) : line;
      let rel = toRel(targetFull);
      if (!rel) continue;
      if (parentRel && parentRel !== rel && !(ignoreAsyncSeamOutgoing && parentRel === 'src/runtime-seam.mjs' && !rel.startsWith('src/runtime/'))) {
        if (!adj.has(parentRel)) adj.set(parentRel, new Set());
        adj.get(parentRel).add(rel);
      }
      if (
        rel === 'src/runtime-seam.mjs' ||
        rel === 'src/runtime/index.mjs' ||
        rel === 'src/runtime/secret-redaction.mjs' ||
        rel === 'src/secret-redaction.mjs' ||
        rel === 'src/product-documents.mjs' ||
        rel === 'src/workflow-eligibility.mjs' ||
        rel === 'src/test-selection.mjs' ||
        rel === 'src/runtime-exit.mjs' ||
        rel === 'src/prompt-tests-words.mjs'
      ) continue;
      if (rel === 'src/runtime/agent-ask.mjs') rel = 'src/agent-adapters.mjs';
      if (rel.startsWith('src/runtime/')) rel = `src/${rel.slice('src/runtime/'.length)}`;
      out.add(rel);
    }
    return { loaded: [...out].sort(), cycles: findTarjanCycles(adj) };
  };

  let seq = 0;
  const runProbe = async (key, args, cwd) => {
    const outFile = join(scratch, `out-${++seq}.txt`);
    writeFileSync(outFile, '');
    const child = execFileAsync(process.execPath, ['--import', pathToFileURL(preload).href, ...args], {
      cwd,
      env: {
        PATH: `${fakeBin}:/usr/bin:/bin`,
        HOME: home,
        PDD_STATE_DIR: stateDir,
        PDD_RUNTIME_URL: 'http://127.0.0.1:9',
        PROBE_OUT: outFile,
      },
      timeout: 8000,
    });
    child.child.stdin?.end();
    try { await child; } catch {}
    const lines = readFileSync(outFile, 'utf8').split('\n').filter(Boolean);
    return analyzeProbeLines(lines, { ignoreAsyncSeamOutgoing: ASYNC_SEAM_BRIDGE_PROBES.has(key) });
  };

  // Every route local in PUBLIC_COMMAND_ROUTES must map to a probed switch arm.
  const coveredLocals = new Set([
    'help', 'version', 'completion', 'setup', 'project-files', 'file-owner', 'interface-draft', 'prompt-approve',
    'runtime-check', 'runtime-try', 'contracts', 'contracts-sync', 'runtime-jobs', 'mcp', 'metrics',
    'issue-dependency-graph', 'dependencies-prepare', 'dependencies-complete',
    'product-status', 'product-next', 'product-start',
    'workflow-list', 'workflow-status', 'workflow-run', 'workflow-done', 'workflow-ask', 'workflow-request-uptake',
    'workflow-approve', 'workflow-resend', 'workflow-card', 'workflow-changes', 'workflow-open', 'workflow-view',
    'workflow-cost', 'workflow-prove', 'workflow-suite', 'workflow-evidence', 'workflow-evidence-associate',
    'workflow-park', 'workflow-yield', 'workflow-cancel', 'workflow-tidy',
    'autopilot-status', 'autopilot-doctor', 'autopilot-regressions', 'autopilot-alerts', 'autopilot-alert',
    'autopilot-start', 'autopilot-stop', 'autopilot-add', 'autopilot-release', 'autopilot-report',
    'autopilot-intake', 'autopilot-audit', 'autopilot-check-base',
    'autopilot.off', 'autopilot.observe', 'autopilot.auto', 'autopilot-trust', 'autopilot-untrust',
  ]);
  for (const route of PUBLIC_COMMAND_ROUTES) {
    assert.ok(coveredLocals.has(route.local), `PUBLIC_COMMAND_ROUTES local ${route.local} (${route.id}) must be covered in SEAM5`);
  }

  const bin = join(root, 'bin/pdd.mjs');
  const replayChildExpr = 'source.identity({root:process.argv[1],tests:JSON.parse(process.argv[2])}).files';
  assert.ok(
    readFileSync(join(root, 'src/workflow-replay.mjs'), 'utf8').includes(replayChildExpr),
    'SEAM5 replayScript must match src/workflow-replay.mjs selectedFiles child expression',
  );
  const replayScript = `import {source} from ${JSON.stringify(pathToFileURL(join(root, 'src/runtime-seam.mjs')).href)};process.stdout.write(JSON.stringify(${replayChildExpr}));`;
  const launcherScript = 'import(process.argv[1]).then(async ({ runShim }) => { process.exitCode = await runShim(process.argv[2], process.argv.slice(3)); }).catch(() => { process.exitCode = 125; });';
  const probes = [
    ['cli:--help', [bin, '--help'], repo],
    ['cli:help-topic', [bin, 'help', 'prompting'], repo],
    ['cli:--version', [bin, '--version'], repo],
    ['cli:completion', [bin, 'completion', 'bash'], repo],
    ['cli:setup', [bin, 'setup', '--yes'], repo],
    ['cli:files', [bin, 'files', '--json'], repo],
    ['cli:owner', [bin, 'owner', 'prompts/a.prompt.md', '--json'], repo],
    ['cli:interface-draft', [bin, 'interface', 'draft', 'prompts/a.prompt.md', '--json'], repo],
    ['cli:approve', [bin, 'approve', 'prompts/missing.prompt.md', '--said', 'ok'], repo],
    ['cli:approve-automatic', [bin, 'approve', 'prompts/a.prompt.md', '--automatic'], repo],
    ['cli:approve-automatic-tests', [bin, 'approve', 'prompts/a.prompt.md', '--automatic', '--tests', 'npm test'], repo],
    ['cli:test', [bin, 'test', 'a'], repo],
    ['cli:lint', [bin, 'lint', '--local'], repo],
    ['cli:simulate', [bin, 'simulate', '--stop', 'a'], repo],
    ['cli:contracts', [bin, 'contracts'], repo],
    ['cli:contracts-sync', [bin, 'contracts', 'sync'], repo],
    ['cli:jobs', [bin, 'jobs'], repo],
    ['cli:mcp', [bin, 'mcp'], repo],
    ['cli:metrics', [bin, 'metrics', '--json'], repo],
    ['cli:graph', [bin, 'graph', '--issue', '1'], nonGit],
    ['cli:dependencies-prepare', [bin, 'dependencies', 'prepare'], nonGit],
    ['cli:dependencies-complete', [bin, 'dependencies', 'complete', '--input', '-'], nonGit],
    ['cli:product-status', [bin, 'product', 'status'], repo],
    ['cli:product-next', [bin, 'product', 'next'], repo],
    ['cli:product-start', [bin, 'product', 'start', 'r1', '--no-run'], repo],
    ['cli:workflow-list', [bin, 'workflow', 'list'], repo],
    ['cli:workflow-status', [bin, 'workflow', 'status'], repo],
    ['cli:workflow-run', [bin, 'workflow', 'run', 'feature', '1'], nonGit],
    ['cli:workflow-done', [bin, 'workflow', 'done', 'story'], nonGit],
    ['cli:workflow-view', [bin, 'workflow', 'view', '1'], nonGit],
    ['cli:workflow-cost', [bin, 'workflow', 'cost', '1'], nonGit],
    ['cli:workflow-prove', [bin, 'workflow', 'prove', '1', '--test', 'true', '--expect', 'ok'], nonGit],
    ['cli:autopilot-status', [bin, 'autopilot', 'status'], nonGit],
    ['cli:autopilot-doctor', [bin, 'autopilot', 'doctor'], repo],
    ['cli:autopilot-regressions', [bin, 'autopilot', 'regressions'], nonGit],
    ['cli:autopilot-alerts', [bin, 'autopilot', 'alerts', 'clear'], nonGit],
    ['cli:autopilot-off', [bin, 'autopilot', 'off'], nonGit],
    ['child:workflow-worker-completion', [join(root, 'src/workflow-worker-completion.mjs'), '{}'], nonGit],
    ['child:workflow-replay-selector', ['--input-type=module', '-e', replayScript, repo, JSON.stringify(['tests/a.json'])], nonGit],
    ['child:try-doors-launcher', ['--input-type=commonjs', '-e', launcherScript, '--', pathToFileURL(join(root, 'src/try-doors.mjs')).href, join(scratch, 'missing.door.json')], nonGit],
    ['child:scripts/autopilot-smoke.mjs', [join(root, 'scripts/autopilot-smoke.mjs')], nonGit],
    ['child:scripts/route-runtime-issues.mjs', [join(root, 'scripts/route-runtime-issues.mjs')], nonGit],
    ['tick:autopilot-launcher', [join(root, 'src/autopilot-launcher.mjs'), join(scratch, 'missing-state.json')], nonGit],
    ['lib:svg-layout.mjs', ['--input-type=module', '-e', `await import(${JSON.stringify(pathToFileURL(join(root, 'src/svg-layout.mjs')).href)})`], nonGit],
    ['lib:prompt-approve.mjs', ['--input-type=module', '-e', `await import(${JSON.stringify(pathToFileURL(join(root, 'src/prompt-approve.mjs')).href)})`], nonGit],
    ['lib:file-owner.mjs', ['--input-type=module', '-e', `await import(${JSON.stringify(pathToFileURL(join(root, 'src/file-owner.mjs')).href)})`], nonGit],
    ['lib:agent-adapters.mjs', ['--input-type=module', '-e', `await import(${JSON.stringify(pathToFileURL(join(root, 'src/agent-adapters.mjs')).href)})`], nonGit],
    ['lib:product.mjs', ['--input-type=module', '-e', `await import(${JSON.stringify(pathToFileURL(join(root, 'src/product.mjs')).href)})`], nonGit],
    ['lib:autopilot-doctor.mjs', ['--input-type=module', '-e', `await import(${JSON.stringify(pathToFileURL(join(root, 'src/autopilot-doctor.mjs')).href)})`], nonGit],
  ];

  const ACYCLIC_ENTRIES = new Set([
    'cli:--help', 'cli:owner', 'cli:files', 'cli:approve', 'cli:interface-draft',
    'child:workflow-replay-selector', 'lib:svg-layout.mjs', 'lib:prompt-approve.mjs',
    'lib:file-owner.mjs', 'lib:agent-adapters.mjs',
  ]);
  for (let i = 0; i < probes.length; i += 8) {
    const chunk = probes.slice(i, i + 8);
    const probeBatch = await Promise.all(chunk.map(([key, args, cwd]) => runProbe(key, args, cwd)));
    chunk.forEach(([key], idx) => {
      const expected = RECORDED_BASE_ENTRIES[key].map(n => BASE_SRC_CATALOG[n]);
      const { loaded, cycles } = probeBatch[idx];
      assert.deepEqual(loaded, expected, `loaded modules mismatch for ${key}`);
      if (ACYCLIC_ENTRIES.has(key)) {
        assert.deepEqual(cycles, [], `expected zero import cycles for ${key}`);
      } else {
        const novel = cycles.filter(c => !ALLOWED_BASE_CYCLES.has(c));
        assert.deepEqual(novel, [], `unexpected new import cycle for ${key}: ${novel.join('; ')}`);
      }
    });
  }

  // Guarded load failures must not escape try/catch, and light/leaf entries must not depend on unrelated leaves.
  const runWithRejectedModule = (rejectSuffix, entryArgs, cwd = nonGit) => {
    const hook = `import { registerHooks } from 'node:module'; registerHooks({ resolve(s, c, n) { const r = n(s, c); if (r.url && r.url.endsWith(${JSON.stringify(rejectSuffix)})) throw new Error('REVIEW_LOAD_FAILURE'); return r; } });`;
    return spawnSync(process.execPath, ['--import', `data:text/javascript,${encodeURIComponent(hook)}`, ...entryArgs], {
      cwd,
      env: {
        PATH: `${fakeBin}:/usr/bin:/bin`,
        HOME: home,
        PDD_STATE_DIR: stateDir,
        PDD_RUNTIME_URL: 'http://127.0.0.1:9',
      },
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
  };

  assert.equal(runWithRejectedModule('/runtime-client.mjs', [bin, '--help']).status, 0);

  for (const suffix of ['/workflow-runner.mjs', '/product.mjs', '/screen-compare.mjs', '/runtime-client.mjs']) {
    for (const extraArgs of [['--automatic', '--tests', 'node --test x.mjs'], ['--automatic']]) {
      const approveFail = runWithRejectedModule(suffix, [bin, 'approve', 'prompts/a.prompt.md', ...extraArgs], repo);
      assert.equal(approveFail.status, 4, `approve ${extraArgs.join(' ')} (${suffix}) expected exit 4, got ${approveFail.status}: ${approveFail.stderr}`);
      assert.equal(approveFail.stdout, '');
      assert.equal(approveFail.stderr, 'REVIEW_LOAD_FAILURE\n');
    }
  }

  for (const [cmdArgs, suffix] of [
    [['test', 'a'], '/workflow-runner.mjs'],
    [['simulate', '--stop', 'a'], '/prompt-approve.mjs'],
  ]) {
    const checkOrTryFail = runWithRejectedModule(suffix, [bin, ...cmdArgs], repo);
    assert.equal(checkOrTryFail.status, 3);
    assert.equal(
      checkOrTryFail.stderr.trim(),
      'pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again. Reason: REVIEW_LOAD_FAILURE',
    );
  }

  for (const suffix of ['/runtime-client.mjs', '/workflow-runner.mjs']) {
    const mcpFail = runWithRejectedModule(suffix, [bin, 'mcp']);
    assert.equal(mcpFail.status, 1);
    assert.equal(mcpFail.stderr.trim(), 'pdd mcp could not start. Reason: REVIEW_LOAD_FAILURE');
  }
  for (const suffix of ['/runtime-client.mjs', '/product.mjs']) {
    const jobsFail = runWithRejectedModule(suffix, [bin, 'jobs']);
    assert.equal(jobsFail.status, 5);
    assert.equal(jobsFail.stderr.trim(), 'Local interpreter jobs could not be read. Reason: REVIEW_LOAD_FAILURE');
    const contractsFail = runWithRejectedModule(suffix, [bin, 'contracts']);
    assert.equal(contractsFail.status, 5);
    assert.equal(contractsFail.stderr.trim(), 'Local contracts could not be read. Reason: REVIEW_LOAD_FAILURE');
  }
  const setupFail = runWithRejectedModule('/interface-draft.mjs', [bin, 'setup', '--yes'], repo);
  assert.equal(setupFail.status, 1);
  assert.match(setupFail.stderr, /Interface drafts: REVIEW_LOAD_FAILURE/);

  const launcherFailScript = 'import(process.argv[1]).then(async ({ runShim }) => { process.exitCode = await runShim(process.argv[2], process.argv.slice(3)); }).catch(() => { process.stderr.write("pdd: The installed adapter could not load. Run pdd simulate STORY --cli again.\\n"); process.exitCode = 125; });';
  const launcherFail = runWithRejectedModule(
    '/product.mjs',
    ['--input-type=commonjs', '-e', launcherFailScript, '--', pathToFileURL(join(root, 'src/try-doors.mjs')).href, join(scratch, 'missing.door.json')],
  );
  assert.equal(launcherFail.status, 125);
  assert.equal(launcherFail.stderr, 'pdd: The installed adapter could not load. Run pdd simulate STORY --cli again.\n');

  assert.equal(
    runWithRejectedModule('/runtime-output.mjs', ['--input-type=module', '-e', `await import(${JSON.stringify(pathToFileURL(join(root, 'src/svg-layout.mjs')).href)})`]).status,
    0,
  );
  assert.equal(runWithRejectedModule('/runtime-output.mjs', [join(root, 'src/workflow-worker-completion.mjs'), '{}']).status, 0);
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
    ['src/runtime/runtime-client.mjs', "const p = join(dirname(dirname(fileURLToPath(import.meta.url))), 'workflow-runner.mjs');\n"],
    ['src/runtime/runtime-client.mjs', "const p = join(here, '..', 'x.mjs');\n"],
    ['src/runtime/runtime-client.mjs', "const p = '.' + './x.mjs';\n"],
    ['src/runtime/runtime-client.mjs', "const p = '\\x2e./x.mjs';\n"],
    ['src/runtime/runtime-client.mjs', "const child = \"import {allRuns} from '../workflow-runs.mjs'\";\n"],
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

test('SEAM11 (M2-2): src/runtime has no hardcoded client version literal; seam supplies package.json version and direct callers get null', async t => {
  const seam = await import('../src/runtime-seam.mjs');
  const directClient = await import('../src/runtime/runtime-client.mjs');
  const { harbor, fakeRuntime, portsFor } = await import('./runtime-fake.mjs');

  for (const rel of walk('src/runtime')) {
    const src = readFileSync(join(root, rel), 'utf8');
    assert.ok(!src.includes('DEFAULT_CLIENT_VERSION'), `${rel} must not define DEFAULT_CLIENT_VERSION`);
    if (rel !== 'src/runtime/try-mcp.mjs') {
      assert.ok(!/['"`]0\.1\.\d+['"`]/.test(src), `${rel} must not contain a hardcoded 0.1.x version literal`);
    }
  }

  const pkgVersion = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8')).version;
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));

  const seenSeam = [];
  const seamPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin },
    {
      cacheHash: bytes => {
        try {
          const parsed = JSON.parse(Buffer.from(bytes).toString('utf8'));
          if (Object.hasOwn(parsed, 'pdd_version')) seenSeam.push(parsed.pdd_version);
        } catch { /* non-fingerprint hash */ }
        return seam.sha256(bytes);
      },
    },
  ).ports;
  const seamCode = await seam.runCheck({ cwd: setup.repo, words: ['place-order'], options: {}, cache: true }, seamPorts);
  assert.equal(seamCode, 0, seamPorts.stderr.text);
  assert.ok(seenSeam.length > 0 && seenSeam.every(v => v === pkgVersion), `expected seam pdd_version=${pkgVersion}, got ${JSON.stringify(seenSeam)}`);

  const seenDirect = [];
  const hostSelection = await import('../src/test-selection.mjs');
  const hostExit = await import('../src/runtime-exit.mjs');
  const directPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin },
    {
      ...hostSelection,
      noTestsMessage: hostSelection.NO_TESTS,
      exitFor: hostExit.exitFor,
      exitCodeFor: hostExit.exitCodeFor,
      cacheHash: bytes => {
        try {
          const parsed = JSON.parse(Buffer.from(bytes).toString('utf8'));
          if (Object.hasOwn(parsed, 'pdd_version')) seenDirect.push(parsed.pdd_version);
        } catch { /* non-fingerprint hash */ }
        return seam.sha256(bytes);
      },
    },
  ).ports;
  const directCode = await directClient.runCheck({ cwd: setup.repo, words: ['place-order'], options: {}, cache: true }, directPorts);
  assert.equal(directCode, 0, directPorts.stderr.text);
  assert.ok(seenDirect.length > 0 && seenDirect.every(v => v === null), `expected direct pdd_version=null, got ${JSON.stringify(seenDirect)}`);
});

test('SEAM12 (MERGE-1): runtime-check-plan keeps approved prompt unchanged and direct buildCheckPlan parses Generated-from headers without ports.headerPrompts', async t => {
  const { execFileSync } = await import('node:child_process');
  const { mkdirSync, mkdtempSync, rmSync, unlinkSync, writeFileSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const { buildCheckPlan } = await import('../src/runtime/runtime-check-plan.mjs');
  const { findTests: rawFindTests, interfaceBlocks, proseSha256 } = await import('../src/runtime/runtime-preflight.mjs');
  const selectionPorts = await import('../src/test-selection.mjs');

  const promptText = readFileSync(join(root, 'prompts/cli/runtime-check-plan.prompt.md'), 'utf8');
  const blocks = interfaceBlocks(promptText);
  assert.equal(blocks.length, 1);
  const iface = JSON.parse(blocks[0][1]);
  assert.equal(iface.status, 'approved');
  assert.equal(iface.prose_sha256, proseSha256(promptText));

  const tmp = mkdtempSync(join(tmpdir(), 'pdd-merge1-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));
  const repo = join(tmp, 'repo');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });
  execFileSync('git', ['init', '-q'], { cwd: repo });

  for (const name of ['alpha', 'beta']) {
    const entryIface = {
      status: 'draft',
      prose_sha256: '',
      entries: [{
        operation: 'run',
        input_schema: { type: 'object', properties: { x: { type: 'number' } }, required: ['x'], additionalProperties: false },
        result_schema: { type: 'object', properties: { y: { type: 'number' } }, required: ['y'], additionalProperties: false },
        errors: [],
      }],
      calls: [],
      resources: [],
      limits: { max_steps: 1, max_model_calls: 1 },
    };
    const body = () => `# ${name}\n\nCompute ${name}.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(entryIface)}\n\`\`\`\n</details>\n`;
    entryIface.prose_sha256 = proseSha256(body());
    writeFileSync(join(repo, `prompts/${name}.prompt.md`), body());
    writeFileSync(join(repo, `src/${name}.mjs`), `// Generated from prompts/${name}.prompt.md\nexport const ${name} = x => ({ y: x });\n`);
    writeFileSync(join(repo, `user_stories/${name}.md`), `# ${name}\n\nI can run ${name}.\n\n## Acceptance criteria\n\n1. ${name} works.\n`);
    writeFileSync(
      join(repo, `tests/${name}.json`),
      JSON.stringify({
        schema_version: 'prompt-runtime.program-scenario.v1',
        story_path: `user_stories/${name}.md`,
        criteria: [{ id: 'AC1', text: `${name} works.` }],
        initial_world: {},
        steps: [{ step_id: 's1', entry_path: `prompts/${name}.prompt.md`, operation: 'run', input: { x: 1 }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/y', op: 'equals', value: 1 }] }],
      }, null, 2) + '\n',
    );
  }
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'base'], { cwd: repo });

  // Modify only src/alpha.mjs and call buildCheckPlan directly WITHOUT ports.headerPrompts.
  writeFileSync(join(repo, 'src/alpha.mjs'), '// Generated from prompts/alpha.prompt.md\nexport const alpha = x => ({ y: x + 1 });\n');
  const found = rawFindTests({ root: repo }, selectionPorts);
  const rows = found.tests.map(test => ({ test: test.path, state: 'passed', steps: [] }));
  const planEdited = buildCheckPlan({ root: repo, found, selected: found.tests, rows, full: true, base: 'HEAD' }, selectionPorts);
  const alphaStory = planEdited.stories.find(s => s.story_path === 'user_stories/alpha.md');
  const betaStory = planEdited.stories.find(s => s.story_path === 'user_stories/beta.md');
  assert.equal(alphaStory?.role, 'target');
  assert.deepEqual(alphaStory?.affected_paths, ['src/alpha.mjs']);
  assert.equal(betaStory?.role, 'baseline');

  // Delete src/beta.mjs while src/alpha.mjs is edited: deleted implementation reads base Generated-from header.
  unlinkSync(join(repo, 'src/beta.mjs'));
  const planDeleted = buildCheckPlan({ root: repo, found, selected: found.tests, rows, full: true, base: 'HEAD' }, selectionPorts);
  const betaDeleted = planDeleted.stories.find(s => s.story_path === 'user_stories/beta.md');
  assert.equal(betaDeleted?.role, 'target');
  assert.deepEqual(betaDeleted?.affected_paths, ['src/beta.mjs']);
});

test('SEAM13 (WEAKER DEFAULTS): agent-project has no localEvidenceEligibility fallback, and unbound host ports fail loudly', async t => {
  const { execFileSync } = await import('node:child_process');
  const { mkdirSync, mkdtempSync, rmSync, writeFileSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const seam = await import('../src/runtime-seam.mjs');
  const directProject = await import('../src/runtime/agent-project.mjs');
  const directComposition = await import('../src/runtime/product-composition.mjs');
  const directClient = await import('../src/runtime/runtime-client.mjs');
  const directPreflight = await import('../src/runtime/runtime-preflight.mjs');
  const hostSelection = await import('../src/test-selection.mjs');
  const hostExit = await import('../src/runtime-exit.mjs');
  const baseCutPorts = {
    ...hostSelection,
    noTestsMessage: hostSelection.NO_TESTS,
    exitFor: hostExit.exitFor,
    exitCodeFor: hostExit.exitCodeFor,
  };
  const { harbor, fakeRuntime, portsFor } = await import('./runtime-fake.mjs');

  const agentProjectSrc = readFileSync(join(root, 'src/runtime/agent-project.mjs'), 'utf8');
  assert.ok(!agentProjectSrc.includes('localEvidenceEligibility'), 'agent-project.mjs must not keep localEvidenceEligibility');

  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
  const checkCode = await seam.runCheck({ cwd: setup.repo, words: ['place-order'], options: {} }, portsFor(env).ports);
  assert.equal(checkCode, 0);

  // Direct buildProjectCard without evidenceEligibility reports unavailable (latestCheck: null), while seam binds workflow eligibility.
  const directCard = directProject.buildProjectCard({ root: setup.repo, env, story: 'place-order' });
  assert.equal(directCard.latestCheck, null);
  const seamCard = seam.buildProjectCard({ root: setup.repo, env, story: 'place-order' });
  assert.notEqual(seamCard.latestCheck, null);

  // Direct preflight/client calls without M3 selection or exit ports fail loudly with unbound-port Errors.
  assert.throws(
    () => directPreflight.findTests({ root: setup.repo }),
    err => !(err instanceof TypeError) && /Test selection ports.*not bound/.test(err.message),
  );
  await assert.rejects(
    () => directClient.runCheck({ cwd: setup.repo, words: ['place-order'], options: {} }, portsFor(env).ports),
    err => !(err instanceof TypeError) && /Test selection ports.*not bound/.test(err.message),
  );
  await assert.rejects(
    () => directClient.runCheck({ cwd: setup.repo, words: ['place-order'], options: {} }, { ...portsFor(env).ports, ...hostSelection, noTestsMessage: hostSelection.NO_TESTS }),
    err => !(err instanceof TypeError) && /Exit code port.*not bound/.test(err.message),
  );

  // Direct composeProductTry without product parser ports throws an unbound-port Error, not invalid-product-map or TypeError.
  assert.throws(
    () => directComposition.composeProductTry({ root: '/project' }, {}),
    err => !(err instanceof TypeError) && err.code !== 'invalid-product-map' && /port.*not bound/i.test(err.message),
  );

  // Direct runCheck --screen without compareScreen throws an unbound-port Error instead of masking as browser failure.
  await assert.rejects(
    () => directClient.runCheck(
      { cwd: setup.repo, words: [], options: { '--screen': 'https://example.test', '--drawing': 'prompts/x.ui.svg' } },
      { env, stdout: { write() {} }, stderr: { write() {} } },
    ),
    err => !(err instanceof TypeError) && /Screen comparison ports.*not bound/.test(err.message),
  );

  // Direct runCheck --lint on a native-only Story without native assessment ports throws an unbound-port Error.
  const tmp = mkdtempSync(join(tmpdir(), 'pdd-native-unbound-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));
  const nativeRepo = join(tmp, 'repo');
  mkdirSync(join(nativeRepo, 'prompts'), { recursive: true });
  mkdirSync(join(nativeRepo, 'user_stories'), { recursive: true });
  execFileSync('git', ['init', '-q'], { cwd: nativeRepo });
  const nativeIface = { kind: 'native-only', status: 'draft', prose_sha256: '', reason: 'Native process boundary.' };
  const nativeBody = () => `# Native\n\nRun natively.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(nativeIface)}\n\`\`\`\n</details>\n`;
  nativeIface.prose_sha256 = seam.proseSha256(nativeBody());
  writeFileSync(join(nativeRepo, 'prompts/native.prompt.md'), nativeBody());
  writeFileSync(
    join(nativeRepo, 'user_stories/native-story.md'),
    '# Native Story\n\nI can run natively.\n\n## Acceptance criteria\n\n1. Works.\n\n## Native validation\n\n[Native profile](../prompts/native.prompt.md#native-validation-profile-native-prof)\n',
  );
  execFileSync('git', ['add', '.'], { cwd: nativeRepo });

  await assert.rejects(
    () => directClient.runCheck(
      { cwd: nativeRepo, words: ['native-story'], options: { '--lint': true } },
      { ...baseCutPorts, env: { HOME: join(tmp, 'home'), PDD_STATE_DIR: join(tmp, 'state') }, stdout: { write() {} }, stderr: { write() {} } },
    ),
    err => !(err instanceof TypeError) && /Native Story assessment ports.*not bound/.test(err.message),
  );
  // Even if assessNativeEvidence/usableResult/resultLines are supplied, missing allRuns also throws loudly instead of silently using [].
  await assert.rejects(
    () => directClient.runCheck(
      { cwd: nativeRepo, words: ['native-story'], options: { '--lint': true } },
      {
        ...baseCutPorts,
        env: { HOME: join(tmp, 'home'), PDD_STATE_DIR: join(tmp, 'state') },
        stdout: { write() {} },
        stderr: { write() {} },
        assessNativeEvidence: async () => ({ criteria: [], sourceState: 'current', identity: { stage: 'pr2' }, limits: [] }),
        usableResult: () => true,
        resultLines: () => [],
      },
    ),
    err => !(err instanceof TypeError) && /Native Story assessment ports.*allRuns.*not bound/.test(err.message),
  );

  // S1: Direct --lint and --lint --local without lintSvgLayouts throw an unbound-port Error instead of silently returning [].
  await assert.rejects(
    () => directClient.runCheck(
      { cwd: setup.repo, words: ['place-order'], options: { '--lint': true } },
      { ...portsFor(env).ports, ...baseCutPorts },
    ),
    err => !(err instanceof TypeError) && /SVG layout port \(lintSvgLayouts\) is not bound/.test(err.message),
  );
  await assert.rejects(
    () => directClient.runCheck(
      { cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--local': true } },
      { ...portsFor(env).ports, ...baseCutPorts },
    ),
    err => !(err instanceof TypeError) && /SVG layout port \(lintSvgLayouts\) is not bound/.test(err.message),
  );

  // S1: Direct connected runTry without loadAgentDefinitions throws an unbound-port Error instead of claiming no agents are configured.
  await assert.rejects(
    () => directClient.runTry(
      { cwd: setup.repo, words: ['place-order'], options: { '--agent': 'codex' } },
      { ...portsFor(env).ports, ...baseCutPorts, agentBridge: undefined },
    ),
    err => !(err instanceof TypeError) && /Agent configuration port \(loadAgentDefinitions\) is not bound/.test(err.message),
  );

  // S1: Direct createAgentBridge without loadAgentDefinitions, discoverAgents or askAgent throws an unbound-port Error before network.
  const directAgentChat = await import('../src/runtime/agent-chat.mjs');
  const directAgentAsk = await import('../src/runtime/agent-ask.mjs');
  await assert.rejects(
    () => directAgentAsk.askAgent({ agent: 'codex', entries: [] }),
    err => !(err instanceof TypeError) && err.unboundPort === true && /Agent process port.*not bound/.test(err.message),
  );
  let chatNetworkCalls = 0;
  const makeChatContext = (extraPorts = {}, preDefinitions = undefined) => ({
    root: setup.repo,
    origin: 'https://runtime.example',
    identity: { token: 'gho_test' },
    secrets: ['gho_test'],
    agentDefinitions: preDefinitions,
    store: { repo: () => ({}), saveRepo() {} },
    ports: { env, now: Date.now, randomUUID: () => '11111111-1111-4111-8111-111111111111', sleep: async () => {}, stdout: { write() {} }, stderr: { write() {} }, ...extraPorts },
    runtime: { send: async () => { chatNetworkCalls += 1; return { status: 404, json: {} }; } },
  });
  await assert.rejects(
    () => directAgentChat.createAgentBridge(makeChatContext(), { path: 'tests/place-order.json' }, '11111111-1111-4111-8111-111111111111', {}, 'https://runtime.example/s/abc/'),
    err => !(err instanceof TypeError) && /Agent configuration port \(loadAgentDefinitions\) is not bound/.test(err.message),
  );
  await assert.rejects(
    () => directAgentChat.createAgentBridge(
      makeChatContext({}, [{ id: 'codex', name: 'Codex', kind: 'codex', command: 'codex', env: {} }]),
      { path: 'tests/place-order.json' },
      '11111111-1111-4111-8111-111111111111',
      {},
      'https://runtime.example/s/abc/',
    ),
    err => !(err instanceof TypeError) && /Agent adapter ports \(discoverAgents, askAgent\) are not bound/.test(err.message),
  );
  assert.equal(chatNetworkCalls, 0, 'unbound agent chat ports must fail before network access');
  // Section 4.2 agents.{list,run} port binds askAgent cleanly without askAgent override.
  const bridgeFromRunPort = await directAgentChat.createAgentBridge(
    makeChatContext(
      { agents: { list: async () => [], run: async () => ({ code: 0, stdout: '{}', stderr: '' }) } },
      [{ id: 'codex', name: 'Codex', kind: 'codex', command: 'codex', env: {} }],
    ),
    { path: 'tests/place-order.json' },
    '11111111-1111-4111-8111-111111111111',
    {},
    'https://runtime.example/s/abc/',
  );
  assert.equal(bridgeFromRunPort, null);
  assert.equal(chatNetworkCalls, 1);

  // S1 (critical): Direct interactive runTry receiving a pending Try-page approval without promptPath/askApproval
  // throws an unbound-port Error and NEVER records or posts a fake 'declined' decision to the Runtime.
  const { Readable } = await import('node:stream');
  const { existsSync } = await import('node:fs');
  const approvalTrySetup = harbor(t);
  const approvalPosts = [];
  const approvalFake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: f.tryJob(entry.request.requestId) };
    if (entry.method === 'GET' && entry.url.endsWith('/tests')) return { status: 200, json: { tests: [] } };
    if (entry.method === 'GET' && entry.url.endsWith('/approvals')) {
      return {
        status: 200,
        json: {
          approvals: [{
            id: 'req-pending-1',
            prompt_path: 'prompts/place_order.prompt.md',
            prose_sha256: 'a'.repeat(64),
            requested_at: '2026-11-11T00:00:00Z',
            state: 'pending',
          }],
        },
      };
    }
    if (entry.method === 'POST' && entry.url.includes('/approvals/')) {
      approvalPosts.push(entry);
      return { status: 200, json: { ok: true } };
    }
    return { status: 404, json: {} };
  });
  const approvalPorts = portsFor(
    { HOME: approvalTrySetup.home, PDD_STATE_DIR: approvalTrySetup.state, PDD_RUNTIME_URL: approvalFake.origin },
    {
      ...baseCutPorts,
      interactive: true,
      agentBridge: false,
      openUrl: async () => true,
      stdin: Readable.from(['y\n']),
      lintSvgLayouts: () => [],
    },
  ).ports;
  await assert.rejects(
    () => directClient.runTry({ cwd: approvalTrySetup.repo, words: ['place-order'], options: { '--no-open': true } }, approvalPorts),
    err => !(err instanceof TypeError) && /Try approval ports \(promptPath, askApproval\) are not bound/.test(err.message),
  );
  assert.equal(approvalPosts.length, 0, 'unbound Try approval ports must never POST a fake decline to the Runtime');
  const triesDir = join(approvalTrySetup.state, 'tries');
  if (existsSync(triesDir)) {
    const { readdirSync } = await import('node:fs');
    const approvalFiles = readdirSync(triesDir).filter(f => f.endsWith('.approvals.json'));
    assert.deepEqual(approvalFiles, [], 'unbound Try approval ports must not write declined state to .approvals.json');
  }
});

test('SEAM14 (Should-fix 1 & 5): single shared defaultLineReader in src/runtime and base load order for agent-adapters in Try', async t => {
  const { spawnSync } = await import('node:child_process');
  const { pathToFileURL } = await import('node:url');
  const { Readable } = await import('node:stream');
  const directClient = await import('../src/runtime/runtime-client.mjs');
  const tryDoorsSrc = readFileSync(join(root, 'src/runtime/try-doors.mjs'), 'utf8');

  // (1) One shared defaultLineReader in src/runtime/runtime-client.mjs, imported by src/runtime/try-doors.mjs.
  assert.equal(typeof directClient.defaultLineReader, 'function');
  assert.ok(!/function\s+defaultLineReader\b/.test(tryDoorsSrc), 'try-doors.mjs must not define a second defaultLineReader');
  const reader = directClient.defaultLineReader(Readable.from(['yes\n']));
  assert.equal(await reader.ask(), 'yes');
  reader.close();

  // (5) createAgentBridge loads src/agent-adapters.mjs before "Connecting your agent..." and GET /model.
  const loader = "export async function resolve(s, c, n) { const r = await n(s, c); if (r.url.endsWith('/agent-adapters.mjs')) throw new Error('ADAPTERS_LOAD_FAILURE'); return r; }";
  const reg = `import { register } from 'node:module'; register(${JSON.stringify(`data:text/javascript,${encodeURIComponent(loader)}`)});`;
  const script = `
    const seam = await import(${JSON.stringify(pathToFileURL(join(root, 'src/runtime-seam.mjs')).href)});
    let stderr = '';
    let modelCalls = 0;
    const context = {
      root: process.cwd(),
      secrets: [],
      agentDefinitions: [{ id: 'codex', name: 'codex' }],
      ports: { stderr: { write(s) { stderr += s; } }, randomUUID: () => '00000000-0000-4000-8000-000000000001', env: {} },
      store: { repo: () => ({}), saveRepo() {} },
      runtime: { async send() { modelCalls++; return { status: 200, json: { entries: [] } }; } },
    };
    try {
      await seam.createAgentBridge(context, { path: 'tests/a.json' }, 'try-1', {}, 'https://runtime.example/try/1', {});
      process.exit(2);
    } catch (err) {
      process.stdout.write(JSON.stringify({ message: err.message, stderr, modelCalls }));
    }
  `;
  const res = spawnSync(
    process.execPath,
    ['--import', `data:text/javascript,${encodeURIComponent(reg)}`, '--input-type=module', '-e', script],
    { cwd: root, encoding: 'utf8' },
  );
  assert.equal(res.status, 0, res.stderr);
  const parsed = JSON.parse(res.stdout);
  assert.equal(parsed.message, 'ADAPTERS_LOAD_FAILURE');
  assert.equal(parsed.stderr, '');
  assert.equal(parsed.modelCalls, 0);
});

test('SEAM15 (R2b-2): src/runtime-seam.mjs supports base standalone call forms with host defaults bound', async t => {
  const { mkdirSync, mkdtempSync, rmSync, writeFileSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const seam = await import('../src/runtime-seam.mjs');

  // 1. composeProductTry with only { statFile, readFile } snapshot ports.
  const emptySchema = { type: 'object', properties: {}, required: [], additionalProperties: false };
  const files = new Map();
  const put = (path, value) => files.set(`/project/${path}`, typeof value === 'string' ? value : JSON.stringify(value));
  put('product/map.md', '# Shop: map\nSize: medium\n## Parts\n| Part | Folder | What it is |\n|---|---|---|\n| server | prompts/server | Processing |\n| phone | prompts/phone | Ordering |\n| barista | prompts/barista | Preparation |\n## Stories\n| Id | Part | Story | Tag |\n|---|---|---|---|\n| P01 | phone | Order | CORE |\n');
  put('product/plan.md', '# Plan\n## Runs\n| Run | Part | Slice | Stories | Needs |\n|---|---|---|---|---|\n| phone-1 | phone | core | P01 | |\n## After every tap\n1. prompts/server/server.prompt.md#forward\n');
  put('contracts/world.md', '# World\n| Key | Writer | Readers |\n|---|---|---|\n| orders | phone | server |\n| tickets | server | barista |\n');
  put('contracts/seed-world.json', { base: true });
  put('prompts/server/seed.json', { tickets: ['retained'] });
  put('prompts/phone/seed.json', { orders: [] });
  put('prompts/server/server.prompt.md', `<details><summary>Runtime interface</summary>\n\`\`\`json\n${JSON.stringify({ entries: [{ operation: 'forward', result_schema: emptySchema }] })}\n\`\`\`\n</details>`);
  for (const part of ['phone', 'barista']) {
    put(`app/maps/${part}.json`, {
      schema_version: 'prompt-runtime.app-map.v1',
      name: part,
      initial_screen: 'home',
      initial_route: null,
      initial_state: { selected: part },
      state_schema: { type: 'object', properties: { selected: { type: 'string' } }, required: ['selected'], additionalProperties: false },
      synthetic: false,
      screens: [{ id: 'home', prompt_path: `prompts/${part}/view.prompt.md`, operation: 'render', source: 'operation', format: 'html', input: {}, result_pointer: '/html' }],
      router: null,
      routes: [],
      stylesheets: [],
      handlers: [{ screen: 'home', kind: 'click', match: {}, handler: { prompt_path: `prompts/${part}/view.prompt.md`, operation: 'tap' }, input: {}, next: { kind: 'screen', screen: 'home', route_pointer: null }, state: { selected: part } }],
    });
  }
  const composed = seam.composeProductTry(
    { root: '/project' },
    {
      statFile: path => ({ exists: files.has(path), is_symlink: false }),
      readFile: path => {
        if (!files.has(path)) throw new Error(`Unexpected read ${path}`);
        return files.get(path);
      },
    },
  );
  assert.deepEqual(composed.parts, ['server', 'phone', 'barista']);
  assert.equal(composed.files.length, 2);

  // 2. runCheck with --screen, --drawing, --json and only { screenBrowser, env, stdout, stderr }.
  const dir = mkdtempSync(join(tmpdir(), 'pdd-r2b-2-screen-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  mkdirSync(join(dir, 'prompts'), { recursive: true });
  writeFileSync(
    join(dir, 'prompts/ready.ui.svg'),
    '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300"><title>Ready</title><desc>Ready screen</desc><text id="status" x="20" y="40">READY</text></svg>\n',
  );
  let browserCalls = 0;
  let stdout = '';
  let stderr = '';
  const code = await seam.runCheck(
    {
      cwd: dir,
      words: [],
      options: { '--screen': 'https://example.test/app', '--drawing': 'prompts/ready.ui.svg', '--json': true },
    },
    {
      screenBrowser: async () => {
        browserCalls++;
        return {
          viewport: { width: 400, height: 300 },
          reference: [{ kind: 'text', value: 'READY', node: 1, visible: true, box: { x: 20, y: 20, width: 80, height: 24 }, ancestors: [], region: null, tokens: ['tok-1'] }],
          actual: [{ kind: 'text', value: 'READY', node: 'tok-1', visible: true, box: { x: 20, y: 20, width: 80, height: 24 }, ancestors: [], region: null, tokens: ['tok-1'] }],
        };
      },
      gh: () => assert.fail('unexpected auth'),
      fetch: async () => assert.fail('unexpected network'),
      env: {},
      stdout: { write(chunk) { stdout += chunk; } },
      stderr: { write(chunk) { stderr += chunk; } },
    },
  );
  assert.equal(code, 0, stderr);
  assert.equal(browserCalls, 1);
  assert.equal(stderr, '');
  const report = JSON.parse(stdout);
  assert.equal(report.passed, true);
});

test('SEAM16 (S2): workflow-worker-completion keeps top-level await (exit 13 on unsettled drain) and no createRequire graph reaches top-level await', async t => {
  const { spawnSync } = await import('node:child_process');
  const { mkdtempSync, rmSync, writeFileSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const { dirname, resolve } = await import('node:path');
  const { pathToFileURL } = await import('node:url');

  // 1. workflow-worker-completion.mjs retains its top-level await and exits 13 when waitForWorkerCompletion stays unsettled at drain.
  const workerSrc = readFileSync(join(root, 'src/workflow-worker-completion.mjs'), 'utf8');
  assert.match(workerSrc, /\bawait\s+waitForWorkerCompletion\s*\(\s*identity\s*\)\s*;/);

  const tmp = mkdtempSync(join(tmpdir(), 'pdd-s2-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));
  const unsettledHook = join(tmp, 'unsettled-exec.mjs');
  writeFileSync(
    unsettledHook,
    "import { registerHooks } from 'node:module';\n" +
      "registerHooks({ load(url, ctx, next) {\n" +
      "  if (url.endsWith('/src/workflow-worker-completion.mjs')) {\n" +
      "    const res = next(url, ctx);\n" +
      "    const src = String(res.source).replace('const exec = promisify(execFile);', 'const exec = () => new Promise(() => {});');\n" +
      "    return { ...res, source: src };\n" +
      "  }\n" +
      "  return next(url, ctx);\n" +
      "} });\n",
  );
  const workerRun = spawnSync(
    process.execPath,
    [
      '--import',
      pathToFileURL(unsettledHook).href,
      join(root, 'src/workflow-worker-completion.mjs'),
      JSON.stringify({ runId: 'r1', number: 1, sourceRoot: tmp, runDir: tmp, area: 'plan', paneId: '%1', startAnchor: 0, coordinatorPaneId: '%2' }),
    ],
    { cwd: root, encoding: 'utf8', timeout: 8000 },
  );
  assert.equal(workerRun.status, 13, `expected unsettled top-level await exit 13, got ${workerRun.status} (${workerRun.stderr})`);

  // 2. Every module that uses createRequire in src/ has zero top-level await anywhere in its reachable require() graphs.
  const requireHosts = walk('src').filter(rel => readFileSync(join(root, rel), 'utf8').includes('createRequire'));
  assert.ok(requireHosts.length > 0, 'expected at least one createRequire host in src/');

  const targets = [];
  for (const hostRel of requireHosts) {
    const hostAbs = join(root, hostRel);
    const src = readFileSync(hostAbs, 'utf8');
    for (const m of src.matchAll(/\breq\(\s*(['"`])([^'"`]+)\1\s*\)/g)) {
      const spec = m[2];
      if (spec.startsWith('.')) {
        targets.push({ hostRel, targetAbs: resolve(dirname(hostAbs), spec) });
      }
    }
  }
  assert.ok(targets.length > 0, 'expected static req(...) targets to inspect');

  // Walk transitive static ESM imports from every req(...) target and verify createRequire succeeds on every reachable module in a fresh process.
  const reachable = new Set();
  const queue = targets.map(item => item.targetAbs);
  while (queue.length) {
    const abs = queue.pop();
    if (reachable.has(abs)) continue;
    reachable.add(abs);
    if (!abs.endsWith('.mjs')) continue;
    const clean = stripCommentsPreservingLines(readFileSync(abs, 'utf8'));
    const staticRe = /\b(?:import|export)\s+(?:[^'"]*?\bfrom\s*)?(['"])([^'"]+)\1/g;
    let m;
    while ((m = staticRe.exec(clean)) !== null) {
      const spec = decodeJsEscapes(m[2]);
      if (spec.startsWith('.')) {
        const nextAbs = resolve(dirname(abs), spec);
        if (!reachable.has(nextAbs)) queue.push(nextAbs);
      }
    }
  }

  const probe = spawnSync(
    process.execPath,
    [
      '-e',
      "const { createRequire } = require('node:module');\n" +
        "const req = createRequire(process.argv[1]);\n" +
        "for (const target of JSON.parse(process.argv[2])) req(target);\n",
      join(root, 'src/runtime-seam.mjs'),
      JSON.stringify([...reachable]),
    ],
    { cwd: root, encoding: 'utf8', timeout: 8000 },
  );
  assert.equal(
    probe.status,
    0,
    `a module reachable from createRequire has top-level await or failed synchronous load:\n${probe.stderr}`,
  );
});

test('SEAM17 (S3): stateless header reader in runtime-check-plan matches file-owner headerPrompts across corpus, and index constants match canonical owners', async () => {
  const { defaultHeaderPrompts } = await import('../src/runtime/runtime-check-plan.mjs');
  const { headerPrompts } = await import('../src/file-owner.mjs');
  const index = await import('../src/runtime/index.mjs');
  const seam = await import('../src/runtime-seam.mjs');
  const hostSelection = await import('../src/test-selection.mjs');
  const hostExit = await import('../src/runtime-exit.mjs');
  const hostPromptWords = await import('../src/prompt-tests-words.mjs');

  assert.deepEqual(index.LIMITS, index.runtimePreflightSlice().LIMITS);
  assert.deepEqual(index.TEST_SCHEMA, index.runtimePreflightSlice().TEST_SCHEMA);
  assert.deepEqual(index.DRAFT_SERVER_TEXT, index.runtimePreflightSlice().DRAFT_SERVER_TEXT);
  assert.deepEqual(index.STALE_HINT, index.runtimePreflightSlice().STALE_HINT);
  assert.deepEqual(index.staleHint, index.runtimePreflightSlice().staleHint);
  assert.deepEqual(index.PROVIDER_TEXT, index.runtimeOutcomeSlice().PROVIDER_TEXT);
  assert.deepEqual(index.CHECK_STATES, index.runtimeOutcomeSlice().CHECK_STATES);
  assert.deepEqual(index.OPEN_STATES, index.runtimeOutputSlice().OPEN_STATES);
  assert.deepEqual(seam.NO_TESTS, hostSelection.NO_TESTS);
  assert.deepEqual(seam.STATE_EXIT_CODES, hostExit.STATE_EXIT_CODES);
  assert.deepEqual(seam.COMMAND_EXIT_CODE, hostExit.COMMAND_EXIT_CODE);
  assert.deepEqual(seam.PROMPT_TESTS_LABEL, hostPromptWords.PROMPT_TESTS_LABEL);
  assert.deepEqual(seam.PROMPT_TESTS_WORDS, hostPromptWords.PROMPT_TESTS_WORDS);
  const clientSource = readFileSync(join(root, 'src/runtime/runtime-client.mjs'), 'utf8');
  const engineShaMatch = /\bconst ENGINE_SHA = '([0-9a-f]{40})';/.exec(clientSource);
  assert.ok(engineShaMatch, 'expected ENGINE_SHA in src/runtime/runtime-client.mjs');
  assert.equal(index.version().engine_sha, engineShaMatch[1]);
  assert.equal(seam.version().engine_sha, engineShaMatch[1]);

  const prefixes = ['', '//', '///', '  // ', '\t#', '##', '--', ';', ';;', '/*', '/**', ' *', '<!--', '"""', "'''", 'rem ', '% ', '// prefix '];
  const suffixes = ['', '.', ' */', '. */', ' -->', '. -->', ' """', " '''", '   ', ' */ trailing'];
  const goodHash = 'a'.repeat(64);
  const hashes = [
    '',
    ` (sha256: ${goodHash})`,
    ` (sha256: ${'0123456789abcdef'.repeat(4)})`,
    ` (sha256: ${'a'.repeat(63)})`,
    ` (sha256: ${'a'.repeat(65)})`,
    ` (sha256: ${'A'.repeat(64)})`,
    ` (sha256: ${'g'.repeat(64)})`,
  ];
  const paths = [
    'prompts/a.prompt.md',
    'a.prompt.md',
    'prompts/cli/runtime-check-plan.prompt.md',
    '/abs/a.prompt.md',
    './a.prompt.md',
    '../a.prompt.md',
    'prompts//a.prompt.md',
    'prompts/.git/a.prompt.md',
    'prompts/.Git/a.prompt.md',
    'prompts\\a.prompt.md',
    'prompts/a.md',
    'prompts/a\x00.prompt.md',
    'prompts/a\x7f.prompt.md',
    `${'p'.repeat(990)}.prompt.md`,
    `${'p'.repeat(991)}.prompt.md`,
  ];

  let checked = 0;
  for (const sample of [null, undefined, false, '', Buffer.alloc(0), '\uFEFF// Generated from prompts/a.prompt.md\n']) {
    assert.deepEqual(defaultHeaderPrompts(sample), headerPrompts(sample));
    checked += 1;
  }

  for (const pre of prefixes) {
    for (const p of paths) {
      for (const h of hashes) {
        const sfx = suffixes[(checked + p.length) % suffixes.length];
        const line = `${pre}${pre && !pre.endsWith(' ') ? ' ' : ''}Generated from ${p}${h}${sfx}`;
        for (const eol of ['\n', '\r\n']) {
          const doc = `${line}${eol}export const x = 1;${eol}`;
          assert.deepEqual(defaultHeaderPrompts(doc), headerPrompts(doc), `mismatch on: ${JSON.stringify(doc)}`);
          checked += 1;
        }
      }
    }
  }

  // Line-length edges around LINE = 1100 and byte-window edges around HEAD = 4096 (including multi-byte UTF-8 and Buffers).
  const targetHeader = '// Generated from prompts/edge.prompt.md';
  for (const padLen of [1050, 1058, 1059, 1060, 1061, 1062, 1100, 1101]) {
    const padded = `${' '.repeat(Math.max(0, padLen - targetHeader.length))}${targetHeader}\n`;
    assert.deepEqual(defaultHeaderPrompts(padded), headerPrompts(padded));
    checked += 1;
  }
  for (const totalBeforeEnd of [4090, 4094, 4095, 4096, 4097, 4098, 4100]) {
    const fillerLen = Math.max(0, totalBeforeEnd - Buffer.byteLength(targetHeader) - 1);
    const asciiDoc = `${'// ' + 'x'.repeat(Math.max(0, fillerLen - 3))}\n${targetHeader}\n// after\n`;
    const utf8Doc = `${'// ' + 'é'.repeat(Math.max(0, Math.floor((fillerLen - 3) / 2)))}\n${targetHeader}\n`;
    const dupDoc = `// Generated from prompts/first.prompt.md\r\n// Generated from prompts/second.prompt.md\r\n// Generated from prompts/first.prompt.md\r\n${asciiDoc}`;
    for (const candidate of [asciiDoc, Buffer.from(asciiDoc, 'utf8'), utf8Doc, Buffer.from(utf8Doc, 'utf8'), dupDoc]) {
      assert.deepEqual(defaultHeaderPrompts(candidate), headerPrompts(candidate));
      checked += 1;
    }
  }
  assert.ok(checked > 3500, `expected >3500 corpus checks, ran ${checked}`);
});

test('SEAM18 (M3-1, M3-2, M3-3): section 4.1 API keeps zero-static-import lazy loading and binds all host ports on runtime-seam', async t => {
  const { execFileSync, spawnSync } = await import('node:child_process');
  const { mkdirSync, mkdtempSync, rmSync, writeFileSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const { pathToFileURL } = await import('node:url');

  const indexSource = readFileSync(join(root, 'src/runtime/index.mjs'), 'utf8');
  const staticImports = [...indexSource.matchAll(/^\s*(?:import|export)\s+(?:[^'"]*?\s+from\s+)?['"]([^'"]+)['"]/gm)].map(m => m[1]);
  assert.ok(staticImports.length > 0);
  for (const spec of staticImports) {
    assert.ok(spec.startsWith('node:'), `src/runtime/index.mjs must have zero relative static imports, found: ${spec}`);
  }

  const loadedSrcInFreshChild = expr => {
    const hookDataUrl = `data:text/javascript,${encodeURIComponent(
      `const prefix = ${JSON.stringify(pathToFileURL(join(root, 'src/')).href)};
       const base = ${JSON.stringify(pathToFileURL(root + '/').href)};
       export async function resolve(s, c, next) {
         const r = await next(s, c);
         if (r.url.startsWith(prefix)) process.stderr.write('MOD:' + r.url.slice(base.length) + '\\n');
         return r;
       }`,
    )}`;
    const registerHook = `data:text/javascript,${encodeURIComponent(
      `import { register } from 'node:module'; register(${JSON.stringify(hookDataUrl)});`,
    )}`;
    const child = spawnSync(
      process.execPath,
      ['--import', registerHook, '--input-type=module', '-e', expr],
      { cwd: root, encoding: 'utf8', timeout: 8000 },
    );
    assert.equal(child.status, 0, `child failed:\n${child.stderr}`);
    const mods = [...new Set(
      child.stderr
        .split('\n')
        .filter(l => l.startsWith('MOD:'))
        .map(l => l.slice(4)),
    )];
    return { mods, stdout: child.stdout.trim() };
  };

  const entryUrl = JSON.stringify(pathToFileURL(join(root, 'src/runtime/index.mjs')).href);
  const seamUrl = JSON.stringify(pathToFileURL(join(root, 'src/runtime-seam.mjs')).href);

  assert.deepEqual(loadedSrcInFreshChild(`await import(${entryUrl});`).mods, ['src/runtime/index.mjs']);
  assert.deepEqual(loadedSrcInFreshChild(`await import(${seamUrl});`).mods, [
    'src/runtime-seam.mjs',
    'src/runtime/index.mjs',
  ]);
  const verChild = loadedSrcInFreshChild(`const s = await import(${seamUrl}); process.stdout.write(JSON.stringify(s.version()));`);
  assert.deepEqual(verChild.mods, ['src/runtime-seam.mjs', 'src/runtime/index.mjs']);
  const ver = JSON.parse(verChild.stdout);
  assert.equal(ver.package, '@promptdriven/runtime-client');
  assert.equal(ver.api_version, 1);
  assert.deepEqual(ver.formats, {
    scenario: 'prompt-runtime.program-scenario.v1',
    app_map: 'prompt-runtime.app-map.v1',
  });
  assert.deepEqual(ver.limits, { bytes: 10_485_760, files: 10_000 });

  // CJS createRequire loads do not pass through ESM resolve, so verify CJS require.cache + ESM mods together:
  const rootPrefix = join(root, 'src/').replaceAll('\\', '/');
  const rootDir = rootPrefix.slice(0, -4);
  const sliceProbe = callExpr => {
    const script = `
      import { createRequire } from 'node:module';
      const req = createRequire(${entryUrl});
      const s = await import(${seamUrl});
      ${callExpr};
      const cjs = Object.keys(req.cache)
        .map(p => p.replaceAll('\\\\', '/'))
        .filter(p => p.startsWith(${JSON.stringify(rootPrefix)}))
        .map(p => p.slice(${JSON.stringify(rootDir)}.length))
        .sort();
      process.stdout.write(JSON.stringify(cjs));
    `;
    const res = loadedSrcInFreshChild(script);
    return JSON.parse(res.stdout);
  };
  assert.deepEqual(sliceProbe('s.version()'), []);
  assert.deepEqual(sliceProbe('s.format.parseScenario(\'{"a":1}\')'), ['src/runtime/scenario-json.mjs']);
  assert.deepEqual(sliceProbe('s.format.interfaceBlocks("# hi\\n")'), ['src/runtime/runtime-preflight.mjs']);
  assert.deepEqual(sliceProbe(`s.workspace.policy({ root: ${JSON.stringify(root)} })`), [
    'src/runtime/runtime-workspace.mjs',
  ]);

  const index = await import('../src/runtime/index.mjs');
  const seam = await import('../src/runtime-seam.mjs');
  const { redactSecrets } = await import('../src/secret-redaction.mjs');
  const { approvePromptText } = await import('../src/prompt-approve.mjs');

  for (const name of ['lint', 'check', 'read', 'retry', 'local', 'simulate', 'jobs', 'health', 'mcp', 'draftInterfaces', 'contracts', 'render']) {
    assert.equal(typeof seam[name], 'function', `seam.${name} must be a function`);
    assert.notEqual(seam[name], index[name], `seam.${name} must wrap host ports, not re-export index.${name}`);
  }
  assert.notEqual(seam.source.identity, index.source.identity);
  assert.notEqual(seam.saved.results, index.saved.results);
  assert.equal(seam.format, index.format);
  assert.equal(seam.workspace, index.workspace);
  assert.equal(seam.version, index.version);
  assert.equal(seam.exactValue, index.exactValue);

  // Reproduce Claude M3-3 probe: seam.health must register gh token into host secret-redaction registry.
  const markerToken = `ghp_seam18HealthSecretMarker${Date.now()}xyz987654321`;
  await seam.health(
    { env: { ...process.env, PDD_RUNTIME_URL: 'https://example.invalid' } },
    {
      gh: () => ({ status: 0, stdout: `${markerToken}\n` }),
      fetch: async () => {
        throw new Error('offline');
      },
    },
  );
  assert.equal(redactSecrets(`token=${markerToken}`), 'token=[redacted]');

  // seam.lint({ root, local: true }) binds lintSvgLayouts and selection ports (whereas index.lint throws unboundPort).
  const tmp = mkdtempSync(join(tmpdir(), 'pdd-seam18-'));
  t.after(() => rmSync(tmp, { recursive: true, force: true }));
  mkdirSync(join(tmp, 'prompts/ui/views'), { recursive: true });
  mkdirSync(join(tmp, 'user_stories'), { recursive: true });
  mkdirSync(join(tmp, 'tests'), { recursive: true });
  writeFileSync(
    join(tmp, 'prompts/ui/views/card__stacked.ui.svg'),
    '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 40"><title>Card</title><desc>Card</desc><g id="unmentioned-card-box"><text x="10" y="20">Hello</text></g></svg>\n',
  );
  const rawPrompt = [
    '# Card view',
    '',
    '## Appearance',
    '',
    '![Card](views/card__stacked.ui.svg)',
    '',
    'Shows Hello.',
    '',
    '<details><summary>Runtime interface</summary>',
    '',
    '```json',
    '{"status":"draft","prose_sha256":"","entries":[{"operation":"render","input_schema":{"type":"object","additionalProperties":false},"result_schema":{"type":"object","properties":{"ok":{"type":"boolean"}},"required":["ok"],"additionalProperties":false}}],"limits":{"max_steps":10,"max_model_calls":4}}',
    '```',
    '</details>',
    '',
  ].join('\n');
  const filledPrompt = seam.format.setInterfaceStatus(rawPrompt, {
    status: 'approved',
    prose_sha256: seam.format.proseSha256(rawPrompt),
  });
  assert.ok(filledPrompt);
  writeFileSync(join(tmp, 'prompts/ui/card.prompt.md'), filledPrompt);
  writeFileSync(join(tmp, 'user_stories/card.md'), '# Card\n\n## Acceptance criteria\n\n1. Shows Hello.\n');
  writeFileSync(
    join(tmp, 'tests/card.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/card.md',
      criteria: [{ id: 'AC1', text: 'Shows Hello.' }],
      initial_world: {},
      steps: [
        {
          step_id: 's1',
          entry_path: 'prompts/ui/card.prompt.md',
          operation: 'render',
          input: {},
          checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', value: true }],
        },
      ],
    }) + '\n',
  );
  execFileSync('git', ['init', '-q'], { cwd: tmp });
  execFileSync('git', ['add', '.'], { cwd: tmp });

  await assert.rejects(() => index.lint({ root: tmp, local: true }), /SVG layout port \(lintSvgLayouts\) is not bound/);
  let lintOut = '';
  const lintErr = { write() {} };
  const lintCode = await seam.lint(
    { root: tmp, local: true, options: { '--json': true } },
    { stdout: { write: s => { lintOut += s; } }, stderr: lintErr, env: { ...process.env, HOME: tmp } },
  );
  assert.equal(lintCode, 0);
  const lintReport = JSON.parse(lintOut);
  assert.ok(
    lintReport.warnings.some(w => String(w).includes('unmentioned-card-box')),
    `expected SVG layout warning from seam.lint, got: ${JSON.stringify(lintReport.warnings)}`,
  );

  let filesOut = '';
  const filesCode = await seam.local(
    { root: tmp, what: 'files' },
    { stdout: { write: s => { filesOut += s; } }, stderr: lintErr, env: { ...process.env, HOME: tmp } },
  );
  assert.equal(filesCode, 0);
  assert.ok(filesOut.includes('prompts/ui/card.prompt.md'));

  let jobsOut = '';
  const jobsCode = await seam.jobs(
    { env: { HOME: tmp, PDD_STATE_DIR: join(tmp, 'state') } },
    { stdout: { write: s => { jobsOut += s; } }, stderr: lintErr },
  );
  assert.equal(jobsCode, 0);
  assert.ok(jobsOut.length > 0);

  const snap = seam.source.identity({ root: tmp, tests: [{ path: 'tests/card.json' }] });
  assert.equal(snap.stories.length, 1);
  assert.equal(snap.stories[0].story_path, 'user_stories/card.md');

  const savedRes = await seam.saved.results({ root: tmp });
  assert.ok(Array.isArray(savedRes.stories));

  const sampleRows = [{ story: 'card', state: 'passed' }];
  assert.equal(seam.render(sampleRows, { as: 'summary' }), seam.summaryLine(sampleRows));
  assert.match(seam.render(sampleRows, { as: 'summary' }), /^Prompt tests:/);
  assert.match(seam.render(sampleRows, { as: 'summary' }, { promptTestsLabel: 'Custom check' }), /^Custom check:/);
  assert.deepEqual(seam.render(sampleRows, { as: 'story-lines' }), seam.storyLines(sampleRows));
  assert.equal(seam.render({ rows: sampleRows, exitCode: 0 }, { as: 'json' }).exit_code, 0);

  // format.setInterfaceStatus agrees with approvePromptText on single-key prompts and rejects duplicate keys / fence injection.
  for (const body of [
    '{"status":"draft","prose_sha256":"0000"}',
    '{\n  "kind": "partial",\n  "status": "draft",\n  "prose_sha256": "",\n  "entries": [{"operation": "op", "nested": {"status": "keep"}}]\n}',
    '{"prose_sha256": "abcd", "status": "approved", "reason": "x", "kind": "native-only"}',
  ]) {
    const doc = `# Title\n\nBody text.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${body}\n\`\`\`\n</details>\n`;
    const digest = seam.format.proseSha256(doc);
    assert.equal(
      seam.format.setInterfaceStatus(doc, { status: 'approved', prose_sha256: digest }),
      approvePromptText(doc),
    );
  }
  const dupStatusDoc =
    '# Title\n\nBody.\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status":"draft","status":"draft","prose_sha256":""}\n```\n</details>\n';
  assert.equal(seam.format.setInterfaceStatus(dupStatusDoc, { status: 'approved', prose_sha256: 'a'.repeat(64) }), null);
  const dupDigestDoc =
    '# Title\n\nBody.\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status":"draft","prose_sha256":"","prose_sha256":""}\n```\n</details>\n';
  assert.equal(seam.format.setInterfaceStatus(dupDigestDoc, { status: 'approved', prose_sha256: 'a'.repeat(64) }), null);
  assert.equal(seam.format.setInterfaceStatus(filledPrompt, { status: 'x```</details>' }), null);
  assert.equal(seam.format.setInterfaceStatus('# No block\n', { status: 'approved' }), null);
  assert.equal(seam.format.setInterfaceStatus(filledPrompt, { status: 123 }), null);
});
