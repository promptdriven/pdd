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

test('SEAM2: src/runtime-seam.mjs imports only src/runtime/index.mjs and exposes its exact surface', async () => {
  const seamSource = readFileSync(join(root, 'src/runtime-seam.mjs'), 'utf8');
  const specifiers = stringLiterals(seamSource).map(item => item.value);
  assert.deepEqual(specifiers, ['./runtime/index.mjs']);
  const seam = await import('../src/runtime-seam.mjs');
  const entry = await import('../src/runtime/index.mjs');
  assert.deepEqual(Object.keys(seam).sort(), Object.keys(entry).sort());
  for (const key of Object.keys(entry)) {
    assert.equal(seam[key], entry[key], `seam export ${key} must match src/runtime/index.mjs`);
  }
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
