// Generated from prompts/cli/human-boundary-card.prompt.md (sha256: 5b627d509ee6c5433a342fb16dddf94167fc43dfbe705671c85372e4ff6d8d58).
import { spawnSync } from 'node:child_process';
import { lstatSync, readdirSync, readFileSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join, posix, resolve, sep } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { isTestPromptPath } from './file-owner.mjs';
import {
  TEST_SCHEMA,
  findTests,
  gitFiles,
  interfaceBlocks,
  parseScenarioJson,
  promptMarkdownTargets,
  readPrompt,
  storyCriteria,
} from './runtime-seam.mjs';
import { isLintableStoryPath } from './story-lint.mjs';
import { hasAcceptance, isStoryPath } from './test-selection.mjs';

export const BOUNDARY_CARD_MAX_LINES = 25;

const BATCH_NAME = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
const UUID_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const EFFECT_SEGMENT_RE = /(?:^|[_-])(effects?|side_effects?|actions?|commands?|calls?|dispatched|dispatch|emitted|emit|sent|notifications?|alerts?|events?|writes?|mutations?|invocations?|executed|outbound)(?:$|[_-])/i;
const EFFECT_KEY_RE = /^(effect|side_effect|action|command|call|port|tool|dispatch|dispatched|emit|emitted|sent|alert|notification|event)$/i;

const STOPWORDS = new Set([
  'about', 'above', 'across', 'after', 'again', 'against', 'allow', 'allows', 'allowed', 'already', 'also', 'always',
  'among', 'another', 'array', 'assert', 'asserts', 'back', 'because', 'been', 'before', 'being', 'below', 'between',
  'boolean', 'both', 'call', 'called', 'calls', 'cannot', 'case', 'cases', 'change', 'changed', 'changes', 'check',
  'checked', 'checks', 'code', 'contain', 'contains', 'context', 'count', 'criteria', 'criterion', 'current', 'data',
  'default', 'does', 'done', 'during', 'each', 'either', 'else', 'empty', 'entry', 'equal', 'equals', 'error', 'errors',
  'even', 'every', 'exact', 'expect', 'expected', 'fail', 'failed', 'fails', 'false', 'field', 'fields', 'file', 'files',
  'first', 'follow', 'follows', 'forbid', 'forbidden', 'from', 'full', 'give', 'given', 'gives', 'have', 'having', 'hold',
  'holds', 'include', 'includes', 'initial', 'input', 'inputs', 'integer', 'into', 'item', 'items', 'json', 'keep',
  'keeps', 'kept', 'kind', 'last', 'least', 'less', 'line', 'lines', 'list', 'lists', 'load', 'loaded', 'make', 'makes',
  'match', 'matches', 'model', 'more', 'most', 'must', 'name', 'named', 'names', 'need', 'needs', 'never', 'next', 'none',
  'null', 'number', 'object', 'objects', 'once', 'only', 'operation', 'operations', 'optional', 'other', 'otherwise',
  'outcome', 'outcomes', 'output', 'outputs', 'over', 'pass', 'passed', 'passes', 'path', 'paths', 'person', 'plain',
  'policy', 'port', 'ports', 'preserve', 'preserves', 'prompt', 'prompts', 'read', 'reads', 'reason', 'record', 'records',
  'report', 'reported', 'reports', 'require', 'required', 'requires', 'resource', 'resources', 'response', 'result',
  'results', 'retain', 'retains', 'return', 'returned', 'returns', 'route', 'rule', 'rules', 'same', 'save', 'saved',
  'scenario', 'scenarios', 'schema', 'section', 'select', 'selected', 'send', 'sends', 'sent', 'shall', 'should', 'show',
  'shown', 'shows', 'simulate', 'simulated', 'simulation', 'simulator', 'since', 'single', 'slice', 'some', 'source',
  'sources', 'state', 'states', 'status', 'stay', 'stays', 'step', 'steps', 'still', 'stories', 'story', 'string',
  'such', 'supplied', 'system', 'target', 'test', 'tested', 'tests', 'text', 'than', 'that', 'their', 'them', 'then',
  'there', 'these', 'they', 'this', 'those', 'through', 'true', 'type', 'types', 'unchanged', 'under', 'until', 'update',
  'updated', 'updates', 'used', 'user', 'users', 'using', 'valid', 'validate', 'value', 'values', 'verify', 'version',
  'want', 'wants', 'when', 'where', 'whether', 'which', 'while', 'with', 'within', 'without', 'word', 'words', 'work',
  'works', 'world', 'write', 'writes',
]);

const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const cleanOneLine = value => String(value ?? '')
  .replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '')
  .replace(/[\x00-\x1f\x7f-\x9f\u2028\u2029]+/g, ' ')
  .replace(/\s+/g, ' ')
  .trim();

function clipText(value, max = 96) {
  const flat = cleanOneLine(value);
  const chars = [...flat];
  if (chars.length <= max) return flat;
  const cut = chars.slice(0, max - 2).join('');
  const word = cut.replace(/\s+\S*$/, '');
  return `${(word.length >= cut.length / 2 ? word : cut).trimEnd()} …`;
}

function canonicalRoot(root) {
  try { return realpathSync(root); } catch { return resolve(root); }
}

function readSafeText(rootReal, relPath) {
  if (typeof relPath !== 'string' || !relPath || relPath.startsWith('/') || relPath.includes('\\')) return null;
  const normalized = posix.normalize(relPath);
  if (normalized.startsWith('..') || normalized.split('/').includes('..')) return null;
  const full = join(rootReal, normalized);
  try {
    const stat = lstatSync(full);
    if (!stat.isFile()) return null;
    const real = realpathSync(full);
    if (real !== rootReal && !real.startsWith(`${rootReal}${sep}`)) return null;
    return readFileSync(real, 'utf8');
  } catch {
    return null;
  }
}

function proseWithoutInterface(text) {
  if (typeof text !== 'string') return '';
  let out = '', at = 0;
  for (const block of interfaceBlocks(text)) {
    out += text.slice(at, block.index);
    at = block.index + block[0].length;
  }
  const rest = out + text.slice(at);
  return rest.replace(/^---\r?\n[\s\S]*?\r?\n---\r?\n?/, '');
}

function countProseLines(text) {
  const prose = proseWithoutInterface(text).replace(/\r\n/g, '\n').replace(/\n+$/, '');
  return prose ? prose.split('\n').length : 0;
}

function headingSlug(rawHeading) {
  return String(rawHeading ?? '')
    .replace(/`([^`]*)`/g, '$1')
    .replace(/\[([^\]]*)\]\([^)]*\)/g, '$1')
    .replace(/<[^>]+>/g, '')
    .toLowerCase()
    .trim()
    .replace(/[^\p{L}\p{N}\s_-]+/gu, '')
    .replace(/\s+/g, '-');
}

function promptHeadingSlugs(text) {
  const slugs = new Set();
  if (typeof text !== 'string') return slugs;
  const prose = proseWithoutInterface(text);
  for (const match of prose.matchAll(/^#{1,6}[ \t]+(.+?)[ \t]*$/gm)) {
    const slug = headingSlug(match[1]);
    if (slug) slugs.add(slug);
  }
  for (const match of prose.matchAll(/<a\s+[^>]*\bid=["']([^"']+)["']/gi)) {
    if (match[1]) slugs.add(match[1].toLowerCase());
  }
  return slugs;
}

function dependenciesSection(text) {
  const prose = proseWithoutInterface(text);
  const heading = /^##[ \t]+Dependencies[ \t]*\r?$/im.exec(prose);
  if (!heading) return '';
  const rest = prose.slice(heading.index + heading[0].length);
  const end = /^#{1,2}[ \t]+/m.exec(rest);
  return end ? rest.slice(0, end.index) : rest;
}

function resolvePromptHref(rawHref, fromPath, visible) {
  if (typeof rawHref !== 'string') return null;
  const trimmed = rawHref.trim().replace(/^<|>$/g, '');
  if (!trimmed || /^[a-z]+:/i.test(trimmed) || trimmed.startsWith('#')) return null;
  const hashAt = trimmed.indexOf('#');
  const rawPath = hashAt >= 0 ? trimmed.slice(0, hashAt) : trimmed;
  const fragment = hashAt >= 0 ? trimmed.slice(hashAt + 1).trim().toLowerCase() : null;
  if (!rawPath.endsWith('.prompt.md')) return null;
  const baseDir = posix.dirname(fromPath);
  const resolved = posix.normalize(baseDir === '.' ? rawPath : posix.join(baseDir, rawPath));
  if (resolved.startsWith('..') || !visible.has(resolved)) return null;
  return { target: resolved, fragment: fragment || null };
}

function extractFragmentLinks(sectionText, fromPath, visible) {
  const links = [];
  if (typeof sectionText !== 'string' || !sectionText) return links;
  for (const match of sectionText.matchAll(/\[[^\]\n]*\]\(([^()\n]+)\)/g)) {
    const resolved = resolvePromptHref(match[1], fromPath, visible);
    if (resolved) links.push({ from: fromPath, ...resolved });
  }
  return links;
}

function parseStorySectionLines(storyText, headingPattern) {
  if (typeof storyText !== 'string') return [];
  const match = headingPattern.exec(storyText);
  if (!match) return [];
  const rest = storyText.slice(match.index + match[0].length);
  const end = /^##[ \t]+/m.exec(rest);
  const body = (end ? rest.slice(0, end.index) : rest).trim();
  if (!body) return [];
  const items = [];
  let current = null;
  for (const raw of body.split(/\r?\n/)) {
    const trimmed = raw.trim();
    if (!trimmed || trimmed.startsWith('<!--')) {
      if (current) { items.push(current.join(' ')); current = null; }
      continue;
    }
    const bullet = /^(?:[-*+]|[1-9][0-9]*[.)])[ \t]+(.+)$/.exec(trimmed);
    if (bullet) {
      if (current) items.push(current.join(' '));
      current = [bullet[1].trim()];
    } else if (current) {
      current.push(trimmed);
    } else {
      items.push(trimmed);
    }
  }
  if (current) items.push(current.join(' '));
  return items.filter(line => !/^none\.?$/i.test(line));
}

function parseStoryBoundaryPrompts(storyText, storyPath, visible) {
  if (typeof storyText !== 'string') return [];
  const found = new Set();
  for (const match of storyText.matchAll(/```json[ \t]+pdd-boundary[ \t]*\r?\n([\s\S]*?)```/gi)) {
    try {
      const parsed = JSON.parse(match[1]);
      for (const p of Array.isArray(parsed?.prompts) ? parsed.prompts : []) {
        if (typeof p === 'string') {
          const norm = posix.normalize(p);
          if (visible.has(norm) && norm.endsWith('.prompt.md')) found.add(norm);
        }
      }
    } catch { /* advisory reader never fails on malformed blocks */ }
  }
  for (const link of extractFragmentLinks(storyText, storyPath, visible)) found.add(link.target);
  for (const match of storyText.matchAll(/(?:^|[\s`"'([])([A-Za-z0-9_./-]+\.prompt\.md)(?=$|[\s`"'),.:;\]])/gm)) {
    const norm = posix.normalize(match[1]);
    if (visible.has(norm)) found.add(norm);
  }
  return [...found].sort();
}

function stemToken(word) {
  let w = word.toLowerCase();
  for (const suffix of ['ations', 'ation', 'ments', 'ment', 'ities', 'ity', 'iness', 'ning', 'ings', 'ing', 'edly', 'ed', 'ies', 'ves', 'ses', 'es', 's']) {
    if (w.length - suffix.length >= 4 && w.endsWith(suffix)) {
      if (suffix === 'ies') w = `${w.slice(0, -3)}y`;
      else if (suffix === 'ves') w = `${w.slice(0, -3)}f`;
      else if (suffix === 'ses') w = `${w.slice(0, -2)}`;
      else w = w.slice(0, -suffix.length);
      break;
    }
  }
  return w.length >= 5 ? w.slice(0, 5) : w;
}

function salientRuleTokens(text, excludedPromptPaths = []) {
  const excludedStems = new Set();
  for (const p of excludedPromptPaths) {
    const base = basename(p, '.prompt.md').toLowerCase();
    for (const part of base.split(/[^a-z0-9]+/)) {
      if (part.length >= 4) excludedStems.add(stemToken(part));
    }
  }
  const rawWords = String(text ?? '')
    .replace(/`[^`]*`/g, ' ')
    .replace(/[A-Za-z0-9_./-]+\.(?:prompt\.md|md|json|mjs|js|ts|py)/gi, ' ')
    .replace(/([a-z])([A-Z])/g, '$1 $2')
    .toLowerCase()
    .split(/[^a-z0-9]+/)
    .filter(token => token.length >= 4 && !/^\d+$/.test(token) && !STOPWORDS.has(token));
  const allStems = [...new Set(rawWords.map(stemToken))];
  const withoutTopic = allStems.filter(stem => !excludedStems.has(stem));
  return withoutTopic.length >= 2 ? withoutTopic : allStems;
}

function explicitIdentifiers(text) {
  const ids = [];
  for (const match of String(text ?? '').matchAll(/`([^`\n]{3,64})`/g)) {
    const token = match[1].trim();
    if (!token || /\s/.test(token) || token.endsWith('.md') || token.endsWith('.json')) continue;
    if (/[_-]|[A-Z0-9]|^\//.test(token)) ids.push(token.replace(/^\//, ''));
  }
  return [...new Set(ids)];
}

function proseStemsOf(proseText) {
  const words = String(proseText ?? '')
    .replace(/([a-z])([A-Z])/g, '$1 $2')
    .toLowerCase()
    .split(/[^a-z0-9]+/)
    .filter(token => token.length >= 4);
  return new Set(words.map(stemToken));
}

function ruleConnectedToSources(ruleText, loadedPromptRecords) {
  if (!loadedPromptRecords.length) return { connected: false, reason: 'no prompt source loaded' };
  const combinedProse = loadedPromptRecords.map(item => item.proseText).join('\n');
  const combinedRaw = loadedPromptRecords.map(item => item.rawText).join('\n');
  const identifiers = explicitIdentifiers(ruleText);
  if (identifiers.length) {
    const missingIds = identifiers.filter(id => !combinedRaw.toLowerCase().includes(id.toLowerCase()));
    if (missingIds.length === identifiers.length) {
      return { connected: false, reason: `missing \`${missingIds[0]}\` in selected source` };
    }
  }
  const stems = salientRuleTokens(ruleText, loadedPromptRecords.map(item => item.path));
  if (!stems.length) return { connected: true, reason: null };
  const corpusStems = proseStemsOf(combinedProse);
  const matched = stems.filter(stem => corpusStems.has(stem));
  if (matched.length === 0) {
    return { connected: false, reason: 'owning rule absent from selected source prose' };
  }
  return { connected: true, reason: null };
}

function pointerGet(rootValue, pointer) {
  if (typeof pointer !== 'string') return { found: false, value: undefined };
  if (pointer === '') return { found: rootValue !== undefined, value: rootValue };
  if (!pointer.startsWith('/')) return { found: false, value: undefined };
  let cur = rootValue;
  for (const rawPart of pointer.slice(1).split('/')) {
    const part = rawPart.replace(/~1/g, '/').replace(/~0/g, '~');
    if (Array.isArray(cur)) {
      const idx = Number(part);
      if (!Number.isInteger(idx) || idx < 0 || idx >= cur.length) return { found: false, value: undefined };
      cur = cur[idx];
    } else if (isObject(cur) && Object.hasOwn(cur, part)) {
      cur = cur[part];
    } else {
      return { found: false, value: undefined };
    }
  }
  return { found: true, value: cur };
}

function valueAppearsSupplied(expected, supplied, checkPath) {
  if (expected === undefined || expected === null || typeof expected === 'boolean') return false;
  if (typeof expected === 'number' && (expected === 0 || expected === 1)) return false;
  if (typeof expected === 'string' && expected.length === 0) return false;
  if (typeof checkPath === 'string' && checkPath.startsWith('/')) {
    const direct = pointerGet(supplied, checkPath);
    if (direct.found && isDeepStrictEqual(direct.value, expected)) return true;
  }
  const leaf = typeof checkPath === 'string' && checkPath.includes('/') ? checkPath.split('/').filter(Boolean).at(-1) : null;
  let matched = false;
  const visit = (node, keyName = null) => {
    if (matched || node === null || node === undefined) return;
    if (isDeepStrictEqual(node, expected)) {
      if (typeof expected === 'object' || !leaf || keyName === leaf || (typeof expected === 'string' && expected.length >= 3)) {
        matched = true;
        return;
      }
    }
    if (Array.isArray(node)) for (const item of node) visit(item, keyName);
    else if (isObject(node)) for (const [k, v] of Object.entries(node)) visit(v, k);
  };
  visit(supplied, null);
  return matched;
}

function looksLikeReturnedEffectClaim(check) {
  if (!isObject(check) || !['result', 'world'].includes(check.target)) return false;
  const segments = String(check.path ?? '').split('/').filter(Boolean);
  if (segments.some(seg => EFFECT_SEGMENT_RE.test(seg))) return true;
  const val = check.value;
  if (Array.isArray(val) && val.length > 0 && val.some(item => isObject(item) && Object.keys(item).some(k => EFFECT_KEY_RE.test(k)))) {
    return true;
  }
  if (isObject(val) && Object.keys(val).some(k => EFFECT_KEY_RE.test(k))) return true;
  return false;
}

function isZeroCallCheck(check) {
  if (!isObject(check) || check.target !== 'calls') return false;
  if ((check.op === 'equals' || check.op === 'count' || check.op === 'at_most' || check.op === 'lte') && check.value === 0) return true;
  if (check.op === 'equals' && Array.isArray(check.value) && check.value.length === 0) return true;
  return false;
}

function instrumentedPortsForStep(doc, step, loadedPromptRecords) {
  const ports = new Set();
  for (const rec of loadedPromptRecords) {
    for (const res of Array.isArray(rec.interface?.resources) ? rec.interface.resources : []) {
      if (typeof res?.name === 'string' && res.name) {
        const ops = Array.isArray(res.operations) ? res.operations : [];
        if (ops.length) for (const op of ops) { if (typeof op?.name === 'string') ports.add(`${res.name}.${op.name}`); }
        else ports.add(res.name);
      }
    }
    for (const call of Array.isArray(rec.interface?.calls) ? rec.interface.calls : []) {
      if (typeof call?.target === 'string' && call?.target_operation) ports.add(`${basename(call.target, '.prompt.md')}.${call.target_operation}`);
    }
  }
  for (const sim of [doc?.simulation, step?.simulation_overrides]) {
    if (!isObject(sim)) continue;
    for (const [k, v] of Object.entries(sim)) {
      if ((k === 'resources' || k === 'calls' || k === 'ports') && isObject(v)) {
        for (const sub of Object.keys(v)) ports.add(sub);
      } else if (k !== '$simulation') {
        ports.add(k);
      }
    }
  }
  return [...ports].sort();
}

function classifyStepCheck(check, doc, step, receiptCheck = null) {
  if (!isObject(check)) return { kind: 'model-returned value', zeroCalls: false, needsPortOrNative: false, portPath: null };
  if (check.target === 'calls') {
    const zero = isZeroCallCheck(check) || receiptCheck?.actual === 0 || (Array.isArray(receiptCheck?.actual) && receiptCheck.actual.length === 0);
    const portLabel = typeof check.path === 'string' && check.path ? check.path.replace(/^\/(?:resources|internal)\//, '').replace(/^\//, '') : 'port';
    return { kind: 'observed simulated port call', zeroCalls: zero, needsPortOrNative: false, portPath: portLabel || 'port' };
  }
  if (check.ref_target === 'input') {
    return { kind: 'supplied fact', zeroCalls: false, needsPortOrNative: false, portPath: null };
  }
  if (check.target === 'world' && Object.hasOwn(check, 'value')) {
    const initial = pointerGet(doc?.initial_world, check.path ?? '');
    if (initial.found && isDeepStrictEqual(initial.value, check.value)) {
      return { kind: 'supplied fact', zeroCalls: false, needsPortOrNative: false, portPath: null };
    }
  }
  if (['result', 'world'].includes(check.target) && Object.hasOwn(check, 'value') && ['equals', 'contains'].includes(check.op)) {
    if (valueAppearsSupplied(check.value, step?.input, check.path) || (check.target === 'result' && valueAppearsSupplied(check.value, doc?.initial_world, check.path))) {
      return { kind: 'supplied fact', zeroCalls: false, needsPortOrNative: false, portPath: null };
    }
  }
  return {
    kind: 'model-returned value',
    zeroCalls: false,
    needsPortOrNative: looksLikeReturnedEffectClaim(check),
    portPath: null,
  };
}

function gitChangedPaths(rootReal, visible) {
  const head = spawnSync('git', ['rev-parse', '--verify', 'HEAD^{commit}'], { cwd: rootReal, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (head.status !== 0) return [...visible].sort();
  const paths = new Set();
  const collect = args => {
    const out = spawnSync('git', args, { cwd: rootReal, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
    if (out.status === 0 && out.stdout) {
      for (const item of out.stdout.split('\0')) if (item && visible.has(item)) paths.add(item);
    }
  };
  collect(['diff', '--no-color', '--no-renames', '--name-only', '-z', 'HEAD']);
  collect(['ls-files', '--others', '--exclude-standard', '-z']);
  let comparedBase = false;
  for (const baseRef of ['refs/remotes/origin/main', 'refs/heads/main']) {
    const mb = spawnSync('git', ['merge-base', 'HEAD', baseRef], { cwd: rootReal, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    const sha = mb.status === 0 ? mb.stdout.trim() : '';
    if (sha) {
      if (sha !== head.stdout.trim()) { collect(['diff', '--no-color', '--no-renames', '--name-only', '-z', sha]); comparedBase = true; }
      break;
    }
  }
  if (!comparedBase) {
    const parent = spawnSync('git', ['rev-parse', '--verify', 'HEAD~1^{commit}'], { cwd: rootReal, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    if (parent.status !== 0) for (const item of visible) paths.add(item);
  }
  return [...paths].sort();
}

function readSavedBatchDiagnostics(rootReal, { since = 0, env = process.env } = {}) {
  const byTest = new Map();
  const divergences = [];
  let maxSamples = 0;
  let agreedMultiSample = 0;
  const stateRoot = resolve(env?.PDD_STATE_DIR || join(env?.HOME || homedir(), '.pdd', 'runtime'));
  const batchesDir = join(stateRoot, 'batches');
  let names = [];
  try { names = readdirSync(batchesDir).filter(name => BATCH_NAME.test(name)).sort(); } catch { return { byTest, divergences, sampleSummary: null }; }
  for (const name of names) {
    const folder = join(batchesDir, name);
    let batch;
    try { batch = JSON.parse(readFileSync(join(folder, 'batch.json'), 'utf8')); } catch { continue; }
    if (!isObject(batch) || typeof batch.root !== 'string' || !Array.isArray(batch.rows)) continue;
    if (batch.intent && batch.intent !== 'check') continue;
    if (canonicalRoot(batch.root) !== rootReal) continue;
    const createdAt = Date.parse(batch.created_at) || 0;
    const batchAt = Math.max(createdAt, ...batch.rows.map(r => Number.isFinite(r?.ended_at) ? r.ended_at : 0));
    if (since > 0 && batchAt > 0 && batchAt < since) continue;
    for (const row of batch.rows) {
      if (!isObject(row) || typeof row.test !== 'string' || !Array.isArray(row.request_ids) || !row.request_ids.length) continue;
      const reqId = row.request_ids.at(-1);
      if (typeof reqId !== 'string' || !UUID_RE.test(reqId)) continue;
      let answer;
      try { answer = JSON.parse(readFileSync(join(folder, `${reqId}.json`), 'utf8')); } catch { continue; }
      const report = answer?.result?.report;
      if (!isObject(report)) continue;
      const samples = Array.isArray(report.samples) ? report.samples.filter(isObject) : [];
      if (samples.length > maxSamples) maxSamples = samples.length;
      if (samples.length > 1) {
        const baseSteps = Array.isArray(samples[0].steps) ? samples[0].steps : [];
        let differed = false;
        for (let idx = 0; idx < baseSteps.length; idx += 1) {
          const first = baseSteps[idx];
          const stepId = cleanOneLine(first?.step_id || `step-${idx + 1}`);
          const surfaces = new Set();
          for (let s = 1; s < samples.length; s += 1) {
            const other = Array.isArray(samples[s].steps) ? samples[s].steps[idx] : null;
            if (!other) continue;
            if (!isDeepStrictEqual(first?.result, other?.result)) surfaces.add('result');
            if (!isDeepStrictEqual(first?.error, other?.error)) surfaces.add('error');
            if (!isDeepStrictEqual(first?.world, other?.world)) surfaces.add('world');
            if (!isDeepStrictEqual(first?.calls, other?.calls)) surfaces.add('calls');
            const passA = (Array.isArray(first?.checks) ? first.checks : []).map(c => Boolean(c?.passed));
            const passB = (Array.isArray(other?.checks) ? other.checks : []).map(c => Boolean(c?.passed));
            if (!isDeepStrictEqual(passA, passB)) surfaces.add('verdict');
          }
          if (surfaces.size) {
            differed = true;
            divergences.push(`${stepId} varied across ${samples.length} samples (${[...surfaces].join(', ')})`);
          }
        }
        if (!differed) agreedMultiSample = Math.max(agreedMultiSample, samples.length);
      }
      for (const rStep of Array.isArray(report?.rerun?.steps) ? report.rerun.steps : []) {
        if (!isObject(rStep)) continue;
        const stepId = cleanOneLine(rStep.step_id || 'step');
        if (Array.isArray(rStep.changed_paths) && rStep.changed_paths.length) {
          divergences.push(`${stepId} rerun varied (${rStep.changed_paths.slice(0, 2).map(cleanOneLine).join(', ')})`);
        } else if (Number.isInteger(rStep.runs) && rStep.runs > 1 && Number.isInteger(rStep.failed) && rStep.failed > 0 && rStep.failed < rStep.runs) {
          divergences.push(`${stepId} split across ${rStep.runs} reruns (${rStep.failed} failed)`);
        }
      }
      for (const div of Array.isArray(report?.divergences) ? report.divergences : []) {
        const note = typeof div === 'string' ? cleanOneLine(div) : isObject(div) ? cleanOneLine(div.summary || div.step_id || div.path || '') : '';
        if (note) divergences.push(note);
      }
      const stepObservations = new Map();
      const primarySteps = Array.isArray(samples[0]?.steps) ? samples[0].steps : [];
      for (const s of primarySteps) {
        if (!isObject(s) || typeof s.step_id !== 'string') continue;
        let observedCallTotal = null;
        if (isObject(s.calls)) {
          let sum = 0, seenNumber = false;
          const countCalls = obj => {
            for (const val of Object.values(obj)) {
              if (typeof val === 'number' && Number.isFinite(val)) { sum += val; seenNumber = true; }
              else if (Array.isArray(val)) { sum += val.length; seenNumber = true; }
              else if (isObject(val)) countCalls(val);
            }
          };
          countCalls(s.calls);
          if (seenNumber || Object.keys(s.calls).length === 0) observedCallTotal = sum;
        }
        stepObservations.set(s.step_id, {
          observedCallTotal,
          checks: Array.isArray(s.checks) ? s.checks : [],
        });
      }
      byTest.set(row.test, { state: answer?.state ?? null, stepObservations });
    }
  }
  const uniqueDivergences = [...new Set(divergences)];
  const sampleSummary = uniqueDivergences.length
    ? `advisory divergence: ${uniqueDivergences.slice(0, 2).join('; ')}`
    : agreedMultiSample > 1
      ? `${agreedMultiSample}/${agreedMultiSample} samples agreed`
      : maxSamples === 1
        ? 'single-sample check'
        : null;
  return { byTest, divergences: uniqueDivergences, sampleSummary };
}

function readPromptRecord(rootReal, visible, path, cache) {
  if (cache.has(path)) return cache.get(path);
  const rawText = readSafeText(rootReal, path);
  if (rawText === null) { cache.set(path, null); return null; }
  let parsed = null;
  try { parsed = readPrompt(rootReal, visible, path); } catch { parsed = null; }
  const iface = parsed?.interface ?? null;
  const proseText = proseWithoutInterface(rawText);
  const rec = {
    path,
    rawText,
    proseText,
    proseLoc: countProseLines(rawText),
    interface: iface,
    kind: iface?.kind === 'native-only' ? 'native-only' : parsed?.blocks?.length ? 'runtime' : 'plain',
    reason: iface?.kind === 'native-only' && typeof iface.reason === 'string' ? cleanOneLine(iface.reason) : null,
    operations: Array.isArray(iface?.entries)
      ? iface.entries.map(e => e?.operation).filter(op => typeof op === 'string' && op.trim())
      : [],
    headings: promptHeadingSlugs(rawText),
  };
  cache.set(path, rec);
  return rec;
}

function resolveScenarioClosure(doc, storyBoundaryPrompts, rootReal, visible, promptCache) {
  const entryCandidates = new Set([
    ...(typeof doc?.entry_path === 'string' ? [doc.entry_path] : []),
    ...(Array.isArray(doc?.entry_paths) ? doc.entry_paths.filter(p => typeof p === 'string') : []),
    ...storyBoundaryPrompts,
  ].filter(p => visible.has(p) && p.endsWith('.prompt.md')));

  const seeds = new Set();
  for (const step of Array.isArray(doc?.steps) ? doc.steps : []) {
    if (typeof step?.entry_path === 'string' && visible.has(step.entry_path) && step.entry_path.endsWith('.prompt.md')) {
      seeds.add(step.entry_path);
      continue;
    }
    if (typeof step?.operation === 'string' && step.operation) {
      let matchedOwner = null;
      for (const candidate of entryCandidates) {
        const rec = readPromptRecord(rootReal, visible, candidate, promptCache);
        if (rec?.operations.includes(step.operation)) { matchedOwner = candidate; break; }
      }
      if (matchedOwner) seeds.add(matchedOwner);
      else if (entryCandidates.size === 1) seeds.add([...entryCandidates][0]);
    }
  }
  for (const ctx of Array.isArray(doc?.context) ? doc.context : []) {
    if (typeof ctx === 'string' && ctx.endsWith('.prompt.md') && visible.has(ctx)) seeds.add(ctx);
    else if (isObject(ctx) && Array.isArray(ctx.paths)) {
      for (const p of ctx.paths) if (typeof p === 'string' && p.endsWith('.prompt.md') && visible.has(p)) seeds.add(p);
    }
  }

  const loaded = new Set();
  const brokenFragments = [];
  const queue = [...seeds];
  while (queue.length) {
    const current = queue.shift();
    if (!current || loaded.has(current) || !visible.has(current)) continue;
    const rec = readPromptRecord(rootReal, visible, current, promptCache);
    if (!rec) continue;
    loaded.add(current);
    const targets = promptMarkdownTargets(rec.rawText, current, visible);
    for (const target of targets) if (!loaded.has(target)) queue.push(target);
    const depLinks = extractFragmentLinks(dependenciesSection(rec.rawText), current, visible);
    for (const link of depLinks) {
      if (!loaded.has(link.target)) queue.push(link.target);
      if (link.fragment) {
        const targetRec = readPromptRecord(rootReal, visible, link.target, promptCache);
        if (targetRec && !targetRec.headings.has(link.fragment)) {
          brokenFragments.push({ from: current, target: link.target, fragment: link.fragment });
        }
      }
    }
    for (const call of Array.isArray(rec.interface?.calls) ? rec.interface.calls : []) {
      if (typeof call?.target === 'string' && call.target.endsWith('.prompt.md') && visible.has(call.target) && !loaded.has(call.target)) {
        queue.push(call.target);
      }
    }
  }
  return {
    entryPrompts: [...seeds].sort(),
    loadedPrompts: [...loaded].sort(),
    loadedRecords: [...loaded].sort().map(p => readPromptRecord(rootReal, visible, p, promptCache)).filter(Boolean),
    brokenFragments,
  };
}

export function buildHumanBoundaryCard({
  root,
  focusPrompt = null,
  promptPaths = [],
  storyPaths = [],
  changedPaths = null,
  since = 0,
  env = process.env,
} = {}) {
  if (!root || typeof root !== 'string') return null;
  const rootReal = canonicalRoot(root);
  let visibleList = [];
  try { visibleList = gitFiles(rootReal); } catch { return null; }
  const visible = new Set(visibleList.filter(path => !path.startsWith('test/fixtures/')));
  const promptCache = new Map();

  const sliceChanged = Array.isArray(changedPaths)
    ? changedPaths.filter(p => typeof p === 'string' && visible.has(p))
    : gitChangedPaths(rootReal, visible);

  let foundTests = { tests: [], stories: [], nativeSelections: [] };
  try {
    foundTests = findTests({ root: rootReal, files: [...visible], excludeFixtureProjects: true });
  } catch {
    foundTests = { tests: [], stories: [], nativeSelections: [] };
  }

  const validTests = [];
  for (const entry of foundTests.tests ?? []) {
    if (entry?.doc && isObject(entry.doc) && entry.doc.schema_version === TEST_SCHEMA) {
      validTests.push(entry);
      continue;
    }
    if (typeof entry?.path === 'string' && visible.has(entry.path)) {
      const raw = readSafeText(rootReal, entry.path);
      if (raw) {
        try {
          const parsed = parseScenarioJson(raw);
          if (isObject(parsed) && parsed.schema_version === TEST_SCHEMA) validTests.push({ ...entry, doc: parsed });
        } catch { /* ignore unreadable JSON */ }
      }
    }
  }

  const storyTextCache = new Map();
  const readStory = path => {
    if (storyTextCache.has(path)) return storyTextCache.get(path);
    const text = isStoryPath(path) && visible.has(path) ? readSafeText(rootReal, path) : null;
    storyTextCache.set(path, text);
    return text;
  };

  const scenarioClosures = new Map();
  for (const testEntry of validTests) {
    const sPath = typeof testEntry.doc?.story_path === 'string' ? testEntry.doc.story_path : testEntry.storyPath;
    const sText = sPath ? readStory(sPath) : null;
    const boundaryPrompts = sText ? parseStoryBoundaryPrompts(sText, sPath, visible) : [];
    scenarioClosures.set(testEntry.path, {
      testEntry,
      storyPath: sPath || null,
      boundaryPrompts,
      ...resolveScenarioClosure(testEntry.doc, boundaryPrompts, rootReal, visible, promptCache),
    });
  }

  // Select relevant Stories for this slice (approve focusPrompt vs. PR 1 slice).
  const candidateStoryPaths = new Set();
  for (const s of storyPaths ?? []) if (typeof s === 'string' && isStoryPath(s) && visible.has(s)) candidateStoryPaths.add(s);

  if (focusPrompt) {
    for (const info of scenarioClosures.values()) {
      if (info.loadedPrompts.includes(focusPrompt) || info.boundaryPrompts.includes(focusPrompt)) {
        if (info.storyPath) candidateStoryPaths.add(info.storyPath);
      }
    }
    for (const p of visible) {
      if (!isStoryPath(p)) continue;
      const text = readStory(p);
      if (text && hasAcceptance(text) && parseStoryBoundaryPrompts(text, p, visible).includes(focusPrompt)) {
        candidateStoryPaths.add(p);
      }
    }
    const focusRec = readPromptRecord(rootReal, visible, focusPrompt, promptCache);
    if (focusRec?.kind !== 'native-only') {
      for (const p of sliceChanged) {
        if (isLintableStoryPath(p) && readStory(p) && hasAcceptance(readStory(p))) candidateStoryPaths.add(p);
      }
      for (const info of scenarioClosures.values()) {
        if (sliceChanged.includes(info.testEntry.path) && info.storyPath) candidateStoryPaths.add(info.storyPath);
      }
    }
  } else {
    for (const p of sliceChanged) {
      if (isLintableStoryPath(p) && readStory(p) && hasAcceptance(readStory(p))) candidateStoryPaths.add(p);
    }
    for (const info of scenarioClosures.values()) {
      if (sliceChanged.includes(info.testEntry.path) && info.storyPath) candidateStoryPaths.add(info.storyPath);
    }
  }

  const selectedStories = [...candidateStoryPaths].sort().filter(p => readStory(p) !== null);
  const selectedScenarios = [...scenarioClosures.values()].filter(info =>
    (info.storyPath && selectedStories.includes(info.storyPath))
    || (!focusPrompt && sliceChanged.includes(info.testEntry.path))
    || (focusPrompt && info.loadedPrompts.includes(focusPrompt)),
  );

  // Collect owning prompts in scope.
  const owningPromptSet = new Set();
  if (focusPrompt && visible.has(focusPrompt)) owningPromptSet.add(focusPrompt);
  for (const p of promptPaths ?? []) {
    if (typeof p === 'string' && p.endsWith('.prompt.md') && visible.has(p) && !isTestPromptPath(p)) owningPromptSet.add(p);
  }
  if (!focusPrompt || selectedStories.length > 0 || selectedScenarios.length > 0) {
    for (const p of sliceChanged) {
      if (p.endsWith('.prompt.md') && visible.has(p) && !isTestPromptPath(p)) owningPromptSet.add(p);
    }
  }
  for (const sPath of selectedStories) {
    const sText = readStory(sPath);
    for (const p of parseStoryBoundaryPrompts(sText, sPath, visible)) {
      if (!isTestPromptPath(p)) owningPromptSet.add(p);
    }
  }

  const owningRecords = [...owningPromptSet]
    .sort()
    .map(p => readPromptRecord(rootReal, visible, p, promptCache))
    .filter(Boolean);

  const allLoadedPaths = new Set(selectedScenarios.flatMap(s => s.loadedPrompts));
  const allRelevantPromptRecords = [...new Set([...owningPromptSet, ...allLoadedPaths])]
    .sort()
    .map(p => readPromptRecord(rootReal, visible, p, promptCache))
    .filter(Boolean);

  const nativeOnlyRecords = allRelevantPromptRecords.filter(r => r.kind === 'native-only');
  const checkableOwners = owningRecords.filter(r => r.kind !== 'native-only');
  const unloadedOwners = selectedScenarios.length > 0
    ? checkableOwners.map(r => r.path).filter(p => !allLoadedPaths.has(p))
    : [];

  const batchDiag = readSavedBatchDiagnostics(rootReal, { since, env });

  // Build policy items & per-rule/criterion provenance rows.
  const policyItems = [];
  const provenanceRows = [];
  const nativeValidatedStories = new Set((foundTests.nativeSelections ?? []).map(item => item.storyPath));

  for (const sPath of selectedStories) {
    const sText = readStory(sPath) ?? '';
    const title = cleanOneLine(sText.split(/\r?\n/).find(l => l.startsWith('# '))?.slice(2) || basename(sPath, '.md'));
    const criteriaTexts = storyCriteria(sText);
    const rulesTexts = parseStorySectionLines(sText, /^##[ \t]+Rules to check[ \t]*\r?$/im);
    const hasNativeSection = nativeValidatedStories.has(sPath) || /^##[ \t]+Native validation[ \t]*\r?$/im.test(sText);
    const storyLinks = extractFragmentLinks(sText, sPath, visible);
    const brokenStoryFragments = storyLinks.filter(link => {
      if (!link.fragment) return false;
      const targetRec = readPromptRecord(rootReal, visible, link.target, promptCache);
      return targetRec && !targetRec.headings.has(link.fragment);
    });

    for (const rule of rulesTexts) policyItems.push({ kind: 'rule', story: title, text: clipText(rule, 88) });
    for (const [idx, crit] of criteriaTexts.entries()) {
      policyItems.push({ kind: 'criterion', id: `AC${idx + 1}`, story: title, text: clipText(crit, 88) });
    }

    const storyScenarios = selectedScenarios.filter(s => s.storyPath === sPath);
    if (!storyScenarios.length) {
      if (hasNativeSection || (nativeOnlyRecords.length > 0 && checkableOwners.length === 0)) {
        const ownerLabel = nativeOnlyRecords.map(r => r.path).join(', ') || `${sPath} (native validation)`;
        for (const [idx, crit] of criteriaTexts.entries()) {
          provenanceRows.push({
            label: `AC${idx + 1}`,
            summary: clipText(crit, 54),
            owner: ownerLabel,
            missingConnection: false,
            missingReason: null,
            observations: ['native test'],
            needsPortOrNative: false,
            zeroPortCalls: false,
            priority: 3,
          });
        }
      } else {
        const unexercised = checkableOwners.map(r => r.path).join(', ') || 'owning prompt';
        for (const [idx, crit] of criteriaTexts.entries()) {
          provenanceRows.push({
            label: `AC${idx + 1}`,
            summary: clipText(crit, 54),
            owner: `missing owner connection (no scenario loads ${unexercised})`,
            missingConnection: true,
            missingReason: `no scenario loads ${unexercised}`,
            observations: ['none'],
            needsPortOrNative: false,
            zeroPortCalls: false,
            priority: 0,
          });
        }
      }
      continue;
    }

    // Evaluate each criterion across the Story's scenarios.
    for (const [idx, critText] of criteriaTexts.entries()) {
      const fallbackId = `AC${idx + 1}`;
      const matchedChecks = [];
      const loadedForCrit = new Map();
      const brokenForCrit = [...brokenStoryFragments];
      let instrumentedZeroCalls = false;

      for (const scen of storyScenarios) {
        const doc = scen.testEntry.doc;
        const docCriteria = Array.isArray(doc?.criteria) ? doc.criteria : [];
        const docCrit = docCriteria.find(c => c?.text === critText) ?? docCriteria[idx];
        const critId = typeof docCrit?.id === 'string' && docCrit.id ? docCrit.id : fallbackId;
        const savedTest = batchDiag.byTest.get(scen.testEntry.path);
        brokenForCrit.push(...scen.brokenFragments);

        for (const step of Array.isArray(doc?.steps) ? doc.steps : []) {
          const stepChecks = (Array.isArray(step?.checks) ? step.checks : []).filter(c => c?.criterion_id === critId);
          if (!stepChecks.length) continue;
          for (const rec of scen.loadedRecords) loadedForCrit.set(rec.path, rec);
          const savedStep = savedTest?.stepObservations?.get(step.step_id);
          const instrumented = instrumentedPortsForStep(doc, step, scen.loadedRecords);
          const classified = stepChecks.map((chk, cIdx) => {
            const receiptChk = savedStep?.checks?.find(rc => rc?.criterion_id === critId && rc?.target === chk?.target && rc?.path === chk?.path) ?? savedStep?.checks?.[cIdx] ?? null;
            return classifyStepCheck(chk, doc, step, receiptChk);
          });
          if (instrumented.length > 0 && !classified.some(c => c.kind === 'observed simulated port call')) {
            if (savedStep?.observedCallTotal === 0 || savedStep === undefined) instrumentedZeroCalls = true;
          }
          matchedChecks.push(...classified);
        }
      }

      const loadedRecords = [...loadedForCrit.values()];
      const obsSet = new Set(matchedChecks.map(c => c.kind));
      if (hasNativeSection) obsSet.add('native test');
      const hasPortOrNative = obsSet.has('observed simulated port call') || obsSet.has('native test');
      const needsPortOrNative = !hasPortOrNative && matchedChecks.some(c => c.needsPortOrNative);
      const explicitZeroCalls = matchedChecks.some(c => c.zeroCalls);
      const zeroPortCalls = explicitZeroCalls || instrumentedZeroCalls;

      // Determine owner connection for this criterion!
      let missingConnection = false;
      let missingReason = null;
      if (focusPrompt && focusRecIsCheckable(focusPrompt, owningRecords) && !loadedForCrit.has(focusPrompt)) {
        missingConnection = true;
        const selectedLabel = loadedRecords.map(r => r.path).join(', ') || 'none';
        missingReason = `unloaded owning source ${focusPrompt}; scenario selects ${selectedLabel}`;
      } else if (brokenForCrit.length > 0) {
        missingConnection = true;
        const b = brokenForCrit[0];
        missingReason = `missing section #${b.fragment} in ${b.target}`;
      } else {
        const ruleConn = ruleConnectedToSources(critText, loadedRecords);
        if (!ruleConn.connected) {
          missingConnection = true;
          const unloadedHint = unloadedOwners.length ? `; unloaded in slice: ${unloadedOwners.join(', ')}` : '';
          missingReason = `${ruleConn.reason}${unloadedHint}`;
        } else if (unloadedOwners.length > 0) {
          // Check if an unloaded owner actually owns domain terms missing or more specific than a simulator stub.
          const unloadedRecords = unloadedOwners.map(p => readPromptRecord(rootReal, visible, p, promptCache)).filter(Boolean);
          const loadedPaths = loadedRecords.map(r => r.path);
          if (loadedPaths.length && loadedPaths.every(p => /simulat|mock|stub|fake|harness/i.test(basename(p)))) {
            const unloadedMatch = unloadedRecords.filter(rec => ruleConnectedToSources(critText, [rec]).connected);
            if (unloadedMatch.length) {
              missingConnection = true;
              missingReason = `unloaded owning source ${unloadedMatch.map(r => r.path).join(', ')}; scenario only runs ${loadedPaths.join(', ')}`;
            }
          }
        }
      }

      const observations = formatObservationList(obsSet, { needsPortOrNative, explicitZeroCalls, instrumentedZeroCalls });
      const ownerDisplay = missingConnection
        ? `missing owner connection (${missingReason})`
        : loadedRecords.map(r => r.path).join(' -> ') || 'unmapped';
      const priority = missingConnection ? 0 : needsPortOrNative ? 1 : zeroPortCalls ? 2 : 3;

      provenanceRows.push({
        label: fallbackId,
        summary: clipText(critText, 50),
        owner: ownerDisplay,
        missingConnection,
        missingReason,
        observations,
        needsPortOrNative,
        zeroPortCalls,
        priority,
      });
    }

    // Also check explicit `## Rules to check` invariants so removed owning rules are always caught!
    const allStoryLoadedRecords = [...new Map(storyScenarios.flatMap(s => s.loadedRecords.map(r => [r.path, r]))).values()];
    for (const [rIdx, ruleText] of rulesTexts.entries()) {
      const conn = ruleConnectedToSources(ruleText, allStoryLoadedRecords);
      const focusUnloaded = focusPrompt && focusRecIsCheckable(focusPrompt, owningRecords) && !allStoryLoadedRecords.some(r => r.path === focusPrompt);
      if (!conn.connected || focusUnloaded) {
        const selectedLabel = allStoryLoadedRecords.map(r => r.path).join(', ') || 'none';
        const reason = focusUnloaded
          ? `unloaded owning source ${focusPrompt}; scenario selects ${selectedLabel}`
          : `${conn.reason}${unloadedOwners.length ? `; unloaded: ${unloadedOwners.join(', ')}` : ''}`;
        provenanceRows.push({
          label: `Rule ${rIdx + 1}`,
          summary: clipText(ruleText, 50),
          owner: `missing owner connection (${reason})`,
          missingConnection: true,
          missingReason: reason,
          observations: hasNativeSection ? ['native test'] : ['unverified rule owner'],
          needsPortOrNative: false,
          zeroPortCalls: false,
          priority: 0,
        });
      }
    }
  }

  // Fallback policy summary when no Story exists in the slice (e.g. standalone prompt approval).
  if (!selectedStories.length && owningRecords.length) {
    for (const rec of owningRecords) {
      if (rec.kind === 'native-only') {
        policyItems.push({ kind: 'prompt', story: rec.path, text: `native-only boundary (${rec.reason || 'deterministic native tests'})` });
        provenanceRows.push({
          label: basename(rec.path, '.prompt.md'),
          summary: 'native-only boundary',
          owner: rec.path,
          missingConnection: false,
          missingReason: null,
          observations: ['native test'],
          needsPortOrNative: false,
          zeroPortCalls: false,
          priority: 3,
        });
      } else if (rec.operations.length) {
        policyItems.push({ kind: 'prompt', story: rec.path, text: `operations: ${rec.operations.join(', ')}` });
      } else {
        policyItems.push({ kind: 'prompt', story: rec.path, text: 'plain module prompt (verified through referencing Story or native tests)' });
      }
    }
  }

  // Verification split summary.
  const runtimeOps = allRelevantPromptRecords
    .filter(r => r.kind !== 'native-only')
    .map(r => r.operations.length ? `${r.path} (${r.operations.join(', ')})` : `${r.path} (plain)`);
  const nativeSplit = [
    ...nativeOnlyRecords.map(r => `${r.path} (native-only: ${clipText(r.reason || 'native tests', 60)})`),
    ...selectedStories.filter(s => nativeValidatedStories.has(s)).map(s => `${s} (Native validation)`),
  ];

  // Complexity budget & advisory sample divergences.
  const budgetPrompts = (focusPrompt ? owningRecords.filter(r => r.path === focusPrompt) : owningRecords);
  const maxPrompt = budgetPrompts.reduce((best, r) => (!best || r.proseLoc > best.proseLoc ? r : best), null);
  const oversizes = budgetPrompts.filter(r => r.proseLoc > 500).map(r =>
    `${r.path} ${r.proseLoc} prose LOC (${r.proseLoc > 1000 ? 'elevated >1000' : 'over 500 budget'})`,
  );
  const scenarioStepCounts = selectedScenarios.map(s => ({
    path: s.testEntry.path,
    steps: Array.isArray(s.testEntry.doc?.steps) ? s.testEntry.doc.steps.length : 0,
    lines: (readSafeText(rootReal, s.testEntry.path) ?? '').split('\n').length,
  }));
  const totalSteps = scenarioStepCounts.reduce((acc, item) => acc + item.steps, 0);
  const stepWarnings = scenarioStepCounts
    .filter(item => item.steps > 15 || item.lines > 1000)
    .map(item => `${item.path} (${item.steps > 15 ? `${item.steps} steps >15` : ''}${item.steps > 15 && item.lines > 1000 ? ', ' : ''}${item.lines > 1000 ? `${item.lines} lines >1000` : ''})`);

  const proseSummary = maxPrompt
    ? budgetPrompts.length === 1
      ? `prose ${maxPrompt.proseLoc} LOC${maxPrompt.proseLoc > 500 ? ' (over 500 budget)' : ' (<=500)'}`
      : `${budgetPrompts.length} prompts (max ${maxPrompt.proseLoc} prose LOC${maxPrompt.proseLoc > 500 ? ', over 500 budget' : ''})`
    : 'prose 0 LOC';
  const stepSummary = scenarioStepCounts.length
    ? `scenario steps ${totalSteps}${stepWarnings.length ? ` (advisory: ${stepWarnings.join('; ')})` : ' (<=15)'}`
    : 'scenario steps 0';

  return {
    advisory: true,
    stories: selectedStories,
    policyItems,
    unloadedOwners,
    selectedSources: [...allLoadedPaths].sort(),
    provenanceRows,
    verificationSplit: {
      runtime: runtimeOps,
      native: nativeSplit,
    },
    complexity: {
      proseSummary,
      stepSummary,
      warnings: [...oversizes, ...stepWarnings],
    },
    sampleSummary: batchDiag.sampleSummary,
    divergences: batchDiag.divergences,
  };
}

function focusRecIsCheckable(focusPrompt, owningRecords) {
  const rec = owningRecords.find(r => r.path === focusPrompt);
  return Boolean(rec && rec.kind !== 'native-only');
}

function formatObservationList(obsSet, { needsPortOrNative, explicitZeroCalls, instrumentedZeroCalls }) {
  const out = [];
  if (obsSet.has('observed simulated port call')) {
    out.push(explicitZeroCalls ? 'observed simulated port call (0 observed port calls)' : 'observed simulated port call');
  }
  if (obsSet.has('supplied fact')) out.push('supplied fact');
  if (obsSet.has('model-returned value')) {
    const notes = [];
    if (instrumentedZeroCalls) notes.push('0 observed port calls on instrumented port');
    if (needsPortOrNative) notes.push('port spy or native observation still needed');
    out.push(notes.length ? `model-returned value (${notes.join('; ')})` : 'model-returned value');
  } else if (instrumentedZeroCalls && !obsSet.has('observed simulated port call')) {
    out.push('0 observed port calls on instrumented port');
  }
  if (obsSet.has('native test')) out.push('native test');
  return out.length ? out : ['unverified'];
}

export function fitBoundaryLines(headerLines, bodyLines, footerLines, maxLines = BOUNDARY_CARD_MAX_LINES) {
  const totalFixed = headerLines.length + footerLines.length;
  if (totalFixed >= maxLines) return [...headerLines, ...footerLines].slice(0, maxLines);
  const room = maxLines - totalFixed;
  if (bodyLines.length <= room) return [...headerLines, ...bodyLines, ...footerLines];
  if (room === 1) return [...headerLines, `  … +${bodyLines.length} provenance rows omitted`, ...footerLines];
  return [
    ...headerLines,
    ...bodyLines.slice(0, room - 1),
    `  … +${bodyLines.length - (room - 1)} more checks omitted for 1-screen budget`,
    ...footerLines,
  ];
}

export function formatApproveBoundaryCard(card) {
  if (!isObject(card)) return [];
  const safeApproveLine = text => {
    const indent = /^ +/.exec(String(text ?? ''))?.[0] ?? '';
    const cleaned = `${indent}${cleanOneLine(text)}`;
    return /^(?:Text|Approve\s)/.test(cleaned) ? `  ${cleaned}` : cleaned;
  };

  const header = ['Human boundary card (advisory):'];
  const policies = Array.isArray(card.policyItems) ? card.policyItems : [];
  if (policies.length) {
    const shown = policies.slice(0, 3).map(p => `${p.id ? `${p.id}: ` : ''}${p.text}`);
    const extra = policies.length > 3 ? ` (+${policies.length - 3} more)` : '';
    header.push(`  Policy: ${shown.join(' | ')}${extra}`);
  }
  if (Array.isArray(card.unloadedOwners) && card.unloadedOwners.length) {
    const selected = Array.isArray(card.selectedSources) && card.selectedSources.length ? card.selectedSources.join(', ') : 'none';
    header.push(`  Owner gap: missing owner connection for ${card.unloadedOwners.join(', ')} (unloaded; scenario selects ${selected})`);
  }

  const rows = [...(Array.isArray(card.provenanceRows) ? card.provenanceRows : [])]
    .sort((a, b) => (a.priority ?? 3) - (b.priority ?? 3));
  const body = rows.length
    ? [
        '  Provenance:',
        ...rows.map(row =>
          `    - ${row.label} (${row.summary}): owner=${row.owner} · obs=${(row.observations ?? []).join(', ')}`,
        ),
      ]
    : ['  Provenance: no Story scenario checks in this slice (standalone / exploratory or native-tested).'];

  const rt = card.verificationSplit?.runtime ?? [];
  const nat = card.verificationSplit?.native ?? [];
  const rtText = rt.length ? rt.slice(0, 2).join(', ') + (rt.length > 2 ? ` (+${rt.length - 2} more)` : '') : 'none';
  const natText = nat.length ? nat.slice(0, 2).join(', ') + (nat.length > 2 ? ` (+${nat.length - 2} more)` : '') : 'code / unit tests';
  const samplePart = card.sampleSummary ? ` · ${card.sampleSummary}` : '';
  const footer = [
    `  Verification split: runtime=[${rtText}] · native=[${natText}]`,
    `  Budget & samples: ${card.complexity?.proseSummary ?? 'prose 0 LOC'} · ${card.complexity?.stepSummary ?? 'scenario steps 0'}${samplePart}`,
  ];

  return fitBoundaryLines(header, body, footer, BOUNDARY_CARD_MAX_LINES).map(safeApproveLine);
}
