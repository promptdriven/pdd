// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Layer-1 core check: verify every Story acceptance criterion has >=1 check in paired runtime JSON scenario(s).
import { posix } from 'node:path';
import { V1_SCENARIO_SCHEMA, criterionContentId, extractStoryCriteria } from '../../scenario-compile.mjs';
import { formatTeachingDetail, readSafeUtf8 } from './diagnostics.mjs';

const NON_SCENARIO_TEST_SUBDIR_RE = /(?:^|\/)(?:fixtures|__fixtures__|mocks|__mocks__|snapshots|__snapshots__|data|testdata|golden|cassettes)\//i;
const TEST_JSON_RE = /(?:^|\/)(?:tests?|__tests__)\/.*\.json$/i;
const TOOLING_CONFIG_JSON = new Set([
  'jsconfig.json', 'package.json', 'package-lock.json', 'npm-shrinkwrap.json', 'composer.json',
  'biome.json', 'deno.json', 'jsr.json', 'eslint.json', 'prettier.json', 'vitest.json', 'jest.json', 'babel.json',
]);

const normalizeCriterionText = text =>
  String(text ?? '')
    .replace(/[\u2018\u2019]/g, "'")
    .replace(/[\u201c\u201d]/g, '"')
    .replace(/\s+/g, ' ')
    .trim()
    .toLowerCase();

function isCandidateScenarioJson(relPath) {
  if (!TEST_JSON_RE.test(relPath) || NON_SCENARIO_TEST_SUBDIR_RE.test(relPath)) return false;
  const base = posix.basename(relPath).toLowerCase();
  if (TOOLING_CONFIG_JSON.has(base) || /^tsconfig.*\.json$/.test(base)) return false;
  if (base === 'cases.json' || base.endsWith('-cases.json')) return false;
  return true;
}

function findCriterionLines(storyText, acs) {
  const lines = String(storyText ?? '').split(/\r?\n/);
  const result = new Map();
  let inCriteria = false;
  let acIdx = 0;
  for (let i = 0; i < lines.length && acIdx < acs.length; i++) {
    const line = lines[i];
    if (/^##[ \t]+/.test(line)) {
      const title = line.replace(/^##[ \t]+/, '').trim().toLowerCase();
      inCriteria = title === 'acceptance criteria' || title === 'acceptance';
      continue;
    }
    if (!inCriteria) continue;
    if (/^\s*(?:[1-9][0-9]*[.)]|[-*+])[ \t]+\S/.test(line)) {
      result.set(acIdx, i + 1);
      acIdx += 1;
    }
  }
  return result;
}

export function collectStoryUnboundCriteriaFindings({ realRoot, storyPaths = [], scopedFiles = [], readFile, allowExplicitSubset = true } = {}) {
  if (!Array.isArray(storyPaths) || !storyPaths.length) return [];
  const read = typeof readFile === 'function' ? readFile : (p => readSafeUtf8(realRoot, p));
  const candidateJsons = scopedFiles.filter(isCandidateScenarioJson);
  if (!candidateJsons.length) return [];

  // Parse scenario JSONs lazily and index by stem + explicit story_path.
  const byStem = new Map();
  const parsedCache = new Map();
  const byExplicitStory = new Map();
  const getDoc = p => {
    if (parsedCache.has(p)) return parsedCache.get(p);
    const raw = read(p);
    let doc = null;
    if (typeof raw === 'string') {
      try {
        const parsed = JSON.parse(raw);
        if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) doc = parsed;
      } catch {}
    }
    parsedCache.set(p, doc);
    return doc;
  };

  for (const jp of candidateJsons) {
    const base = posix.basename(jp, '.json');
    const stems = new Set([base]);
    for (let at = base.lastIndexOf('.'); at > 0; at = base.lastIndexOf('.', at - 1)) stems.add(base.slice(0, at));
    for (const s of stems) {
      if (!byStem.has(s)) byStem.set(s, []);
      byStem.get(s).push(jp);
    }
  }

  const findings = [];
  for (const storyPath of storyPaths) {
    const slug = posix.basename(storyPath, '.md');
    const matchedCandidates = new Set(byStem.get(slug) ?? []);
    for (const jp of byExplicitStory.get(storyPath) ?? []) matchedCandidates.add(jp);
    if (!matchedCandidates.size) continue;

    const storyText = read(storyPath);
    if (typeof storyText !== 'string') continue;
    const acs = extractStoryCriteria(storyText);
    if (!acs.length) continue;

    const matchedFiles = [];
    const coveredIds = new Set();
    const coveredIdsLower = new Set();
    const declaredCriteriaTextToId = new Map();
    const declaredCriteriaIds = new Set();
    let hasSingleImplicitCheck = false;
    let hasBoundOrCheckedScenario = false;
    let allExplicitV1Subsets = true;

    for (const jp of [...matchedCandidates].sort()) {
      const doc = getDoc(jp);
      if (!doc) continue;
      if (Array.isArray(doc.cases) || /^pdd\.native-cases\./.test(String(doc.schema_version ?? ''))) continue;
      if (!Array.isArray(doc.steps)) continue;
      const explicitStory = typeof doc.story_path === 'string' ? doc.story_path.trim().replace(/^\.\//, '') : '';
      if (explicitStory && explicitStory !== storyPath) continue;

      matchedFiles.push(jp);
      const isExplicitV1Subset = doc.schema_version === V1_SCENARIO_SCHEMA && Array.isArray(doc.criteria) && doc.criteria.length > 0 && doc.criteria.length < acs.length;
      if (!isExplicitV1Subset) allExplicitV1Subsets = false;
      if (doc.schema_version === V1_SCENARIO_SCHEMA || Array.isArray(doc.criteria) || Array.isArray(doc.bound_criteria)) {
        hasBoundOrCheckedScenario = true;
      }
      for (const c of Array.isArray(doc.criteria) ? doc.criteria : []) {
        if (c && typeof c === 'object' && typeof c.id === 'string' && typeof c.text === 'string') {
          const cid = c.id.trim();
          if (cid) {
            declaredCriteriaTextToId.set(normalizeCriterionText(c.text), cid);
            declaredCriteriaIds.add(cid);
          }
        }
      }
      for (const ex of Array.isArray(doc.check_exemptions) ? doc.check_exemptions : []) {
        if (ex && typeof ex === 'object' && ex.criterion_id !== undefined && ex.criterion_id !== null) {
          const cid = String(ex.criterion_id).trim();
          if (cid) { coveredIds.add(cid); coveredIdsLower.add(cid.toLowerCase()); hasBoundOrCheckedScenario = true; }
        }
      }
      for (const step of doc.steps) {
        if (!step || typeof step !== 'object') continue;
        if (Array.isArray(step.checks)) {
          for (const ch of step.checks) {
            if (Array.isArray(ch) && ch.length > 0) {
              hasSingleImplicitCheck = true;
            } else if (ch && typeof ch === 'object') {
              if (ch.criterion_id !== undefined && ch.criterion_id !== null) {
                const cid = String(ch.criterion_id).trim();
                if (cid) { coveredIds.add(cid); coveredIdsLower.add(cid.toLowerCase()); hasBoundOrCheckedScenario = true; }
              } else {
                hasSingleImplicitCheck = true;
              }
            }
          }
        } else if (step.checks && typeof step.checks === 'object') {
          hasBoundOrCheckedScenario = true;
          for (const [k, v] of Object.entries(step.checks)) {
            const hasEntries = Array.isArray(v) ? v.length > 0 : Boolean(v);
            if (!hasEntries) continue;
            const cid = String(k).trim();
            if (cid) { coveredIds.add(cid); coveredIdsLower.add(cid.toLowerCase()); }
          }
        }
      }
    }

    if (!matchedFiles.length) continue;
    // Skip only when a single-AC shorthand scenario has implicit checks without explicit criterion_id.
    if (acs.length === 1 && hasSingleImplicitCheck && !hasBoundOrCheckedScenario) continue;
    // Honor valid v1 subset-criteria tests in `pdd lint --local` when every explicitly declared criterion is covered
    // (while `pdd prove` passes `allowExplicitSubset: false` to verify full Story coverage before merge).
    if (allowExplicitSubset && allExplicitV1Subsets && declaredCriteriaIds.size > 0
      && [...declaredCriteriaIds].every(cid => coveredIds.has(cid) || coveredIdsLower.has(cid.toLowerCase()))) {
      continue;
    }

    const acLines = findCriterionLines(storyText, acs);
    const missing = [];
    for (let idx = 0; idx < acs.length; idx++) {
      const acText = acs[idx];
      const num = String(idx + 1);
      const shaWithPath = criterionContentId(acText, storyPath);
      const shaBare = criterionContentId(acText, '');
      const acTagLower = `ac${num}`;
      const acDashLower = `ac-${num}`;
      const mappedId = declaredCriteriaTextToId.get(normalizeCriterionText(acText));

      const covered = coveredIds.has(num)
        || coveredIds.has(shaWithPath)
        || coveredIds.has(shaBare)
        || (mappedId ? coveredIds.has(mappedId) : false)
        || coveredIdsLower.has(acTagLower)
        || coveredIdsLower.has(acDashLower)
        || [...coveredIdsLower].some(id => id.startsWith(`${num}:`) || id.startsWith(`${acTagLower}:`) || id.startsWith(`${acDashLower}:`));

      if (!covered) {
        missing.push({ index: idx + 1, line: acLines.get(idx) ?? 1, text: acText });
      }
    }

    if (!missing.length) continue;
    const missingLabel = missing.map(m => `#${m.index}`).join(', ');
    const detail = formatTeachingDetail({
      invariant: `Story "${storyPath}" has ${missing.length} acceptance criteri${missing.length === 1 ? 'on' : 'a'} (${missingLabel}) with 0 checks in ${matchedFiles.join(', ')}`,
      fix: `Add runtime check(s) covering AC ${missingLabel} in ${matchedFiles[0]}`,
      rerun: 'pdd lint',
    });
    findings.push({
      filePath: storyPath,
      line: missing[0].line,
      order: 11,
      code: 'story-unbound-criteria',
      category: 'Story coverage',
      defaultSeverity: 'warn',
      detail,
    });
  }

  return findings;
}
