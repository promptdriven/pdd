#!/usr/bin/env node
// Mechanical G7 Architecture Boundary & Cycle Checker + Shrinking Semantic-Anchor Ratchet.
import { existsSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseJsModuleEdges, resolveImportSpecifier } from './lib/js-module-parser.mjs';

export { parseJsModuleEdges, resolveImportSpecifier };

const SCRIPT_DIR = dirname(fileURLToPath(import.meta.url));
export const DEFAULT_ROOT = resolve(SCRIPT_DIR, '..');
export const DEFAULT_RATCHET_PATH = join(SCRIPT_DIR, 'architecture-ratchet.json');
export const LAYERS = ['cli', 'setup', 'core', 'accounts', 'autopilot', 'shared', 'legacy-workflow', 'vendor'];
const RULE_ORDER = ['circular-import', 'layer-boundary', 'legacy-workflow-import', 'path-string-spawn', 'disallowed-npm-import', 'unmapped-layer'];

const ALLOWED_IMPORTS = {
  cli: new Set(['cli', 'setup', 'core', 'accounts', 'autopilot', 'shared']),
  autopilot: new Set(['autopilot', 'core', 'accounts', 'shared']),
  core: new Set(['core', 'shared']),
  setup: new Set(['setup', 'shared']),
  accounts: new Set(['accounts', 'shared']),
  shared: new Set(['shared']),
  'legacy-workflow': new Set(['legacy-workflow', 'shared', 'core', 'setup', 'accounts', 'autopilot', 'cli', 'vendor']),
  vendor: new Set(['vendor']),
};

const FLAT_LAYER_MAP = new Map([
  ['pdd-cli.mjs', 'cli'], ['command-catalog.mjs', 'cli'], ['argument-parser.mjs', 'cli'], ['completion.mjs', 'cli'], ['try-doors.mjs', 'cli'],
  ['skills-install.mjs', 'setup'], ['agent-mcp-setup.mjs', 'setup'], ['project-setup.mjs', 'setup'], ['project-files.mjs', 'setup'],
  ['setup-interaction.mjs', 'setup'], ['interpreter-version.mjs', 'setup'], ['cli-upgrade.mjs', 'setup'],
  ['toml-string.mjs', 'shared'], ['secret-redaction.mjs', 'shared'], ['process-lifecycle.mjs', 'shared'], ['runtime-exit.mjs', 'shared'],
  ['path-diagnostic.mjs', 'shared'], ['release-notice.mjs', 'shared'], ['github-calls.mjs', 'shared'], ['agent-config.mjs', 'shared'],
  ['validation-evidence.mjs', 'shared'], ['machine-resources.mjs', 'shared'],
  ['file-owner.mjs', 'core'], ['repo-hygiene-lint.mjs', 'core'], ['story-lint.mjs', 'core'], ['runtime-seam.mjs', 'core'],
  ['scenario-compile.mjs', 'core'], ['test-selection.mjs', 'core'], ['compiled-test.mjs', 'core'], ['svg-layout.mjs', 'core'],
  ['screen-compare.mjs', 'core'], ['screen-design-check.mjs', 'core'], ['update-sync.mjs', 'core'], ['product.mjs', 'core'],
  ['product-documents.mjs', 'core'], ['prompt-approve.mjs', 'core'], ['prompt-tests-words.mjs', 'core'], ['approval-policy.mjs', 'core'],
  ['approval-evidence.mjs', 'core'], ['human-boundary-card.mjs', 'core'],
  ['accounts-cli.mjs', 'accounts'], ['login-pool.mjs', 'accounts'], ['pdd-codex.mjs', 'accounts'], ['pdd-claude.mjs', 'accounts'], ['codex-limits.mjs', 'accounts'],
  ['autopilot.mjs', 'autopilot'], ['agent-adapters.mjs', 'autopilot'], ['agent-job.mjs', 'autopilot'],
  ['codex-lint.mjs', 'autopilot'], ['cost-ledger.mjs', 'autopilot'], ['machine-guard.mjs', 'autopilot'],
]);

export function classifyLayer(relPath) {
  const p = relPath.replace(/\\/g, '/').replace(/^\.\//, '');
  if (p === 'bin/pdd.mjs' || p.startsWith('src/cli/')) return 'cli';
  if (p === 'bin/pdd-codex.mjs' || p === 'bin/pdd-claude.mjs' || p.startsWith('src/accounts/')) return 'accounts';
  if (p.startsWith('src/setup/')) return 'setup';
  if (p.startsWith('src/core/')) return 'core';
  if (p.startsWith('src/autopilot/')) return 'autopilot';
  if (p.startsWith('src/shared/')) return 'shared';
  if (p.startsWith('src/legacy-workflow/')) return 'legacy-workflow';
  if (p.startsWith('src/vendor/')) return 'vendor';
  if (p.startsWith('src/') && !p.slice(4).includes('/')) {
    const base = p.slice(4);
    if (FLAT_LAYER_MAP.has(base)) return FLAT_LAYER_MAP.get(base);
    if (base.startsWith('workflow-')) return 'legacy-workflow';
    if (base.startsWith('autopilot-') || base.startsWith('issue-') || base.startsWith('metrics-') || base.startsWith('test-suite-')) return 'autopilot';
    if (base.startsWith('product') || base.startsWith('screen-')) return 'core';
  }
  return null;
}

function collectJsFiles(root) {
  const out = [];
  const walk = (absDir, relPrefix) => {
    if (!existsSync(absDir)) return;
    for (const name of readdirSync(absDir).sort()) {
      const abs = join(absDir, name);
      const rel = relPrefix ? `${relPrefix}/${name}` : name;
      const st = statSync(abs);
      if (st.isDirectory()) walk(abs, rel);
      else if (st.isFile() && /\.(?:mjs|js|cjs)$/.test(name)) out.push(rel);
    }
  };
  walk(join(root, 'src'), 'src');
  walk(join(root, 'bin'), 'bin');
  return out.sort();
}

function findTarjanSccs(nodes, adj) {
  let index = 0;
  const indices = new Map();
  const lowlink = new Map();
  const onStack = new Set();
  const stack = [];
  const sccs = [];

  const strongConnect = v => {
    indices.set(v, index);
    lowlink.set(v, index);
    index++;
    stack.push(v);
    onStack.add(v);
    for (const w of adj.get(v) ?? []) {
      if (!indices.has(w)) {
        strongConnect(w);
        lowlink.set(v, Math.min(lowlink.get(v), lowlink.get(w)));
      } else if (onStack.has(w)) {
        lowlink.set(v, Math.min(lowlink.get(v), indices.get(w)));
      }
    }
    if (lowlink.get(v) === indices.get(v)) {
      const comp = [];
      while (true) {
        const w = stack.pop();
        onStack.delete(w);
        comp.push(w);
        if (w === v) break;
      }
      if (comp.length >= 2) sccs.push(comp.sort());
      else if (comp.length === 1 && (adj.get(comp[0]) ?? []).includes(comp[0])) sccs.push(comp);
    }
  };

  for (const node of nodes) if (!indices.has(node)) strongConnect(node);
  return sccs.sort((a, b) => a[0].localeCompare(b[0]) || a.length - b.length);
}

function allowedNpmPackages(root) {
  const allowed = new Set(['smol-toml']);
  const pkgPath = join(root, 'package.json');
  if (existsSync(pkgPath)) {
    try {
      const pkg = JSON.parse(readFileSync(pkgPath, 'utf8'));
      for (const name of Object.keys(pkg.dependencies ?? {})) allowed.add(name);
    } catch {}
  }
  return allowed;
}

const countLines = text => (!text ? 0 : text.split(/\r?\n/).length - (text.endsWith('\n') ? 1 : 0));

export function analyzeArchitecture({ root = DEFAULT_ROOT } = {}) {
  const files = collectJsFiles(root);
  const fileSet = new Set(files);
  const npmAllowed = allowedNpmPackages(root);
  const layerStats = Object.fromEntries(LAYERS.map(l => [l, { files: 0, loc: 0 }]));
  const adj = new Map(files.map(f => [f, []]));
  const edgeLines = new Map();
  const findings = [];
  let totalLoc = 0;

  for (const rel of files) {
    const source = readFileSync(join(root, rel), 'utf8');
    const loc = countLines(source);
    totalLoc += loc;
    const fromLayer = classifyLayer(rel);
    if (!fromLayer) {
      findings.push({
        rule: 'unmapped-layer',
        path: rel,
        line: 1,
        semantic_anchor: `unmapped:${rel}`,
        invariant: `Every src/ and bin/ module must belong to a declared layer (${LAYERS.join(', ')}).`,
        fix: `Move "${rel}" into a domain folder (src/shared/, src/core/, src/cli/, src/setup/, src/accounts/, or src/autopilot/).`,
      });
      continue;
    }
    layerStats[fromLayer].files += 1;
    layerStats[fromLayer].loc += loc;

    const { imports, spawns } = parseJsModuleEdges(source, rel);
    for (const edge of imports) {
      const res = resolveImportSpecifier(rel, edge.specifier, fileSet);
      if (res.kind === 'builtin') continue;
      if (res.kind === 'npm') {
        if (!npmAllowed.has(res.packageName)) {
          findings.push({
            rule: 'disallowed-npm-import',
            path: rel,
            line: edge.line,
            semantic_anchor: `${fromLayer} -> npm:${res.packageName}`,
            invariant: `Layer "${fromLayer}" may only import Node stdlib or declared production npm dependencies (${[...npmAllowed].sort().join(', ')}).`,
            fix: `Replace "${edge.specifier}" with a Node stdlib API or add an approved dependency in package.json.`,
          });
        }
        continue;
      }
      if (res.kind !== 'repo') continue;

      const target = res.target;
      adj.get(rel).push(target);
      const edgeKey = `${rel}->${target}`;
      if (!edgeLines.has(edgeKey)) edgeLines.set(edgeKey, edge.line);
      const toLayer = classifyLayer(target);
      if (!toLayer) continue;

      const allowedTargets = ALLOWED_IMPORTS[fromLayer];
      if (!allowedTargets.has(toLayer)) {
        const isLegacy = toLayer === 'legacy-workflow';
        const allowedList = [...allowedTargets].sort().join(', ');
        findings.push({
          rule: isLegacy ? 'legacy-workflow-import' : 'layer-boundary',
          path: rel,
          line: edge.line,
          semantic_anchor: `${fromLayer} -> ${toLayer}:${target} (${edge.kind})`,
          invariant: isLegacy
            ? `Non-legacy layer "${fromLayer}" must not import frozen "legacy-workflow" module "${target}" (${edge.kind}).`
            : `Layer "${fromLayer}" may only import from [${allowedList}] (found ${edge.kind} -> "${target}" in layer "${toLayer}").`,
          fix: isLegacy
            ? `Extract the needed helper from "${target}" into src/shared/ instead of importing legacy workflow code.`
            : `Move the shared helper from "${target}" into src/shared/ or invert the dependency via injected ports.`,
        });
      }
    }

    for (const sp of spawns) {
      if (!fileSet.has(sp.target)) continue;
      findings.push({
        rule: 'path-string-spawn',
        path: rel,
        line: sp.line,
        semantic_anchor: `${sp.fn} -> ${sp.target}`,
        invariant: `Child process spawn (${sp.fn}) hardcodes repository module path "${sp.target}", bypassing static module boundaries.`,
        fix: `Import the owning module directly or route through a single declared CLI/shared entrypoint instead of spawning "${sp.target}".`,
      });
    }
  }

  for (const list of adj.values()) list.sort();
  const sccs = findTarjanSccs(files, adj);
  for (const members of sccs) {
    const memberSet = new Set(members);
    const anchorPath = members[0];
    let firstLine = 1;
    for (const target of adj.get(anchorPath) ?? []) {
      if (memberSet.has(target)) { firstLine = edgeLines.get(`${anchorPath}->${target}`) ?? 1; break; }
    }
    findings.push({
      rule: 'circular-import',
      path: anchorPath,
      line: firstLine,
      semantic_anchor: `scc:${members.join(' -> ')}`,
      invariant: `Circular import strongly connected component (${members.length} modules): ${members.join(' -> ')}.`,
      fix: `Extract the shared symbols out of the cycle into Layer-0 src/shared/ so imports flow strictly one way.`,
    });
  }

  findings.sort((a, b) => a.rule.localeCompare(b.rule) || a.path.localeCompare(b.path) || a.semantic_anchor.localeCompare(b.semantic_anchor) || a.line - b.line);
  return { root, files, totalLoc, layerStats, sccs, findings };
}

export function buildRatchetEntries(findings) {
  const counts = new Map();
  for (const f of findings) {
    const key = JSON.stringify([f.rule, f.path, f.semantic_anchor]);
    const entry = counts.get(key) ?? { rule: f.rule, path: f.path, semantic_anchor: f.semantic_anchor, count: 0 };
    entry.count += 1;
    counts.set(key, entry);
  }
  return [...counts.values()].sort(
    (a, b) => a.rule.localeCompare(b.rule) || a.path.localeCompare(b.path) || a.semantic_anchor.localeCompare(b.semantic_anchor),
  );
}

export function loadRatchet(ratchetPath = DEFAULT_RATCHET_PATH) {
  if (!existsSync(ratchetPath)) return { exists: false, entries: [], map: new Map(), total: 0 };
  const parsed = JSON.parse(readFileSync(ratchetPath, 'utf8'));
  const entries = Array.isArray(parsed.entries) ? parsed.entries : [];
  const map = new Map();
  let total = 0;
  for (const e of entries) {
    const key = JSON.stringify([e.rule, e.path, e.semantic_anchor]);
    map.set(key, (map.get(key) ?? 0) + Number(e.count || 0));
    total += Number(e.count || 0);
  }
  return { exists: true, entries, map, total };
}

export function checkArchitecture({ root = DEFAULT_ROOT, ratchetPath = DEFAULT_RATCHET_PATH } = {}) {
  const analysis = analyzeArchitecture({ root });
  const ratchet = loadRatchet(ratchetPath);
  const grouped = new Map();
  for (const f of analysis.findings) {
    const key = JSON.stringify([f.rule, f.path, f.semantic_anchor]);
    if (!grouped.has(key)) grouped.set(key, []);
    grouped.get(key).push(f);
  }

  const failures = [];
  for (const [key, items] of grouped.entries()) {
    const allowed = ratchet.map.get(key) ?? 0;
    if (items.length > allowed) {
      for (const item of items.slice(allowed)) failures.push({ ...item, currentCount: items.length, allowedCount: allowed });
    }
  }

  let shrunkCount = 0;
  const resolved = [];
  for (const [key, allowed] of ratchet.map.entries()) {
    const cur = (grouped.get(key) ?? []).length;
    if (cur < allowed) {
      shrunkCount += allowed - cur;
      const [rule, path, semantic_anchor] = JSON.parse(key);
      resolved.push({ rule, path, semantic_anchor, delta: allowed - cur });
    }
  }

  return {
    ok: failures.length === 0,
    analysis,
    ratchetTotal: ratchet.total,
    ratchetExists: ratchet.exists,
    currentTotal: analysis.findings.length,
    failures,
    shrunkCount,
    resolved,
  };
}

export function formatFailureDiagnostic(failure, rerunCmd = 'node scripts/check-architecture.mjs') {
  return [
    `ERROR [${failure.rule}] ${failure.path}:${failure.line}`,
    `  Invariant: ${failure.invariant}`,
    `  Fix: ${failure.fix}`,
    `  Rerun: ${rerunCmd}`,
  ].join('\n');
}

export function formatReport(result) {
  const { analysis, ratchetTotal, currentTotal, shrunkCount, failures } = result;
  const lines = [
    `G7 Architecture Report (${analysis.files.length} files, ${analysis.totalLoc} LOC)`,
    '',
    'Layer Breakdown:',
    '  Layer             Files     LOC',
    '  -------------------------------',
  ];
  for (const layer of LAYERS) {
    const st = analysis.layerStats[layer];
    lines.push(`  ${layer.padEnd(17)} ${String(st.files).padStart(5)} ${String(st.loc).padStart(7)}`);
  }
  const byRule = Object.fromEntries(RULE_ORDER.map(r => [r, analysis.findings.filter(f => f.rule === r).length]));
  lines.push(
    '',
    `Cycles (Tarjan SCCs):        ${analysis.sccs.length}`,
    `Legacy-workflow imports:     ${byRule['legacy-workflow-import']}`,
    `Layer-boundary violations:   ${byRule['layer-boundary']}`,
    `Path-string child spawns:    ${byRule['path-string-spawn']}`,
    `Disallowed npm / unmapped:   ${byRule['disallowed-npm-import'] + byRule['unmapped-layer']}`,
    `Ratchet baseline -> current: ${ratchetTotal} -> ${currentTotal} (shrunk by ${shrunkCount}, new/excess: ${failures.length})`,
  );
  if (analysis.sccs.length > 0) {
    lines.push('', 'Circular SCCs:');
    analysis.sccs.forEach((scc, idx) => lines.push(`  #${idx + 1} (${scc.length} files): ${scc.join(' -> ')}`));
  }
  return lines.join('\n');
}

function main(argv) {
  let root = DEFAULT_ROOT, ratchetPath = DEFAULT_RATCHET_PATH, writeMode = false, reportMode = false, jsonMode = false;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--write-ratchet') writeMode = true;
    else if (a === '--report') reportMode = true;
    else if (a === '--json') jsonMode = true;
    else if (a === '--root' && argv[i + 1]) root = resolve(argv[++i]);
    else if (a === '--ratchet' && argv[i + 1]) ratchetPath = resolve(argv[++i]);
    else {
      process.stderr.write(`Unknown argument: ${a}\nUsage: node scripts/check-architecture.mjs [--report] [--write-ratchet] [--json] [--root DIR] [--ratchet FILE]\n`);
      return 2;
    }
  }

  if (writeMode) {
    const prev = loadRatchet(ratchetPath);
    const entries = buildRatchetEntries(analyzeArchitecture({ root }).findings);
    mkdirSync(dirname(ratchetPath), { recursive: true });
    writeFileSync(ratchetPath, `${JSON.stringify({ schema_version: 'pdd.architecture-ratchet.v1', rules: RULE_ORDER, entries }, null, 2)}\n`, 'utf8');
    const curTotal = entries.reduce((sum, e) => sum + e.count, 0);
    if (jsonMode) process.stdout.write(`${JSON.stringify({ ok: true, previousTotal: prev.total, currentTotal: curTotal, entries: entries.length }, null, 2)}\n`);
    else process.stdout.write(`Wrote ${ratchetPath}: ${curTotal} debt entries across ${entries.length} unique semantic anchors${prev.exists ? ` (was ${prev.total}, delta ${curTotal - prev.total})` : ' (initial baseline)'}.\n`);
    return 0;
  }

  const result = checkArchitecture({ root, ratchetPath });
  if (reportMode) {
    if (jsonMode) {
      process.stdout.write(`${JSON.stringify({
        ok: result.ok, files: result.analysis.files.length, totalLoc: result.analysis.totalLoc,
        layerStats: result.analysis.layerStats, cycleCount: result.analysis.sccs.length, cycles: result.analysis.sccs,
        ratchetTotal: result.ratchetTotal, currentTotal: result.currentTotal, shrunkCount: result.shrunkCount, newFailureCount: result.failures.length,
      }, null, 2)}\n`);
    } else process.stdout.write(`${formatReport(result)}\n`);
    return result.ok ? 0 : 1;
  }
  if (jsonMode) {
    process.stdout.write(`${JSON.stringify({ ok: result.ok, ratchetTotal: result.ratchetTotal, currentTotal: result.currentTotal, shrunkCount: result.shrunkCount, failures: result.failures }, null, 2)}\n`);
    return result.ok ? 0 : 1;
  }
  if (!result.ok) {
    for (const f of result.failures) process.stderr.write(`${formatFailureDiagnostic(f)}\n\n`);
    process.stderr.write(`Architecture check FAILED: ${result.failures.length} new/exceeding violation(s) beyond ratchet (${result.ratchetTotal} baseline -> ${result.currentTotal} current).\n`);
    return 1;
  }
  process.stdout.write(`Architecture check PASSED: 0 new violations (${result.currentTotal}/${result.ratchetTotal} ratcheted debt, ${result.analysis.sccs.length} SCCs).\n`);
  if (result.shrunkCount > 0) process.stdout.write(`Ratchet can shrink by ${result.shrunkCount} resolved item(s); run \`node scripts/check-architecture.mjs --write-ratchet\` to lock in the reduction.\n`);
  return 0;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  process.exitCode = main(process.argv.slice(2));
}
