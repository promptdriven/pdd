// Shrinking Semantic-Anchor Multiset Ratchet + 4-part Lauren Tan diagnostics & report formatting.
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';

export const RATCHET_SCHEMA_VERSION = 'pdd.architecture-ratchet.v1';

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

export function loadRatchet(ratchetPath) {
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

export function evaluateRatchet(analysis, ratchetPath) {
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

export function writeRatchetFile(analysis, ratchetPath, { rules, allowGrowth = false } = {}) {
  const prev = loadRatchet(ratchetPath);
  const entries = buildRatchetEntries(analysis.findings);
  if (prev.exists && !allowGrowth) {
    const growth = [];
    for (const e of entries) {
      const key = JSON.stringify([e.rule, e.path, e.semantic_anchor]);
      const allowed = prev.map.get(key) ?? 0;
      if (e.count > allowed) growth.push({ ...e, allowed });
    }
    if (growth.length > 0) {
      return { ok: false, refused: 'ratchet-growth', previousTotal: prev.total, growth };
    }
  }
  mkdirSync(dirname(ratchetPath), { recursive: true });
  writeFileSync(ratchetPath, `${JSON.stringify({ schema_version: RATCHET_SCHEMA_VERSION, rules, entries }, null, 2)}\n`, 'utf8');
  const currentTotal = entries.reduce((sum, e) => sum + e.count, 0);
  return { ok: true, existed: prev.exists, previousTotal: prev.total, currentTotal, entryCount: entries.length };
}

export function formatFailureDiagnostic(failure, rerunCmd = 'node scripts/check-architecture.mjs') {
  return [
    `ERROR [${failure.rule}] ${failure.path}:${failure.line}`,
    `  Invariant: ${failure.invariant}`,
    `  Fix: ${failure.fix}`,
    `  Rerun: ${rerunCmd}`,
  ].join('\n');
}

export function formatReport(result, { layers, rules }) {
  const { analysis, ratchetTotal, currentTotal, shrunkCount, failures } = result;
  const lines = [
    `G7 Architecture Report (${analysis.files.length} files, ${analysis.totalLoc} LOC)`,
    '',
    'Layer Breakdown:',
    '  Layer             Files     LOC',
    '  -------------------------------',
  ];
  for (const layer of layers) {
    const st = analysis.layerStats[layer];
    lines.push(`  ${layer.padEnd(17)} ${String(st.files).padStart(5)} ${String(st.loc).padStart(7)}`);
  }
  const byRule = Object.fromEntries(rules.map(r => [r, analysis.findings.filter(f => f.rule === r).length]));
  lines.push(
    '',
    `Cycles (Tarjan SCCs):        ${analysis.sccs.length} (${byRule['circular-import']} intra-SCC edges)`,
    `Legacy-workflow imports:     ${byRule['legacy-workflow-import']}`,
    `Layer-boundary violations:   ${byRule['layer-boundary']}`,
    `Path-string child spawns:    ${byRule['path-string-spawn']}`,
    `Unresolved local imports:    ${byRule['unresolved-local-import']}`,
    `Disallowed npm / unmapped:   ${byRule['disallowed-npm-import'] + byRule['unmapped-layer']}`,
    `Ratchet baseline -> current: ${ratchetTotal} -> ${currentTotal} (shrunk by ${shrunkCount}, new/excess: ${failures.length})`,
  );
  if (analysis.sccs.length > 0) {
    lines.push('', 'Circular SCCs:');
    analysis.sccs.forEach((scc, idx) => lines.push(`  #${idx + 1} (${scc.length} files): ${scc.join(' -> ')}`));
  }
  return lines.join('\n');
}
