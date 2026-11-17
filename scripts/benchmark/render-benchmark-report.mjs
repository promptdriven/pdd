#!/usr/bin/env node
// Part C: Self-Contained Ishaan-Style HTML + Inline SVG Trend Dashboard Generator.
// Strictly zero external assets and zero commit hashes or UUIDs in output.

import * as nativeFs from 'node:fs';
import { resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  assertCleanPublicText,
  computeNorthStarScorecard,
  roundNum,
  sanitizePublicText,
} from './scorecard.mjs';

function esc(value) {
  return sanitizePublicText(String(value ?? ''))
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;')
    .replaceAll("'", '&#39;');
}

export function fmtSec(seconds) {
  if (seconds === null || seconds === undefined || !Number.isFinite(Number(seconds))) return '—';
  const s = Math.max(0, Number(seconds));
  const m = Math.floor(s / 60);
  let rem = Math.round(s - m * 60);
  if (rem === 60) return `${m + 1}m 00s`;
  return m > 0 ? `${m}m ${String(rem).padStart(2, '0')}s` : `${rem}s`;
}

function fmtCompactTokens(n) {
  if (n === null || n === undefined || !Number.isFinite(Number(n))) return '—';
  const v = Number(n);
  if (v >= 1_000_000) return `${(v / 1_000_000).toFixed(2)}M`;
  if (v >= 1_000) return `${(v / 1_000).toFixed(1)}k`;
  return String(Math.round(v));
}

function fmtUsd(n) {
  if (n === null || n === undefined || !Number.isFinite(Number(n))) return '—';
  return `$${Number(n).toFixed(2)}`;
}

export function renderSvgDualBarChart({
  title,
  subtitle,
  labels = [],
  seriesA = [],
  seriesB = null,
  baselineRef = null,
  baselineLabel = '',
  maxY = null,
  fmtValue = v => String(Math.round(v)),
  failZeroB = false,
  colorA = '#2563eb',
  colorB = '#ea580c',
}) {
  const w = 540;
  const h = 255;
  const padL = 54;
  const padR = 24;
  const padT = 46;
  const padB = 42;
  const pw = w - padL - padR;
  const ph = h - padT - padB;
  const n = Math.max(1, labels.length);
  const step = pw / n;

  const allVals = [
    ...seriesA.filter(v => Number.isFinite(v)),
    ...(seriesB ? seriesB.filter(v => Number.isFinite(v)) : []),
    ...(Number.isFinite(baselineRef) ? [baselineRef] : []),
  ];
  const computedMax = maxY || Math.max(10, ...(allVals.length ? allVals : [10])) * 1.18;

  const out = [
    `<svg viewBox="0 0 ${w} ${h}" style="width:100%;height:auto;background:#ffffff;border:1px solid #e2e8f0;border-radius:10px;">`,
    `<text x="16" y="22" font-family="system-ui,-apple-system,sans-serif" font-size="13.5" font-weight="700" fill="#0f172a">${esc(title)}</text>`,
    `<text x="16" y="37" font-family="system-ui,-apple-system,sans-serif" font-size="11" fill="#64748b">${esc(subtitle)}</text>`,
  ];

  for (let g = 0; g <= 4; g++) {
    const yv = (computedMax * g) / 4;
    const yp = padT + ph - (ph * g) / 4;
    out.push(`<line x1="${padL}" y1="${yp.toFixed(1)}" x2="${w - padR}" y2="${yp.toFixed(1)}" stroke="#f1f5f9" stroke-width="1"/>`);
    out.push(`<text x="${padL - 6}" y="${(yp + 4).toFixed(1)}" text-anchor="end" font-family="system-ui,sans-serif" font-size="10" fill="#64748b">${esc(fmtValue(yv))}</text>`);
  }

  if (Number.isFinite(baselineRef) && baselineRef > 0 && baselineRef <= computedMax) {
    const by = padT + ph - (ph * baselineRef) / computedMax;
    out.push(`<line x1="${padL}" y1="${by.toFixed(1)}" x2="${w - padR}" y2="${by.toFixed(1)}" stroke="#16a34a" stroke-width="1.5" stroke-dasharray="5,4"/>`);
    if (baselineLabel) {
      out.push(`<text x="${w - padR - 2}" y="${Math.max(padT + 10, by - 4).toFixed(1)}" text-anchor="end" font-family="system-ui,sans-serif" font-size="9.5" font-weight="600" fill="#15803d">${esc(baselineLabel)}</text>`);
    }
  }

  const safeColorA = esc(colorA);
  const safeColorB = esc(colorB);
  const barW = Math.min(24, step * 0.32);
  labels.forEach((lbl, i) => {
    const cx = padL + step * (i + 0.5);
    const va = seriesA[i];
    const vb = seriesB ? seriesB[i] : null;
    if (i === labels.length - 1 && labels.length > 1) {
      out.push(`<rect x="${(cx - step * 0.45).toFixed(1)}" y="${padT}" width="${(step * 0.9).toFixed(1)}" height="${ph}" fill="#eff6ff" opacity="0.65"/>`);
    }
    if (Number.isFinite(va) && va >= 0) {
      const ha = Math.max(2, (ph * Math.min(va, computedMax)) / computedMax);
      const ya = padT + ph - ha;
      const bx = cx - (seriesB ? barW + 2 : barW / 2);
      out.push(`<rect x="${bx.toFixed(1)}" y="${ya.toFixed(1)}" width="${barW.toFixed(1)}" height="${ha.toFixed(1)}" rx="3" fill="${safeColorA}"/>`);
      out.push(`<text x="${(bx + barW / 2).toFixed(1)}" y="${(ya - 5).toFixed(1)}" text-anchor="middle" font-family="system-ui,sans-serif" font-size="9.5" font-weight="600" fill="${safeColorA}">${esc(fmtValue(va))}</text>`);
    }
    if (seriesB) {
      const bx2 = cx + 2;
      if (Number.isFinite(vb) && vb > 0) {
        const hb = Math.max(2, (ph * Math.min(vb, computedMax)) / computedMax);
        const yb = padT + ph - hb;
        out.push(`<rect x="${bx2.toFixed(1)}" y="${yb.toFixed(1)}" width="${barW.toFixed(1)}" height="${hb.toFixed(1)}" rx="3" fill="${safeColorB}"/>`);
        out.push(`<text x="${(bx2 + barW / 2).toFixed(1)}" y="${(yb - 5).toFixed(1)}" text-anchor="middle" font-family="system-ui,sans-serif" font-size="9.5" font-weight="600" fill="${safeColorB}">${esc(fmtValue(vb))}</text>`);
      } else if (failZeroB) {
        out.push(`<text x="${(bx2 + barW / 2).toFixed(1)}" y="${(padT + ph - 6).toFixed(1)}" text-anchor="middle" font-family="system-ui,sans-serif" font-size="9" font-weight="700" fill="#dc2626">FAIL</text>`);
      }
    }
    out.push(`<text x="${cx.toFixed(1)}" y="${h - 14}" text-anchor="middle" font-family="system-ui,sans-serif" font-size="10" font-weight="600" fill="#334155">${esc(lbl)}</text>`);
  });

  out.push('</svg>');
  return out.join('\n');
}

function renderProgressMeter(currentPct, targetPct, label) {
  const clamped = Math.max(0, Math.min(100, Number(currentPct) || 0));
  const targetClamped = Math.max(0, Math.min(100, Number(targetPct) || 90));
  const color = clamped >= targetClamped ? '#16a34a' : (clamped >= 50 ? '#2563eb' : '#ea580c');
  return `
    <div style="margin-top:8px;">
      <div style="display:flex;justify-content:space-between;font-size:11.5px;color:#475569;margin-bottom:3px;">
        <span>${esc(label)}</span>
        <span><strong>${Number.isFinite(currentPct) ? `${currentPct}%` : 'Pending'}</strong> / ${targetClamped}% target</span>
      </div>
      <div style="position:relative;height:10px;background:#e2e8f0;border-radius:999px;overflow:hidden;">
        <div style="width:${clamped}%;height:100%;background:${color};border-radius:999px;"></div>
        <div style="position:absolute;left:${targetClamped}%;top:0;bottom:0;width:2px;background:#0f172a;" title="Target ${targetClamped}%"></div>
      </div>
    </div>`;
}

function parseJsonl(text = '') {
  return String(text ?? '')
    .split('\n')
    .map(l => l.trim())
    .filter(Boolean)
    .map(l => JSON.parse(l));
}

export function renderBenchmarkReport({
  releaseReport = null,
  observeRuns = [],
  title = 'PDD Release Benchmark & Autopilot Daily Observe Scorecard',
  subtitle = null,
} = {}) {
  const candidate = releaseReport?.candidate || null;
  const baseline = releaseReport?.baseline || null;
  const history = Array.isArray(releaseReport?.history) && releaseReport.history.length
    ? releaseReport.history
    : [baseline, candidate].filter(Boolean);
  const comparison = releaseReport?.comparison || { advisory_warning_count: 0, warnings: [] };
  const northStar = computeNorthStarScorecard({
    releaseRun: candidate,
    observeRuns,
  });

  const bar1 = northStar.pdd_vs_direct_coding;
  const bar2 = northStar.autopilot_zero_edit;

  const generatedDate = (candidate?.date || observeRuns[observeRuns.length - 1]?.date || new Date().toISOString().slice(0, 10));
  const subLine = subtitle || `Prepared ${generatedDate} · Tracks locked next-month investor North-Star targets, release authoring/runtime trends, and live read-only Autopilot observe telemetry.`;

  // Build Part A SVG charts from history
  const chartsHtml = [];
  if (history.length > 0) {
    const versionLabels = history.map(h => h.label || `${h.date ? `${h.date} ` : ''}(${h.version || '?'})`);
    for (const [wid, wTitle, baseSec, baseTxt] of [
      ['snake', 'Snake: Authoring vs Runtime Test Time', 196, 'Direct baseline: 3m 16s'],
      ['2048', '2048: Authoring vs Runtime Test Time', 440, 'Direct baseline: 7m 20s'],
      ['task-manager', 'Task Manager: Authoring vs Runtime Test Time', 568, 'Direct baseline: 9m 28s'],
    ]) {
      const authSeries = history.map(h => {
        const found = (h.workloads || []).find(w => w.workload === wid);
        return found?.total_authoring_seconds ?? null;
      });
      const testSeries = history.map(h => {
        const found = (h.workloads || []).find(w => w.workload === wid);
        if (!found) return null;
        return found.pdd_test_status?.status === 'pass'
          ? (found.pdd_test_status?.duration_seconds ?? 0)
          : 0;
      });
      if (authSeries.some(v => v !== null)) {
        chartsHtml.push(renderSvgDualBarChart({
          title: wTitle,
          subtitle: `Blue = PDD Authoring · Orange = Hosted pdd test · Green dashed = ${baseTxt}`,
          labels: versionLabels,
          seriesA: authSeries,
          seriesB: testSeries,
          baselineRef: baseSec,
          baselineLabel: baseTxt,
          fmtValue: fmtSec,
          failZeroB: true,
        }));
      }
    }

    // Token & Cost trend chart (average across small builds per version)
    const avgTokMillions = history.map(h => {
      const small = (h.workloads || []).filter(w => (w.tier || 'small') === 'small' && Number.isFinite(w.input_tokens));
      if (!small.length) return null;
      const avg = small.reduce((s, w) => s + w.input_tokens + (w.output_tokens || 0), 0) / small.length;
      return roundNum(avg / 1_000_000, 2);
    });
    const skillKbSeries = history.map(h => (h.skills?.total_bytes ? roundNum(h.skills.total_bytes / 1024, 1) : null));

    if (avgTokMillions.some(v => v !== null)) {
      chartsHtml.push(renderSvgDualBarChart({
        title: 'Authoring Token Volume Trend (Avg Small Build)',
        subtitle: 'Blue = Mean Authoring Tokens per App (Millions)',
        labels: versionLabels,
        seriesA: avgTokMillions,
        seriesB: null,
        fmtValue: v => `${Number(v).toFixed(2)}M`,
        colorA: '#1d4ed8',
      }));
    }
    if (skillKbSeries.some(v => v !== null)) {
      chartsHtml.push(renderSvgDualBarChart({
        title: 'Bundled Skill Footprint Trend (All PDD Skills)',
        subtitle: 'Purple = Total Bundled Skill Markdown Size (KB)',
        labels: versionLabels,
        seriesA: skillKbSeries,
        seriesB: null,
        fmtValue: v => `${Math.round(v)} KB`,
        colorA: '#7c3aed',
      }));
    }
  }

  // Build Part B Autopilot Observe SVG charts
  const latestByRepo = new Map();
  for (const r of observeRuns) {
    if (r?.repo) latestByRepo.set(r.repo, r);
  }
  const latestObserve = [...latestByRepo.values()];

  if (latestObserve.length > 0) {
    const repoShortLabels = latestObserve.map(r => r.repo.split('/')[1] || r.repo);
    chartsHtml.push(renderSvgDualBarChart({
      title: 'Autopilot Live Observe Funnel by Repository',
      subtitle: 'Blue = Open Issues · Green = Eligible Issues Ready for Dispatch (0 Mutations)',
      labels: repoShortLabels,
      seriesA: latestObserve.map(r => r.repo_open_issues),
      seriesB: latestObserve.map(r => r.eligible_issues),
      fmtValue: v => String(Math.round(v)),
      colorA: '#2563eb',
      colorB: '#16a34a',
    }));

    const qualityRepos = bar2.repos.filter(r => (r.evaluated_runs ?? 0) > 0);
    if (qualityRepos.length > 0) {
      chartsHtml.push(renderSvgDualBarChart({
        title: 'Autopilot End-to-End Zero-Edit Completion vs 90% Bar',
        subtitle: 'Blue = Strict Merged Zero-Edit % · Teal = Incl. Observe Would-Merge % · Green = 90% Target',
        labels: qualityRepos.map(r => r.repo.split('/')[1] || r.repo),
        seriesA: qualityRepos.map(r => r.zero_edit_completion_pct ?? 0),
        seriesB: qualityRepos.map(r => r.observe_included_completion_pct ?? 0),
        baselineRef: 90,
        baselineLabel: '90% Target Bar',
        maxY: 105,
        fmtValue: v => `${Math.round(v)}%`,
        colorA: '#0284c7',
        colorB: '#0d9488',
      }));
    }
  }

  // Build Release Candidate Table rows
  const candidateRowsHtml = (candidate?.workloads || []).map(w => {
    const nsRow = [...bar1.small_builds.workloads, ...bar1.large_codebases.workloads].find(x => x.workload === w.workload);
    const lintBadge = w.pdd_lint_status?.status === 'pass'
      ? '<span class="pill ok">PASS</span>'
      : (w.pdd_lint_status?.status === 'fail' ? '<span class="pill bad">FAIL</span>' : '<span class="pill warn">NOT RUN</span>');
    const testBadge = w.pdd_test_status?.status === 'pass'
      ? '<span class="pill ok">PASS</span>'
      : (w.pdd_test_status?.status === 'fail' ? '<span class="pill bad">FAIL</span>' : '<span class="pill warn">NOT RUN</span>');
    const refusals = (w.pdd_test_status?.refusal_codes || []).length
      ? `<br><span class="muted">Refused: ${esc(w.pdd_test_status.refusal_codes.join(', '))}</span>`
      : '';
    return `
      <tr>
        <td><strong>${esc(w.label || w.workload)}</strong><br><span class="muted">Tier: ${esc(w.tier || 'small')}</span></td>
        <td><strong>${fmtSec(w.total_authoring_seconds)}</strong><br><span class="muted">Direct: ${fmtSec(w.direct_baseline_seconds)}</span></td>
        <td>${fmtSec(w.prompt_only_seconds)}</td>
        <td>${fmtSec(w.post_prompt_pre_test_seconds)}</td>
        <td>${fmtCompactTokens(w.input_tokens)} in / ${fmtCompactTokens(w.output_tokens)} out<br><span class="muted">Auth: ${fmtUsd(w.authoring_usd)} · Total: ${fmtUsd(nsRow?.total_usd)}</span></td>
        <td>${Number.isFinite(Number(w.skill_files_read)) && w.skill_files_read !== null ? Number(w.skill_files_read) : '—'} files<br><span class="muted">${Number.isFinite(Number(w.skill_total_bytes)) && Number(w.skill_total_bytes) > 0 ? `${(Number(w.skill_total_bytes) / 1024).toFixed(1)} KB` : '—'}</span></td>
        <td>${lintBadge} <span class="muted">(${fmtSec(w.pdd_lint_status?.duration_seconds)})</span></td>
        <td>${testBadge} <span class="muted">(${fmtSec(w.pdd_test_status?.duration_seconds)})</span>${refusals}</td>
        <td>Speed: <strong>${nsRow?.speed_ratio_vs_direct !== null && nsRow?.speed_ratio_vs_direct !== undefined ? `${esc(nsRow.speed_ratio_vs_direct)}x` : '—'}</strong><br>Cost: <strong>${nsRow?.cost_ratio_vs_direct !== null && nsRow?.cost_ratio_vs_direct !== undefined ? `${esc(nsRow.cost_ratio_vs_direct)}x` : '—'}</strong></td>
      </tr>`;
  }).join('');

  // Advisory regression warnings list
  const warningsHtml = comparison.warnings?.length
    ? `<ul>${comparison.warnings.map(w => `<li><strong>[${esc(w.kind)}]</strong> ${esc(w.message)}</li>`).join('')}</ul>`
    : '<p><span class="pill ok">CLEAN</span> Zero release regressions flagged against baseline threshold.</p>';

  // Observe table rows
  const safeRepoSlugRe = /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/;
  const observeRowsHtml = latestObserve.map(r => {
    const repoNs = bar2.repos.find(x => x.repo === r.repo) || null;
    const sk = r.skipped_by_reason || {};
    const skipParts = Object.entries(sk)
      .filter(([, count]) => Number(count) > 0)
      .map(([k, count]) => `${k.replaceAll('_', ' ')}: ${Number(count)}`)
      .join(' · ') || 'none';
    const slotsTxt = (r.dispatch_plan?.selected || [])
      .map(s => `S${esc(s.slot)}: #${esc(s.issue)} (${(Array.isArray(s.areas) ? s.areas : []).map(esc).join(', ')})`)
      .join('<br>') || '<span class="muted">No eligible issues</span>';
    const q = r.quality || {};
    const evalRuns = repoNs?.evaluated_runs ?? Number(q.evaluated_runs ?? 0);
    const mergedPct = repoNs?.zero_edit_completion_pct ?? q.zero_edit_completion_pct;
    const obsPct = repoNs?.observe_included_completion_pct ?? q.observe_included_completion_pct;
    const mergedClean = repoNs?.zero_edit_merged_runs ?? Number(q.zero_edit_merged_runs ?? 0);
    const wouldMergeClean = repoNs?.observe_would_merge_runs ?? Number(q.observe_would_merge_runs ?? 0);
    const zeTxt = evalRuns > 0 && mergedPct !== null && mergedPct !== undefined
      ? `${mergedPct}% merged (${mergedClean}/${evalRuns})`
      : 'No prior runs';
    const obsSub = evalRuns > 0 && wouldMergeClean > 0
      ? ` · ${obsPct}% incl. ${wouldMergeClean} observe would-merge`
      : '';
    const repoSlug = String(r.repo || '');
    const repoCell = safeRepoSlugRe.test(repoSlug)
      ? `<a href="https://github.com/${esc(repoSlug)}">${esc(repoSlug)}</a>`
      : esc(repoSlug);
    return `
      <tr>
        <td><strong>${repoCell}</strong><br><span class="muted">${esc(r.date)} · ${Number(r.mutations) || 0} writes</span></td>
        <td><strong>${Number(r.repo_open_issues) || 0}</strong></td>
        <td><strong>${Number(r.eligible_issues) || 0}</strong> <span class="pill ${(Number(r.eligible_issues) || 0) > 0 ? 'ok' : 'warn'}">${Number(r.taken_pct) || 0}%</span></td>
        <td>${esc(skipParts)}</td>
        <td>${slotsTxt}</td>
        <td><strong>${esc(zeTxt)}</strong>${esc(obsSub)}<br><span class="muted">Grade A:${Number(q.grade_a ?? 0)} · B:${Number(q.grade_b ?? 0)} · C:${Number(q.grade_c ?? 0)} · 7d reopen:${Number(q.reopened_7d ?? 0)}</span></td>
        <td>${Number(r.api_calls ?? 0)} calls · ${roundNum((Number(r.etag_hit_rate) || 0) * 100, 1)}% ETag<br><span class="muted">${Number(r.latency_ms ?? 0)} ms</span></td>
      </tr>`;
  }).join('');

  const smallBadge = bar1.small_builds.meets_target
    ? '<span class="pill ok">ON TARGET</span>'
    : '<span class="pill warn">GAP TO 1.0x BAR</span>';
  const largeBadge = bar1.large_codebases.meets_target
    ? '<span class="pill ok">ON TARGET</span>'
    : '<span class="pill warn">IN PROGRESS</span>';
  const apBadge = bar2.meets_target
    ? '<span class="pill ok">ON TARGET (90-95%)</span>'
    : '<span class="pill warn">GAP TO 90-95% BAR</span>';

  const html = `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>${esc(title)}</title>
<style>
  :root {
    --bg: #f8fafc;
    --card: #ffffff;
    --ink: #0f172a;
    --muted: #475569;
    --line: #e2e8f0;
    --blue: #2563eb;
    --orange: #ea580c;
    --red: #dc2626;
    --green: #16a34a;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
    background: var(--bg);
    color: var(--ink);
    line-height: 1.5;
  }
  .wrap { max-width: 1240px; margin: 0 auto; padding: 28px 20px 64px; }
  h1 { font-size: 26px; margin: 0 0 6px; }
  h2 { font-size: 19px; margin: 28px 0 12px; border-bottom: 2px solid var(--line); padding-bottom: 6px; }
  h3 { font-size: 15px; margin: 0 0 8px; }
  p, li { font-size: 13.5px; color: #1e293b; }
  .sub { color: var(--muted); font-size: 14px; margin-bottom: 20px; }
  .grid2 { display: grid; grid-template-columns: repeat(auto-fit, minmax(500px, 1fr)); gap: 16px; }
  .grid3 { display: grid; grid-template-columns: repeat(auto-fit, minmax(350px, 1fr)); gap: 14px; }
  .card {
    background: var(--card);
    border: 1px solid var(--line);
    border-radius: 12px;
    padding: 16px 18px;
    box-shadow: 0 1px 2px rgba(15,23,42,0.04);
  }
  .card.bar-blue { border-left: 5px solid var(--blue); }
  .card.bar-green { border-left: 5px solid var(--green); }
  .card.bar-orange { border-left: 5px solid var(--orange); }
  .card.bar-red { border-left: 5px solid var(--red); }
  .kpi-row { display: flex; gap: 14px; flex-wrap: wrap; margin: 10px 0; }
  .kpi { background: #f8fafc; border: 1px solid var(--line); border-radius: 8px; padding: 8px 12px; flex: 1; min-width: 110px; }
  .kpi .val { font-size: 18px; font-weight: 800; color: var(--ink); }
  .kpi .lbl { font-size: 11px; color: var(--muted); }
  table { width: 100%; border-collapse: collapse; font-size: 12.8px; background: #fff; border: 1px solid var(--line); border-radius: 10px; overflow: hidden; margin-bottom: 14px; }
  th, td { padding: 9px 10px; border-bottom: 1px solid var(--line); text-align: left; vertical-align: top; }
  th { background: #f1f5f9; font-weight: 700; color: #0f172a; font-size: 12px; }
  .muted { color: var(--muted); font-size: 11.5px; }
  .pill { display: inline-block; padding: 2px 8px; border-radius: 999px; font-size: 11px; font-weight: 700; }
  .pill.ok { background: #dcfce7; color: #166534; }
  .pill.bad { background: #fee2e2; color: #991b1b; }
  .pill.warn { background: #fef3c7; color: #92400e; }
  code { background: #f1f5f9; padding: 1px 5px; border-radius: 4px; font-size: 12px; }
  a { color: var(--blue); text-decoration: none; }
  a:hover { text-decoration: underline; }
</style>
</head>
<body>
<div class="wrap">
  <h1>${esc(title)}</h1>
  <div class="sub">${esc(subLine)}</div>

  <h2>Locked Next-Month North-Star Investor Scorecard</h2>
  <div class="grid3">
    <div class="card bar-blue">
      <h3>Bar 1A · Small Builds vs. Direct AI Coding ${smallBadge}</h3>
      <p>Target: <strong>match raw AI coding on speed (&le; 1.0x) and cost (&le; 1.0x)</strong> with <strong>100% first-try Runtime pass</strong> across Snake, 2048, and Task Manager.</p>
      <div class="kpi-row">
        <div class="kpi">
          <div class="val">${bar1.small_builds.speed_ratio_vs_direct !== null ? `${bar1.small_builds.speed_ratio_vs_direct}x` : '—'}</div>
          <div class="lbl">Speed vs Direct (&le;1.0x)</div>
        </div>
        <div class="kpi">
          <div class="val">${bar1.small_builds.cost_ratio_vs_direct !== null ? `${bar1.small_builds.cost_ratio_vs_direct}x` : '—'}</div>
          <div class="lbl">Cost vs Direct (&le;1.0x)</div>
        </div>
        <div class="kpi">
          <div class="val">${bar1.small_builds.first_try_runtime_pass_pct !== null ? `${bar1.small_builds.first_try_runtime_pass_pct}%` : '—'}</div>
          <div class="lbl">1st-Try Pass (100%)</div>
        </div>
      </div>
      ${renderProgressMeter(bar1.small_builds.first_try_runtime_pass_pct ?? 0, 100, 'First-Try Hosted Runtime Pass Rate')}
    </div>

    <div class="card bar-orange">
      <h3>Bar 1B · Larger Real-World Codebases ${largeBadge}</h3>
      <p>Target (where direct coding slows to <code>30–60+ min</code> of regressions &amp; rework): <strong>2.0x–3.0x faster feature iteration</strong>, <strong>&gt; 50% lower rework cost</strong>, and incremental brownfield repo sync.</p>
      <div class="kpi-row">
        <div class="kpi">
          <div class="val">${bar1.large_codebases.feature_iteration_speedup_x !== null ? `${bar1.large_codebases.feature_iteration_speedup_x}x` : 'Pending'}</div>
          <div class="lbl">Speedup (Target 2–3x)</div>
        </div>
        <div class="kpi">
          <div class="val">${bar1.large_codebases.rework_cost_reduction_pct !== null ? `${bar1.large_codebases.rework_cost_reduction_pct}%` : 'Pending'}</div>
          <div class="lbl">Rework Cut (&gt;50%)</div>
        </div>
        <div class="kpi">
          <div class="val">${bar1.large_codebases.existing_repo_sync_ready ? 'Ready' : 'In Flight'}</div>
          <div class="lbl">Brownfield Repo Sync</div>
        </div>
      </div>
      ${renderProgressMeter(bar1.large_codebases.rework_cost_reduction_pct ?? 0, 50, 'Rework Cost Reduction vs Direct Coding')}
    </div>

    <div class="card bar-green">
      <h3>Bar 2 · Autopilot Zero-Edit Completion ${apBadge}</h3>
      <p>Target: raise end-to-end delivery (<code>prompts &rarr; Runtime verification &rarr; merged code</code> with zero human edits) from <strong>~50% baseline today to 90%–95%</strong> across real repos.</p>
      <div class="kpi-row">
        <div class="kpi">
          <div class="val">${bar2.zero_edit_completion_pct !== null ? `${bar2.zero_edit_completion_pct}%` : '—'}</div>
          <div class="lbl">Merged Zero-Edit (${bar2.zero_edit_merged_runs}/${bar2.evaluated_runs})</div>
        </div>
        <div class="kpi">
          <div class="val">${bar2.observe_included_completion_pct !== null ? `${bar2.observe_included_completion_pct}%` : '—'}</div>
          <div class="lbl">Incl. Observe (${bar2.observe_included_completed_runs}/${bar2.evaluated_runs})</div>
        </div>
        <div class="kpi">
          <div class="val">${bar2.reopened_7d}</div>
          <div class="lbl">7-Day Reopens (Target 0)</div>
        </div>
      </div>
      ${renderProgressMeter(bar2.zero_edit_completion_pct ?? 0, 90, 'Strict Merged Zero-Edit Completion (Baseline ~50%)')}
    </div>
  </div>

  <h2>1. Release Regression Advisory Check (${esc(candidate?.version || 'Candidate')}${baseline?.version ? ` vs ${esc(baseline.version)}` : ''})</h2>
  <div class="card ${comparison.advisory_warning_count > 0 ? 'bar-red' : 'bar-green'}">
    ${warningsHtml}
  </div>

  <h2>2. Inline SVG Trend Charts (Authoring, Runtime, Tokens, Skills &amp; Autopilot Observe)</h2>
  <div class="grid2">
    ${chartsHtml.join('\n')}
  </div>

  ${candidate ? `
  <h2>3. PDD Release Authoring &amp; Runtime Matrix (${esc(candidate.version)})</h2>
  <table>
    <thead>
      <tr>
        <th>Workload</th>
        <th>Authoring Wall Time</th>
        <th>Prompt-Only Phase</th>
        <th>Post-Prompt Pre-Test</th>
        <th>Authoring Tokens &amp; USD</th>
        <th>Skills Read</th>
        <th><code>pdd lint</code></th>
        <th>Hosted <code>pdd test</code></th>
        <th>Ratio vs Direct</th>
      </tr>
    </thead>
    <tbody>
      ${candidateRowsHtml}
    </tbody>
  </table>` : ''}

  <h2>4. Autopilot Live Read-Only (<code>--observe</code>) Funnel, Dispatch Plan &amp; Quality</h2>
  <table>
    <thead>
      <tr>
        <th>Repository</th>
        <th>Open Issues</th>
        <th>Eligible (Taken %)</th>
        <th>Skipped by Reason</th>
        <th>Spread-First Dispatch Plan</th>
        <th>Zero-Edit &amp; PR Quality</th>
        <th>API &amp; ETag Telemetry</th>
      </tr>
    </thead>
    <tbody>
      ${observeRowsHtml || '<tr><td colspan="7" class="muted">No Autopilot observe runs loaded.</td></tr>'}
    </tbody>
  </table>
</div>
</body>
</html>
`;

  const sanitized = sanitizePublicText(html);
  return assertCleanPublicText(sanitized, 'HTML benchmark dashboard');
}

function parseCliArgs(argv) {
  const opts = {};
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--release-json') opts.releaseJson = argv[++i];
    else if (arg === '--observe-jsonl') opts.observeJsonl = argv[++i];
    else if (arg === '--title') opts.title = argv[++i];
    else if (arg === '--subtitle') opts.subtitle = argv[++i];
    else if (arg === '--out') opts.outFile = argv[++i];
    else if (arg === '--help' || arg === '-h') opts.help = true;
    else throw new Error(`Unknown argument: ${arg}`);
  }
  return opts;
}

const USAGE = `Usage: node scripts/benchmark/render-benchmark-report.mjs [options]
  --release-json FILE     Release benchmark JSON from run-release-benchmark.mjs
  --observe-jsonl FILE    JSONL file of Autopilot observe runs from run-autopilot-observe.mjs
  --title TEXT            Custom HTML report title
  --subtitle TEXT         Custom HTML subtitle
  --out FILE              Output self-contained HTML file path (required)
`;

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const opts = parseCliArgs(process.argv.slice(2));
    if (opts.help || !opts.outFile) {
      process.stdout.write(USAGE);
      process.exit(opts.help ? 0 : 2);
    }
    const releaseReport = opts.releaseJson
      ? JSON.parse(nativeFs.readFileSync(resolve(opts.releaseJson), 'utf8'))
      : null;
    const observeRuns = opts.observeJsonl && nativeFs.existsSync(resolve(opts.observeJsonl))
      ? parseJsonl(nativeFs.readFileSync(resolve(opts.observeJsonl), 'utf8'))
      : [];
    const html = renderBenchmarkReport({
      releaseReport,
      observeRuns,
      title: opts.title,
      subtitle: opts.subtitle,
    });
    const outPath = resolve(opts.outFile);
    nativeFs.mkdirSync(dirname(outPath), { recursive: true });
    nativeFs.writeFileSync(outPath, html, 'utf8');
    process.stdout.write(`Wrote clean benchmark dashboard to ${outPath} (${Buffer.byteLength(html, 'utf8').toLocaleString()} bytes)\n`);
  } catch (err) {
    process.stderr.write(`Render report error: ${err.message}\n`);
    process.exit(2);
  }
}
