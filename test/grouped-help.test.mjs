import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES, PUBLIC_HELP_TEXT } from '../src/command-catalog.mjs';
import { renderHelp, runPdd } from '../src/pdd-cli.mjs';

const sink = () => ({ text: '', write(chunk) { this.text += chunk; return true; } });
const ANSI_RE = /\x1b\[[0-9;]*[A-Za-z]/;

async function runHelp(argv, packageRoot = '/opt/pdd') {
  const stdout = sink(), stderr = sink();
  const exit = await runPdd(argv, { stdout, stderr, packageRoot, cwd: '/nonexistent/dir' });
  return { exit, stdout: stdout.text, stderr: stderr.text };
}

test('3496: root help is concise, grouped human-first, 80-column wrapped in its catalog body, and identical across aliases', async () => {
  const aliases = [[], ['--help'], ['-h'], ['-help'], ['help']];
  const results = await Promise.all(aliases.map(argv => runHelp(argv)));
  const baseline = results[0].stdout;

  for (let i = 0; i < aliases.length; i++) {
    assert.equal(results[i].exit, 0, JSON.stringify(aliases[i]));
    assert.equal(results[i].stderr, '', JSON.stringify(aliases[i]));
    assert.equal(results[i].stdout, baseline, JSON.stringify(aliases[i]));
    assert.doesNotMatch(results[i].stdout, ANSI_RE);
  }

  // Concise scannable entry point rather than multi-page wall of option paragraphs
  assert.ok(Buffer.byteLength(baseline, 'utf8') < 6500, `expected concise root help, got ${Buffer.byteLength(baseline, 'utf8')} bytes`);
  const allLines = baseline.replace(/\n$/, '').split('\n');
  assert.ok(allLines.length < 90, `expected < 90 lines in root help, got ${allLines.length}`);

  // Leads with description, usage, and concise numbered Quick start
  assert.equal(allLines[0], 'PDD: prompt-driven development for your coding agent.');
  assert.equal(allLines[2], 'Usage: pdd <PROMPT.md|STORY|.> [args...]  |  pdd <command> [options]');
  assert.equal(allLines[4], 'Quick start:');
  assert.match(baseline, /Quick start:\n  1\. pdd setup\b[\s\S]*?\n  2\. pdd init\b[\s\S]*?\n  3\. \/pdd <task>[\s\S]*?\n  4\. pdd prove\b/);
  assert.ok(baseline.includes('  pdd <PROMPT.md|STORY|.>'), 'Core workflow leads with direct prompt execution');
  assert.doesNotMatch(baseline, /\b(?:sim|simulate|simulator)\b/i, 'root help has zero sim/simulate/Simulator wording');

  // Human-first group ordering: Core PDD workflow before Product & graph, Autopilot, Cloud accounts, Metrics
  const coreIdx = baseline.indexOf('Core PDD workflow:');
  const productIdx = baseline.indexOf('Product & graph (pdd product --help):');
  const autopilotIdx = baseline.indexOf('Autopilot (pdd autopilot --help):');
  const accountsIdx = baseline.indexOf('Cloud accounts (pdd accounts --help):');
  const metricsIdx = baseline.indexOf('Metrics, shell & help:');
  assert.ok(coreIdx > 0 && coreIdx < productIdx, 'Core PDD workflow comes before Product & graph');
  assert.ok(productIdx < autopilotIdx, 'Product & graph comes before Autopilot');
  assert.ok(autopilotIdx < accountsIdx, 'Autopilot comes before Cloud accounts');
  assert.ok(accountsIdx < metricsIdx, 'Cloud accounts comes before Metrics, shell & help');

  // Core commands come right at the top, not buried behind metrics/internals
  assert.ok(baseline.indexOf('  1. pdd setup') < baseline.indexOf('  pdd metrics'));
  const statusIdx = baseline.indexOf('  pdd status [--changed]', coreIdx);
  assert.ok(statusIdx > coreIdx && statusIdx < productIdx);
  assert.ok(baseline.indexOf('  pdd autopilot status|logs') > autopilotIdx);
  assert.ok(baseline.includes('  pdd --version, pdd -V, pdd -VV Show CLI version & interpreter build.'));

  // No removed approve command, duplicate approval heredoc blocks or stale removed-engine migration note on root help
  assert.doesNotMatch(baseline, /\bapprove\b/i);
  assert.doesNotMatch(baseline, /<<'PDD_SAID'/);
  assert.doesNotMatch(baseline, /removed full engine/i);

  // Every single line of root `pdd --help` (including heading, groups, learnLines, and closingLines) fits in <= 80 columns
  for (const line of allLines) {
    assert.ok(line.length <= 80, `root help line exceeds 80 columns (${line.length}): "${line}"`);
  }
  for (const line of PUBLIC_HELP_TEXT.closingLines) {
    assert.ok(line.length <= 80, `closingLine exceeds 80 columns (${line.length}): "${line}"`);
  }
  for (const line of PUBLIC_HELP_TEXT.promptingLines) {
    assert.ok(line.length <= 80, `promptingLine exceeds 80 columns (${line.length}): "${line}"`);
  }

  // Preserves Focused help guidance and installed PDD skill / Prompting guide paths
  assert.match(baseline, /Run pdd <command> --help for full options/);
  assert.match(baseline, /Skill: \/opt\/pdd\/skills\/pdd\/SKILL\.md/);
  assert.match(baseline, /Prompting guide: \/opt\/pdd\/skills\/pdd\/references\/prompting\.md/);
});

test('3496: focused family and command help exposes complete options, defaults, and constraints within 80 columns', async () => {
  const families = ['test', 'lint', 'prove', '.', 'accounts', 'product', 'autopilot', 'metrics'];
  for (const family of families) {
    const res = await runHelp([family, '--help']);
    assert.equal(res.exit, 0, `${family} --help`);
    assert.equal(res.stderr, '', `${family} --help`);
    assert.doesNotMatch(res.stdout, /\b(?:sim|simulate|simulator)\b/i, `${family} --help has zero sim/simulate/Simulator wording`);
    const unwrapped = res.stdout.replace(/\|\n      /g, '|').replace(/\n      /g, ' ');
    const expectedForms = family === '.'
      ? PUBLIC_COMMAND_ROUTES.find(r => r.id === 'try').forms
      : PUBLIC_COMMAND_MANIFEST.filter(({ form }) => form.slice(4).split(/\s+/)[0] === family);
    assert.ok(expectedForms.length > 0, `manifest has forms for ${family}`);
    for (const entry of expectedForms) {
      assert.ok(unwrapped.includes(`  ${entry.form}\n`), `${family} --help includes ${entry.form}`);
    }
    // Every rendered line (both wrapped usage forms and wrapped descriptions) fits in <= 80 columns
    for (const renderedLine of res.stdout.split('\n')) {
      assert.ok(renderedLine.length <= 80, `${family} --help line exceeds 80 columns (${renderedLine.length}): "${renderedLine}"`);
    }
  }

  // Autopilot start focused help keeps complete options and removes stale full-engine migration sentence
  const startHelp = renderHelp(['autopilot', 'start']);
  assert.match(startHelp, /--mode auto\|observe\|off/);
  assert.match(startHelp, /--share PERCENT/);
  assert.doesNotMatch(startHelp, /removed full engine/i);

  // Autopilot logs focused help documents both positional ISSUE and --issue N forms
  const logsHelp = renderHelp(['autopilot', 'logs']);
  assert.match(logsHelp, /pdd autopilot logs \[ISSUE\] \[--follow\|-f\] \[--lines N\] \[--json\]/);
  assert.match(logsHelp, /pdd autopilot logs --issue N \[--follow\|-f\] \[--lines N\] \[--json\]/);
  assert.match(logsHelp, /observe mode/);

  // Every top-level command family in PUBLIC_COMMAND_ROUTES is discoverable from root --help
  const rootText = renderHelp([], '/opt/pdd');
  const topWords = new Set(PUBLIC_COMMAND_ROUTES.map(r => r.prefix[0]).filter(w => w && w !== 'help'));
  for (const word of topWords) {
    assert.ok(word.startsWith('-') ? rootText.includes(word) : rootText.includes(`pdd ${word}`), `root help mentions top-level command "${word}"`);
  }
});
