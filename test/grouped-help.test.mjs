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

  // Leads with description, usage, and practical Quick start examples
  assert.equal(allLines[0], 'PDD: prompt-driven development for your coding agent.');
  assert.equal(allLines[2], 'Usage: pdd <command> [options]');
  assert.equal(allLines[4], 'Quick start:');
  assert.match(baseline, /Quick start:\n  pdd setup\b[\s\S]*?\n  pdd init\b[\s\S]*?\n  pdd status\b[\s\S]*?\n  pdd test\b[\s\S]*?\n  pdd simulate\b/);

  // Human-first group ordering: Core PDD workflow before Cloud accounts, Product & dependency graph, Autopilot, Metrics
  const coreIdx = baseline.indexOf('Core PDD workflow:');
  const accountsIdx = baseline.indexOf('Cloud accounts (pdd accounts --help):');
  const productIdx = baseline.indexOf('Product & dependency graph (pdd product --help):');
  const autopilotIdx = baseline.indexOf('Autopilot (pdd autopilot --help):');
  const metricsIdx = baseline.indexOf('Metrics, shell & help (pdd metrics --help):');
  assert.ok(coreIdx > 0 && coreIdx < accountsIdx, 'Core PDD workflow comes before Cloud accounts');
  assert.ok(accountsIdx < productIdx, 'Cloud accounts comes before Product & dependency graph');
  assert.ok(productIdx < autopilotIdx, 'Product & dependency graph comes before Autopilot');
  assert.ok(autopilotIdx < metricsIdx, 'Autopilot comes before Metrics, shell & help');

  // Core commands come right at the top, not buried behind metrics/internals
  assert.ok(baseline.indexOf('  pdd setup [--yes]') < baseline.indexOf('  pdd metrics'));
  const initIdx = baseline.indexOf('  pdd init', coreIdx);
  const statusIdx = baseline.indexOf('  pdd status [PATH...]', coreIdx);
  assert.ok(initIdx > coreIdx && initIdx < accountsIdx);
  assert.ok(statusIdx > coreIdx && statusIdx < accountsIdx);
  assert.ok(baseline.indexOf('  pdd autopilot logs [ISSUE] [-f]') > autopilotIdx);
  assert.ok(baseline.includes('  pdd --version | -V | pdd -VV   Show CLI version (and interpreter build).'));

  // No duplicate approval heredoc blocks or stale removed-engine migration note on root help
  assert.doesNotMatch(baseline, /<<'PDD_SAID'/);
  assert.doesNotMatch(baseline, /removed full engine/i);

  // Every single line of root `pdd --help` (including heading, groups, learnLines, and closingLines) fits in <= 80 columns
  for (const line of allLines) {
    assert.ok(line.length <= 80, `root help line exceeds 80 columns (${line.length}): "${line}"`);
  }
  for (const line of PUBLIC_HELP_TEXT.closingLines) {
    assert.ok(line.length <= 80, `closingLine exceeds 80 columns (${line.length}): "${line}"`);
  }

  // Preserves Focused help guidance and installed PDD skill / Prompting guide paths
  assert.match(baseline, /Focused help: run pdd <command> --help/);
  assert.match(baseline, /Skill: \/opt\/pdd\/skills\/pdd\/SKILL\.md/);
  assert.match(baseline, /Prompting guide: \/opt\/pdd\/skills\/pdd\/references\/prompting\.md/);
});

test('3496: focused family and command help exposes complete options, defaults, constraints and approval heredocs', async () => {
  const families = ['test', 'lint', 'simulate', 'approve', 'accounts', 'product', 'autopilot', 'metrics'];
  for (const family of families) {
    const res = await runHelp([family, '--help']);
    assert.equal(res.exit, 0, `${family} --help`);
    assert.equal(res.stderr, '', `${family} --help`);
    const expectedForms = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => form.slice(4).split(/\s+/)[0] === family);
    assert.ok(expectedForms.length > 0, `manifest has forms for ${family}`);
    for (const entry of expectedForms) {
      assert.ok(res.stdout.includes(`  ${entry.form}  ${entry.description}`), `${family} --help includes ${entry.form}`);
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
  const topWords = new Set(PUBLIC_COMMAND_ROUTES.map(r => r.prefix[0]).filter(w => w !== 'help'));
  for (const word of topWords) {
    assert.ok(word.startsWith('-') ? rootText.includes(word) : rootText.includes(`pdd ${word}`), `root help mentions top-level command "${word}"`);
  }
});
