#!/usr/bin/env node
// Deterministic generator for command tables in docs/cli.md from PUBLIC_COMMAND_MANIFEST.
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';

export const CLI_DOCS_PATH = fileURLToPath(new URL('../docs/cli.md', import.meta.url));

export const CLI_DOC_GROUPS = Object.freeze([
  'setup',
  'autopilot-settings',
  'autopilot',
  'accounts',
  'interpreter',
  'mcp',
  'other',
  'contracts',
  'product',
  'metrics',
]);

const SETUP_IDS = new Set(['setup', 'init', 'status', 'files', 'owner', 'update', 'upgrade', 'doctor']);
const AUTOPILOT_SETTINGS_IDS = new Set([
  'autopilot.off',
  'autopilot.observe',
  'autopilot.auto',
  'autopilot.trust',
  'autopilot.untrust',
]);
const INTERPRETER_IDS = new Set(['check', 'lint', 'prove', 'try']);
const CONTRACT_IDS = new Set(['contracts', 'contracts.sync', 'product.contracts']);
const PRODUCT_IDS = new Set(['product.status', 'product.next', 'product.start', 'graph']);

export function classifyRouteGroup(route) {
  const id = String(route?.id ?? '');
  if (SETUP_IDS.has(id)) return 'setup';
  if (AUTOPILOT_SETTINGS_IDS.has(id)) return 'autopilot-settings';
  if (id === 'autopilot' || id.startsWith('autopilot.')) return 'autopilot';
  if (id === 'accounts' || id.startsWith('accounts.')) return 'accounts';
  if (INTERPRETER_IDS.has(id)) return 'interpreter';
  if (id === 'mcp') return 'mcp';
  if (CONTRACT_IDS.has(id) || id.startsWith('contracts.')) return 'contracts';
  if (PRODUCT_IDS.has(id) || id.startsWith('product.')) return 'product';
  if (id === 'metrics' || id.startsWith('metrics.')) return 'metrics';
  return 'other';
}

const escapeCell = (text) => String(text ?? '').replace(/\s+/g, ' ').trim().replaceAll('|', '\\|');

export function renderGroupTable(forms) {
  const lines = ['| Command | What it does |', '|---|---|'];
  for (const entry of forms) {
    lines.push(`| \`${escapeCell(entry.form)}\` | ${escapeCell(entry.description)} |`);
  }
  return lines.join('\n');
}

export function groupCommandForms(routes = PUBLIC_COMMAND_ROUTES) {
  const grouped = new Map(CLI_DOC_GROUPS.map((group) => [group, []]));
  const rendered = [];
  for (const route of routes) {
    const group = classifyRouteGroup(route);
    const bucket = grouped.get(group);
    if (!bucket) throw new Error(`Unknown CLI docs group "${group}" for route "${route?.id}"`);
    for (const entry of route.forms ?? []) {
      bucket.push(entry);
      rendered.push(entry.form);
    }
  }
  if (routes === PUBLIC_COMMAND_ROUTES) {
    const expected = PUBLIC_COMMAND_MANIFEST.map((entry) => entry.form);
    if (rendered.length !== expected.length || rendered.some((form, i) => !expected.includes(form))) {
      throw new Error(`Rendered command form count (${rendered.length}) does not match PUBLIC_COMMAND_MANIFEST (${expected.length}).`);
    }
  }
  return grouped;
}

const markerStart = (group) => `<!-- BEGIN GENERATED: cli-commands:${group} -->`;
const markerEnd = (group) => `<!-- END GENERATED: cli-commands:${group} -->`;

export function renderCliDocs(markdown, routes = PUBLIC_COMMAND_ROUTES) {
  const grouped = groupCommandForms(routes);
  const staleGroups = [];
  let output = String(markdown);

  for (const group of CLI_DOC_GROUPS) {
    const start = markerStart(group);
    const end = markerEnd(group);
    const firstStart = output.indexOf(start);
    if (firstStart === -1) throw new Error(`Missing generator marker: ${start}`);
    if (output.indexOf(start, firstStart + start.length) !== -1) {
      throw new Error(`Duplicate generator marker: ${start}`);
    }
    const firstEnd = output.indexOf(end, firstStart + start.length);
    if (firstEnd === -1) throw new Error(`Missing closing generator marker: ${end}`);
    if (output.indexOf(end, firstEnd + end.length) !== -1) {
      throw new Error(`Duplicate closing generator marker: ${end}`);
    }

    const before = output.slice(0, firstStart);
    const currentInner = output.slice(firstStart + start.length, firstEnd);
    const after = output.slice(firstEnd + end.length);
    const nextInner = `\n${renderGroupTable(grouped.get(group))}\n`;
    if (currentInner !== nextInner) staleGroups.push(group);
    output = `${before}${start}${nextInner}${end}${after}`;
  }

  return { output, staleGroups, changed: output !== markdown };
}

function parseCliArgs(argv) {
  let check = false;
  let file = CLI_DOCS_PATH;
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--check') check = true;
    else if (arg === '--write') check = false;
    else if (arg === '--file') {
      if (!argv[i + 1]) throw new Error('--file requires a path');
      file = resolve(argv[++i]);
    } else if (arg === '--help' || arg === '-h') {
      console.log('Usage: node scripts/generate-cli-docs.mjs [--check|--write] [--file PATH]');
      process.exit(0);
    } else {
      throw new Error(`Unknown option: ${arg}`);
    }
  }
  return { check, file };
}

export function runCli(argv = process.argv.slice(2)) {
  const { check, file } = parseCliArgs(argv);
  const current = readFileSync(file, 'utf8');
  const { output, staleGroups, changed } = renderCliDocs(current, PUBLIC_COMMAND_ROUTES);
  if (check) {
    if (changed) {
      console.error(`docs/cli.md command tables are out of sync with PUBLIC_COMMAND_MANIFEST (stale groups: ${staleGroups.join(', ')}).`);
      console.error('Run: node scripts/generate-cli-docs.mjs');
      return 1;
    }
    console.log(`docs/cli.md command tables match PUBLIC_COMMAND_MANIFEST (${PUBLIC_COMMAND_MANIFEST.length} forms across ${CLI_DOC_GROUPS.length} groups).`);
    return 0;
  }
  if (changed) {
    writeFileSync(file, output, 'utf8');
    console.log(`Updated ${file} (${PUBLIC_COMMAND_MANIFEST.length} forms across ${staleGroups.length} updated group(s)).`);
  } else {
    console.log(`${file} is already up to date (${PUBLIC_COMMAND_MANIFEST.length} forms).`);
  }
  return 0;
}

const isDirectRun = process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url);
if (isDirectRun) {
  try {
    process.exitCode = runCli();
  } catch (err) {
    console.error(err instanceof Error ? err.message : String(err));
    process.exitCode = 1;
  }
}
