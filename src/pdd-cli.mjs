import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { CommandInputError, parseArgv } from './argument-parser.mjs';
import { renderCompletion } from './completion.mjs';
import { PUBLIC_COMMAND_IDS, PUBLIC_COMMAND_MANIFEST, PUBLIC_COMMAND_ROUTES } from './command-catalog.mjs';
import { loadInstalledHost } from './host-adapter.mjs';
import { formatLocalWorkflows, listLocalWorkflows } from './workflow-list.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const HOST_UNAVAILABLE = {
  missing: 'The installed PDD Host entry module is missing. See the PDD setup guide for supported distribution availability: docs/setup.md in this package',
  'load-failed': 'The installed PDD Host could not load; its files or dependencies may be incomplete. See the PDD setup guide for supported distribution availability before repairing the Host: docs/setup.md in this package',
  incompatible: 'The installed PDD Host does not export the supported command entry. See the PDD setup guide for compatible distribution availability: docs/setup.md in this package',
  unknown: 'This command needs the installed PDD Host. See the PDD setup guide for supported distribution availability: docs/setup.md in this package',
};

function writeLine(stream, text) {
  stream.write(`${text}\n`);
}

export function renderHelp(prefix = []) {
  const normalized = Array.isArray(prefix) ? prefix : [];
  const rows = PUBLIC_COMMAND_MANIFEST.filter(({ form }) => {
    if (!normalized.length) return true;
    const command = form.slice('pdd '.length).split(/\s+/);
    return normalized.every((token, index) => command[index] === token);
  });
  const heading = normalized.length ? `PDD ${normalized.join(' ')} commands` : 'PDD commands';
  const entries = rows.map(({ form, description }) => `  ${form}  ${description}`);
  return [
    `${heading}\n`,
    ...entries,
    '',
    'Help, version, skill output, completion and local workflow listing work from this source tree.',
    'Host-dependent commands use the installed PDD Host and keep its person and approval checks.',
    'If Host is unavailable, those commands explain the problem and point to distribution availability in the setup guide.',
  ].join('\n');
}

function packageVersion(packageRoot) {
  const metadata = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8'));
  return typeof metadata.version === 'string' ? metadata.version : 'unknown';
}

function printSkill({ packageRoot, stdout, stderr }) {
  const skillPath = join(packageRoot, 'skills', 'pdd', 'SKILL.md');
  try {
    const skill = readFileSync(skillPath, 'utf8');
    stdout.write(skill.endsWith('\n') ? skill : `${skill}\n`);
    return 0;
  } catch (error) {
    if (error?.code !== 'ENOENT') throw error;
    writeLine(stderr, 'The PDD skill file is missing from this package checkout: skills/pdd/SKILL.md.');
    return 1;
  }
}

async function runHostCommand(plan, { env, stdin, stdout, stderr, loadHost }) {
  if (!PUBLIC_COMMAND_IDS.includes(plan.commandId) || plan.host !== true || !Array.isArray(plan.hostArgv)) {
    writeLine(stderr, 'This command is not available in this PDD build.');
    return 2;
  }
  let runCli;
  let unavailable = 'unknown';
  try {
    runCli = await loadHost({ onUnavailable: (reason) => {
      if (Object.hasOwn(HOST_UNAVAILABLE, reason)) unavailable = reason;
    } });
  } catch { runCli = null; unavailable = 'load-failed'; }
  if (typeof runCli !== 'function') {
    writeLine(stderr, HOST_UNAVAILABLE[unavailable]);
    return 69;
  }
  try {
    const result = await runCli([...plan.hostArgv], {
      env,
      stdin,
      stdout,
      stderr,
      say: (message) => writeLine(stdout, message),
      err: (message) => writeLine(stderr, message),
    });
    if (Number.isInteger(result) && result >= 0 && result <= 255) return result;
    writeLine(stderr, 'The installed PDD Host returned an invalid command status.');
    return 1;
  } catch (error) {
    if (Number.isInteger(error?.exitCode) && error.exitCode >= 1 && error.exitCode <= 255) return error.exitCode;
    writeLine(stderr, 'The installed PDD Host could not complete this command.');
    return 1;
  }
}

export async function runPdd(argv, {
  stdout = process.stdout,
  stderr = process.stderr,
  stdin = process.stdin,
  env = process.env,
  cwd = process.cwd(),
  packageRoot = PACKAGE_ROOT,
  loadHost = loadInstalledHost,
} = {}) {
  let plan;
  try {
    plan = parseArgv(argv);
  } catch (error) {
    if (error instanceof CommandInputError || Number.isInteger(error?.exitCode)) {
      writeLine(stderr, error.message);
      return error.exitCode ?? 2;
    }
    writeLine(stderr, 'The PDD command could not be parsed. Run pdd --help.');
    return 2;
  }

  if (!PUBLIC_COMMAND_IDS.includes(plan.commandId)) {
    writeLine(stderr, 'This command is not available in this PDD build.');
    return 2;
  }

  switch (plan.local) {
    case 'help':
      stdout.write(`${renderHelp(plan.helpPrefix)}\n`);
      return 0;
    case 'version':
      writeLine(stdout, `pdd ${packageVersion(packageRoot)}`);
      return 0;
    case 'skill':
      return printSkill({ packageRoot, stdout, stderr });
    case 'completion':
      try {
        stdout.write(renderCompletion(plan.operands[0]));
        return 0;
      } catch (error) {
        writeLine(stderr, error.message);
        return 2;
      }
    case 'workflow-list':
      try {
        const catalog = listLocalWorkflows({ cwd });
        writeLine(stdout, formatLocalWorkflows(catalog, { json: plan.options['--json'] === true }));
        return 0;
      } catch {
        writeLine(stderr, 'Workflows in .pdd/workflows could not be read.');
        return 1;
      }
    default:
      return runHostCommand(plan, { env, stdin, stdout, stderr, loadHost });
  }
}
