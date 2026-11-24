import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { PUBLIC_COMMAND_ROUTES, PUBLIC_COMMAND_MANIFEST } from '../src/command-catalog.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { renderHelp } from '../src/pdd-cli.mjs';

test('3444 check route exposes --max-total-calls and --no-restart-replacement in options, manifest and help', () => {
  const checkRoute = PUBLIC_COMMAND_ROUTES.find(item => item.id === 'check');
  assert.ok(checkRoute);
  const maxTotal = checkRoute.options.find(item => item.name === '--max-total-calls');
  const noRestart = checkRoute.options.find(item => item.name === '--no-restart-replacement');
  assert.deepEqual(maxTotal, { name: '--max-total-calls', kind: 'integer', min: 1, max: 999999 });
  assert.deepEqual(noRestart, { name: '--no-restart-replacement', kind: 'flag' });
  const formEntry = PUBLIC_COMMAND_MANIFEST.find(({ form }) =>
    form === 'pdd test [PATH|STORY...] [--max-total-calls N] [--no-restart-replacement] [--max-calls N] [--timeout MIN] [--json]',
  );
  assert.ok(formEntry, 'manifest must advertise the invocation call-budget and restart-replacement form');
  const help = renderHelp(['test']);
  assert.match(help, /--max-total-calls N/);
  assert.match(help, /--no-restart-replacement/);
  assert.match(help, /1\.\.999999/);
  assert.deepEqual(
    parseArgv(['test', '--journeys', 'checkout', '--max-total-calls', '40', '--no-restart-replacement']),
    {
      commandId: 'check',
      local: 'runtime-check',
      operands: ['checkout'],
      options: { '--journeys': true, '--max-total-calls': '40', '--no-restart-replacement': true },
    },
  );
});

test('C1/S1 catalog exposes setup --skills-dir, init, status, direct prompt execution, and refuses sim/simulate', () => {
  assert.deepEqual(parseArgv(['setup', '--yes', '--skills-dir', '/tmp/skills']), {
    commandId: 'setup', local: 'setup', operands: [], options: { '--yes': true, '--skills-dir': '/tmp/skills' },
  });
  assert.deepEqual(parseArgv(['init']), {
    commandId: 'init', local: 'init', operands: [], options: {},
  });
  assert.deepEqual(parseArgv(['status', 'src/a.mjs', '--changed', '--json']), {
    commandId: 'status', local: 'status', operands: ['src/a.mjs'], options: { '--changed': true, '--json': true },
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md'], options: {},
  });
  assert.deepEqual(parseArgv(['.']), {
    commandId: 'try', local: 'runtime-try', operands: [], options: {},
  });
  assert.deepEqual(parseArgv(['--stop', 'my-story']), {
    commandId: 'try', local: 'runtime-try', operands: ['my-story'], options: { '--stop': true },
  });
  assert.throws(() => parseArgv(['sim', 'my-story']), /pdd sim was removed\. Run pdd <PROMPT\.md\|STORY> instead\./);
  assert.throws(() => parseArgv(['simulate', 'my-story']), /pdd simulate was removed\. Run pdd <PROMPT\.md\|STORY> instead\./);
});
