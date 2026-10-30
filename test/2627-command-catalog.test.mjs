// PROPOSAL ONLY: command shape and behavior have not been approved by the person.
import test from 'node:test';
import assert from 'node:assert/strict';
import { PUBLIC_COMMAND_ROUTES, PUBLIC_COMMAND_MANIFEST } from '../src/command-catalog.mjs';
import { parseArgv, CommandInputError } from '../src/argument-parser.mjs';
import { renderHelp } from '../src/pdd-cli.mjs';

const proposed = name => `2627 PROPOSAL (not approved): ${name}`;
function observedParse(words) {
  try { return { plan: parseArgv(['workflow', 'open', ...words]), error: null }; }
  catch (error) { return { plan: null, error }; }
}
function accepts(words, operands, options) {
  const observed = observedParse(words);
  assert.equal(observed.error, null, `Proposed open form must parse: ${words.join(' ')}`);
  assert.deepEqual(observed.plan, { commandId: 'workflow.open', local: 'workflow-open', operands, options });
}

test(proposed('catalog exposes one optional AREA and the --new flag'), () => {
  const route = PUBLIC_COMMAND_ROUTES.find(item => item.id === 'workflow.open');
  assert.ok(route);
  assert.equal(route.operands.length, 2, 'One ISSUE and one optional AREA');
  assert.equal(route.operands[0].type, 'issue');
  assert.equal(Boolean(route.operands[0].optional), false);
  assert.equal(route.operands[1].optional, true);
  assert.equal(Boolean(route.operands[1].repeat), false);
  assert.deepEqual(route.options.map(({ name, kind }) => ({ name, kind })), [{ name: '--new', kind: 'flag' }]);
  const forms = PUBLIC_COMMAND_MANIFEST.filter(item => /^pdd workflow open\b/.test(item.form));
  assert.ok(forms.some(({ form }) => /ISSUE\s+\[AREA\]\s+\[--new\]/.test(form)));
  const help = renderHelp(['workflow', 'open']);
  assert.match(help, /\[AREA\]/);
  assert.match(help, /\[--new\]/);
  assert.match(help, /focus|attach/i);
  assert.match(help, /resume/i);
  assert.match(help, /(?:new|fresh|replace\w*)\s+(?:\w+\s+){0,3}(?:session|chat)/i,
    'Explain fresh/replacement-session behavior, beyond merely printing --new');
});

test(proposed('parser accepts a recorded-area selector after ISSUE'), () => {
  // Preservation/error controls already pass on the base; these are not separate red cases.
  accepts(['17'], ['17'], {});
  for (const words of [[], ['17', '--unknown'], ['17', '--new', '--new'], ['17', 'plan', 'build']]) {
    const observed = observedParse(words);
    assert.ok(observed.error instanceof CommandInputError, words.join(' '));
    assert.equal(observed.error.exitCode, 2);
  }
  accepts(['example/project#17', 'plan'], ['example/project#17', 'plan'], {});
});

test(proposed('parser accepts --new without changing the issue operand'), () => {
  accepts(['17', '--new'], ['17'], { '--new': true });
});

test(proposed('parser retains AREA and --new together'), () => {
  accepts(['17', 'build', '--new'], ['17', 'build'], { '--new': true });
});
