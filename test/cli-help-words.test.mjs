import test from 'node:test';
import assert from 'node:assert/strict';
import { parseArgv } from '../src/argument-parser.mjs';

test('-help works like --help', () => {
  assert.equal(parseArgv(['-help']).local, 'help');
  assert.deepEqual(parseArgv(['workflow', '-help']).helpPrefix, ['workflow']);
});

test('an unknown command is named in the error', () => {
  assert.throws(() => parseArgv(['install']), { message: 'Unknown command "install". Run pdd --help to see the commands.' });
  assert.throws(() => parseArgv(['se\x1btup']), { message: 'Unknown command "se tup". Run pdd --help to see the commands.' });
});
