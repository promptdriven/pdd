// Generated from examples/native-replay/replay.prompt.md.
import {readFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
import {isDeepStrictEqual} from 'node:util';

try {
  const [file, modulePath, ...extra] = process.argv.slice(2);
  if (!file || !modulePath || extra.length) throw new Error('usage: node replay.mjs CASES MODULE');
  const data = JSON.parse(await readFile(file, 'utf8'));
  if (!Array.isArray(data.cases) || !data.cases.length) throw new Error('cases must be a nonempty array');
  for (const c of data.cases) {
    const keys = c?.expected && Object.keys(c.expected);
    if (typeof c?.id !== 'string' || !c.id || !Object.hasOwn(c, 'input') || !keys || keys.length !== 1 ||
        !(keys[0] === 'return' || keys[0] === 'error' && typeof c.expected.error?.name === 'string' && typeof c.expected.error?.message === 'string'))
      throw new Error('invalid case');
  }
  const {countWords} = await import(pathToFileURL(resolve(modulePath)).href);
  if (typeof countWords !== 'function') throw new Error('missing countWords export');
  let passed = 0;
  for (const c of data.cases) {
    let value, error, threw = false;
    try { value = await countWords(c.input); } catch (e) { threw = true; error = e; }
    const ok = Object.hasOwn(c.expected, 'error')
      ? threw && error?.name === c.expected.error.name && error?.message === c.expected.error.message
      : !threw && isDeepStrictEqual(value, c.expected.return);
    if (ok) passed++;
    console.log(`${ok ? 'PASS' : 'FAIL'} ${c.id}`);
  }
  console.log(`${passed}/${data.cases.length} passed`);
  if (passed !== data.cases.length) process.exitCode = 1;
} catch (error) {
  console.error(`setup: ${error.message}`);
  process.exitCode = 1;
}
