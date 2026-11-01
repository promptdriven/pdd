// Child isolation bounds synchronous resolver loops and keeps fs hooks out of other tests.
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { join } from 'node:path';
const [mode, repo, moduleURL, outside] = process.argv.slice(2);
let swapped = false;
if (mode === 'race') {
  const open = fs.openSync;
  fs.openSync = function(path, ...args) {
    if (!swapped && path === join(repo, 'shared/data.md')) {
      swapped = true;
      fs.renameSync(join(repo, 'shared'), join(repo, 'original'));
      fs.symlinkSync(outside, join(repo, 'shared'));
    }
    return open.call(this, path, ...args);
  };
} else if (mode === 'title-race') {
  const read = fs.readFileSync;
  fs.readFileSync = function(path, ...args) {
    if (!swapped && path === join(repo, 'docs/story.md')) {
      swapped = true;
      fs.unlinkSync(path);
      fs.symlinkSync(join(outside, 'story.md'), path);
    }
    return read.call(this, path, ...args);
  };
}
syncBuiltinESMExports();
const { sourceFilePort, findTests } = await import(moduleURL);
let result;
try {
  if (mode === 'title-race') result = { title: findTests({root:repo}).tests.find(t=>t.path==='tests/title.json').title };
  else result = { content: sourceFilePort(repo).read({path: mode === 'race' ? 'shared/data.md' : mode === 'expanding' ? 'd/file.md' : 'l0.md'}).content };
} catch (error) { result = { exitCode: error.exitCode, message: error.message }; }
console.log(JSON.stringify({...result, swapped}));
