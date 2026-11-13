// Native CLI fault fixture: keep filesystem writes real, obstruct only summary publication.
// This preload also fails if an offline command tries authentication or transport.
import fs from 'node:fs';
import childProcess from 'node:child_process';
import {dirname,join} from 'node:path';
import {syncBuiltinESMExports} from 'node:module';

globalThis.fetch = () => { throw Error('Offline local lint must not call fetch'); };
for (const name of ['spawn','spawnSync','execFileSync']) {
  const native = childProcess[name];
  childProcess[name] = function(command,...args) {
    if (/(^|\/)gh$/.test(command)) throw Error('Offline local lint must not authenticate');
    return native.call(this,command,...args);
  };
}
if (process.env.PDD_TEST_OBSTRUCT_LOCAL_SUMMARY === '1') {
  const rename = fs.renameSync;
  fs.renameSync = function(from,to) {
    const result = rename.call(this,from,to);
    if (String(to).endsWith('/batch.json')) fs.mkdirSync(join(dirname(to),'summary.json'));
    return result;
  };
}
syncBuiltinESMExports();
