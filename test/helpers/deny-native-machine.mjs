// Preload for offline boundary checks. Refuse before any host observation.
import fs from 'node:fs';
import os from 'node:os';
import childProcess from 'node:child_process';
import {syncBuiltinESMExports} from 'node:module';

const refused = operation => { throw Object.assign(Error(`Native machine observation refused: ${operation}`), {code:'NATIVE_MACHINE_READ'}); };
for (const name of ['readFileSync','readdirSync','accessSync','statSync','statfsSync']) {
  const native = fs[name];
  fs[name] = function(path, ...args) {
    if (name === 'statfsSync' || /^\/(proc|sys)(\/|$)/.test(String(path)) || /\/taskset$/.test(String(path))) refused(`${name} ${path}`);
    return native.call(this, path, ...args);
  };
}
for (const name of ['cpus','availableParallelism','loadavg','freemem','totalmem']) os[name] = () => refused(name);
for (const name of ['spawn','spawnSync','execFileSync']) {
  const native = childProcess[name];
  childProcess[name] = function(command, ...args) {
    if (/(^|\/)(nproc|taskset|systemd-detect-virt)$/.test(command)) refused(command);
    return native.call(this, command, ...args);
  };
}
syncBuiltinESMExports();
