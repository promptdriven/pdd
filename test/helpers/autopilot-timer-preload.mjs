// Child-only observation seam. The generated launcher entry point stays native.
import './deny-native-machine.mjs';
import assert from 'node:assert/strict';
import {registerHooks} from 'node:module';
import {fileURLToPath} from 'node:url';

// Fake git/gh/Herdr executables are separate Node programs, not launcher entries.
delete process.env.NODE_OPTIONS;
assert.equal(process.argv[1], fileURLToPath(new URL('../../src/autopilot-launcher.mjs', import.meta.url)));
const checkMachine = JSON.stringify(new URL('./check-machine.mjs', import.meta.url).href);
const healthyMachine = JSON.stringify(new URL('./healthy-machine.mjs', import.meta.url).href);
const sources = new Map([
  [new URL('../../src/machine-resources.mjs', import.meta.url).href, `
    import {checkMachine, GiB} from ${checkMachine};
    export const machineCheckPorts = () => checkMachine().ports;
    // #3231: no Autopilot job runs on this test machine.
    export const readAutopilotUse = () => ({processes:0, wrappers:0, rss:0, cores:0});
    export async function readMachineResources() {
      const p = machineCheckPorts();
      return {cpuCount:40, load:p.load(), memory:{available:p.memory(),total:256*GiB},
        disk:{available:80*GiB,total:100*GiB}, pressure:{io:0,memory:0},
        check:{cpuIds:p.cores(),platform:p.platform,battery:p.battery(),virtualized:p.virtualized(),taskset:p.taskset()}};
    }
  `],
  [new URL('../../src/codex-limits.mjs', import.meta.url).href, `
    import {healthyMachine} from ${healthyMachine};
    export const readCodexLimits = healthyMachine.codexLimits;
  `],
]);
registerHooks({load(url, context, nextLoad) {
  if (sources.has(url)) return {format:'module',source:sources.get(url),shortCircuit:true};
  return nextLoad(url, context);
}});
