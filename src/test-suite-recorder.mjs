// Generated from prompts/cli/test-suite-queue.prompt.md (sha256: a971f88ae1db279eea4f13ba3871c6e329e18bc343b0db7579146e961739c038).
// This process keeps validation evidence when the calling chat disappears.
import * as fs from 'node:fs';
import {randomUUID} from 'node:crypto';
import {executeSuite} from './test-suite-queue.mjs';

let started = false;
const send = message => {
  if (process.connected) try { process.send(message, () => {}); } catch {}
};
// Losing the caller is not a request to cancel an already admitted command.
process.on('disconnect', () => { if (!started) process.exitCode = 1; });
process.on('message', async message => {
  if (message.cancel && started) { process.emit(message.cancel); return; }
  if (!message.start || started) return;
  started = true;
  const {command, record, environmentRoot, ...options} = message.start;
  const save = () => {
    const temp = `${record.receiptPath}.${randomUUID()}.tmp`;
    try { fs.writeFileSync(temp, JSON.stringify(record), {mode:0o600}); fs.renameSync(temp,record.receiptPath); }
    finally { try { fs.unlinkSync(temp); } catch {} }
  };
  let pending = '', summary = {}, complete = null, tap = false, plan = false;
  const keys = ['tests','suites','pass','fail','cancelled','skipped','todo'];
  const output = (stream, bytes) => {
    fs.appendFileSync(record.logPath,bytes);
    if (stream === 'stdout') {
      // Summary lines are short. Never retain a large, unterminated output line.
      for (const part of bytes.toString('utf8').split(/(?<=\n)/)) {
        pending += part;
        if (pending.endsWith('\n')) {
          const header = /^TAP version 13\r?\n$/.test(pending);
          const planLine = /^1\.\.\d+(?: # [^\r\n]*)?\r?\n$/.test(pending);
          const duration = /^# duration_ms \d+(?:\.\d+)?\r?\n$/.test(pending);
          const match = /^# (tests|suites|pass|fail|cancelled|skipped|todo) (\d+)\r?\n$/.exec(pending);
          if (header) { tap = true; plan = false; summary = {}; complete = null; }
          else if (planLine) { plan = true; summary = {}; complete = null; }
          else if (match && Number.isSafeInteger(Number(match[2]))) {
            if (match[1] === 'tests') { summary = {}; complete = null; }
            if (match[1] !== keys[Object.keys(summary).length]) { summary = {}; complete = null; }
            else {
              summary[match[1]] = Number(match[2]);
              if (tap && plan && keys.every(key => summary[key] !== undefined)) complete = {...summary};
            }
          } else if (!duration && pending.trim()) { summary = {}; complete = null; }
          pending = '';
        } else if (pending.length > 256) pending = '!';
      }
    }
    send({stream,bytes:bytes.toString('base64')});
  };
  let result;
  try {
    result = await executeSuite(command, {...options,startGate:true,onOutput:output,
      onChild: pid => { record.childPid = pid; save(); }});
    record.exitCode = result.exitCode; record.signal = result.signal ?? null;
    record.outcome = result.ownershipConfirmed === false ? 'unknown' : 'completed';
    record.exitCode = result.ownershipConfirmed === false ? null : result.exitCode;
    record.counts = record.outcome === 'completed' && !pending ? complete : null;
  } catch (error) {
    result = {exitCode:1,reason:`Validation recorder failed: ${error.code ?? error.message}`};
    record.exitCode = null; record.signal = null; record.outcome = 'unknown'; record.counts = null;
  }
  try {
    if (environmentRoot && record.outcome === 'completed') fs.rmSync(environmentRoot,{recursive:true,force:true});
    record.state = record.outcome === 'completed' ? 'finished' : 'running'; record.finishedAt = record.state === 'finished' ? Date.now() : null;
    record.reason = result.reason ?? (result.exitCode ? `Test suite exited with status ${result.exitCode}.` : null);
    save();
    send({result:{...result,record}});
  } catch (error) {
    // No terminal message may claim a receipt that was not saved.
    process.exitCode = 1;
  } finally {
    if (process.connected) process.disconnect();
  }
});
