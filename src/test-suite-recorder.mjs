// Generated from prompts/cli/test-suite-queue.prompt.md (sha256: 9a6fbeb4f0e51d65db80cee642a73f0977c1943b8a6548f9c24281b66b319d3c).
// This process keeps validation evidence when the calling chat disappears.
import {rememberSecrets} from './secret-redaction.mjs';
import * as fs from 'node:fs';
import {randomUUID} from 'node:crypto';
import {serializeValidationReceipt, redactingLines, validationLog, safeEvidenceText} from './validation-evidence.mjs';
import {executeSuite} from './test-suite-queue.mjs';
import {parseTestSummaryOutput} from './autopilot/core/test-runners.mjs';

let started = false;
const send = (message, done = () => {}) => {
  if (process.connected) try { process.send(message, done); return; } catch {}
  done();
};
// Losing the caller is not a request to cancel an already admitted command.
process.on('disconnect', () => { if (!started) process.exitCode = 1; });
process.on('message', async message => {
  if (message.cancel && started) { process.emit(message.cancel); return; }
  if (!message.start || started) return;
  started = true;
  const {command, record, environmentRoot, secrets = [], ...options} = message.start;
  rememberSecrets(...secrets);
  const save = () => {
    const temp = `${record.receiptPath}.${randomUUID()}.tmp`;
    try { fs.writeFileSync(temp, serializeValidationReceipt(record), {mode:0o600}); fs.renameSync(temp,record.receiptPath); }
    finally { try { fs.unlinkSync(temp); } catch {} }
  };
  const log = validationLog(bytes=>fs.writeFileSync(record.logPath,bytes,{mode:0o600}),
    bytes=>fs.appendFileSync(record.logPath,bytes));
  record.evidence = log.evidence;
  let safeParts = [], suppressed = 0;
  const filters = Object.fromEntries(['stdout','stderr'].map(stream=>[stream,redactingLines((text,omitted)=>{
    safeParts.push(text); suppressed += omitted;
  })]));
  const flush = stream => {
    if (!safeParts.length) return;
    const text = safeParts.join('');
    log.add(text,suppressed);
    safeParts = []; suppressed = 0;
    send({stream,bytes:Buffer.from(text).toString('base64')});
  };
  let pending = '', summary = {}, complete = null, tap = false, plan = false;
  let polyPending = '', polyOverflow = false, polyBytes = 0;
  const polyLines = [];
  const MAX_POLY_BYTES = 262_144, MAX_POLY_LINE = 1024;
  const keys = ['tests','suites','pass','fail','cancelled','skipped','todo'];
  const pushPolyLine = line => {
    polyLines.push(line); polyBytes += line.length;
    if (polyBytes <= MAX_POLY_BYTES) return;
    let keptBytes = 0;
    const tail = [];
    for (let i = polyLines.length - 1; i >= 0 && keptBytes < 65_536; i -= 1) {
      tail.push(polyLines[i]); keptBytes += polyLines[i].length;
    }
    tail.reverse();
    const tailStart = polyLines.length - tail.length;
    const anchors = [];
    for (let i = 0; i < tailStart && keptBytes < MAX_POLY_BYTES - 16_384; i += 1) {
      const l = polyLines[i];
      if (/^(?:running \d+ tests?|test result:)|\s*"Action"\s*:\s*"(?:run|pass|fail|skip|build-fail)"/.test(l)) {
        anchors.push(l); keptBytes += l.length;
      }
    }
    polyLines.length = 0;
    polyLines.push(...anchors, ...tail);
    polyBytes = keptBytes;
  };
  const output = (stream, bytes) => {
    log.evidence.outputBytes += bytes.length;
    filters[stream].write(bytes); flush(stream);
    if (stream === 'stdout') {
      // Summary lines are short. Never retain a large, unterminated output line.
      for (const part of bytes.toString('utf8').split(/(?<=\n)/)) {
        if (polyOverflow) {
          if (part.endsWith('\n')) { polyPending = ''; polyOverflow = false; }
        } else {
          polyPending += part;
          if (polyPending.endsWith('\n')) { pushPolyLine(polyPending); polyPending = ''; }
          else if (polyPending.length > MAX_POLY_LINE) { polyPending = ''; polyOverflow = true; }
        }
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

  };
  let result;
  let flushed = false;
  try {
    result = await executeSuite(command, {...options,startGate:true,onOutput:output,
      onChild: pid => { record.childPid = pid; save(); }});
    for (const stream of ['stdout','stderr']) { filters[stream].end(); flush(stream); }
    log.flush();
    flushed = true;
    record.exitCode = result.exitCode; record.signal = result.signal ?? null;
    if (result.signalDiagnostics) record.signalDiagnostics = result.signalDiagnostics;
    record.outcome = result.ownershipConfirmed === false ? 'unknown' : 'completed';
    record.exitCode = result.ownershipConfirmed === false ? null : result.exitCode;
    let counts = null;
    if (record.outcome === 'completed' && !pending) {
      if (complete) counts = complete;
      else if (!tap && polyLines.length) {
        const parsed = parseTestSummaryOutput(polyLines.join(''));
        if (parsed && parsed.format !== 'tap') {
          counts = {
            tests: parsed.total, pass: parsed.passed, fail: parsed.failed, skipped: parsed.skipped,
            total: parsed.total, passed: parsed.passed, failed: parsed.failed, format: parsed.format,
          };
        }
      }
    }
    record.counts = counts;
  } catch (error) {
    result = {exitCode:1,reason:safeEvidenceText(`Validation recorder failed: ${error.code ?? error.message}`)};
    record.exitCode = null; record.signal = null; record.outcome = 'unknown'; record.counts = null;
  } finally {
    if (!flushed) {
      for (const stream of ['stdout','stderr']) { try { filters[stream].end(); flush(stream); } catch {} }
      try { log.flush(); } catch {}
    }
  }
  try {
    if (environmentRoot && record.outcome === 'completed') fs.rmSync(environmentRoot,{recursive:true,force:true});
    record.state = record.outcome === 'completed' ? 'finished' : 'running'; record.finishedAt = record.state === 'finished' ? Date.now() : null;
    record.reason = result.reason == null ? (result.exitCode ? `Test suite exited with status ${result.exitCode}.` : null) : safeEvidenceText(result.reason);
    save();
    // Disconnect only after the terminal write clears earlier queued output.
    await new Promise(done => send({result:{...result,record}},done));
  } catch (error) {
    // No terminal message may claim a receipt that was not saved.
    process.exitCode = 1;
  } finally {
    if (process.connected) process.disconnect();
  }
});
