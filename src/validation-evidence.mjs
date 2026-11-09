// Owned by prompts/cli/test-suite-queue.prompt.md.
import {StringDecoder} from 'node:string_decoder';
import {redactSecrets} from './secret-redaction.mjs';

export const MAX_VALIDATION_LOG_BYTES = 1048576;
export const MAX_VALIDATION_RECEIPT_BYTES = 65536;
export const MAX_RECEIPT_TEXT_BYTES = 4096;
export const MAX_EVIDENCE_LINE_BYTES = 262144;
const marker = n => `\n[${n} bytes omitted]\n`;
const quoteEnd = (text, start, quote) => {
  for(let index=start;index<text.length;index++) {
    if(text[index]==='\\') index++;
    else if(text[index]===quote) return index;
  }
  return -1;
};
const clip = (text, limit) => {
  const bytes = Buffer.from(text);
  if (bytes.length <= limit) return text;
  const end = limit - 128;
  // A partial final UTF-8 character can expand to three encoded bytes.
  return bytes.subarray(0,end).toString('utf8') + marker(bytes.length-end);
};
export const safeEvidenceText = value => clip(redactSecrets(value),MAX_RECEIPT_TEXT_BYTES);

export function serializeValidationReceipt(record) {
  const scrub = (value, key) => {
    if (typeof value === 'string') return ['reason','error','runId','issue'].includes(key)
      ? safeEvidenceText(value) : redactSecrets(value);
    if (Array.isArray(value)) return value.map(item=>scrub(item));
    if (value && typeof value === 'object') return Object.fromEntries(Object.entries(value).map(([k,v])=>[k,scrub(v,k)]));
    return value;
  };
  const text = JSON.stringify(scrub(record));
  if (Buffer.byteLength(text) > MAX_VALIDATION_RECEIPT_BYTES) throw Object.assign(
    Error('Validation receipt metadata exceeds its byte budget.'),{code:'VALIDATION_RECEIPT_BUDGET'});
  return text;
}

// Hold whole lines across transport chunks. Oversized lines fail closed rather
// than expose a credential whose terminator has not arrived yet.
export function redactingLines(emit) {
  const decoder = new StringDecoder('utf8');
  let pending = [], length = 0, oversized = false, privateKey = false, quotedSecret = null;
  const line = ended => {
    if (oversized) emit(marker(length),length);
    else {
      const text = decoder.write(Buffer.concat(pending));
      if (quotedSecret) {
        if (quoteEnd(text,0,quotedSecret)>=0) quotedSecret = null;
        emit(`[redacted]${ended?'\n':''}`,0);
      } else if (privateKey || /-----BEGIN [^-]*PRIVATE KEY-----/.test(text)) {
        privateKey = !/-----END [^-]*PRIVATE KEY-----/.test(text);
        emit(`[redacted]${ended?'\n':''}`,0);
      } else {
        // A quoted secret may continue over a newline. Suppress subsequent
        // lines until its closing quote, even if they have no secret prefix.
        for (const match of text.matchAll(/\b(?:key|token|password|secret|api[_-]?key|authorization|cookie|credential)["']?\s*[:=]\s*(["'])/gi)) {
          if (quoteEnd(text,match.index+match[0].length,match[1])<0) quotedSecret = match[1];
        }
        emit(redactSecrets(text),0);
      }
    }
    pending = []; length = 0; oversized = false;
  };
  return {
    write(bytes) {
      let start = 0;
      while (start < bytes.length) {
        const newline = bytes.indexOf(10,start), end = newline < 0 ? bytes.length : newline+1;
        const part = bytes.subarray(start,end); length += part.length;
        if (length > MAX_EVIDENCE_LINE_BYTES) { oversized = true; pending = []; }
        else if (!oversized) pending.push(Buffer.from(part));
        if (newline >= 0) line(true);
        start = end;
      }
    },
    end() { if (length) line(false); const rest=decoder.end(); if(rest) emit(redactSecrets(rest),0); },
  };
}

export function validationLog(write, append) {
  const partBytes = (MAX_VALIDATION_LOG_BYTES - 128) / 2;
  let head = Buffer.alloc(0), tail = Buffer.alloc(0), total = 0, suppressed = 0, overflow = false;
  const evidence = {outputBytes:0,logBytes:0,omittedBytes:0,truncated:false};
  return {
    evidence,
    add(text, omitted = 0) {
      const bytes = Buffer.from(text); total += bytes.length; suppressed += omitted;
      // Keep two bounded ends even before overflow, for the next append.
      if (head.length < partBytes) head = Buffer.concat([head,bytes.subarray(0,partBytes-head.length)]);
      tail = Buffer.concat([tail,bytes]).subarray(-partBytes);
      let saved;
      if (!overflow && total <= MAX_VALIDATION_LOG_BYTES) { append(bytes); evidence.logBytes = total; }
      else {
        overflow = true;
        saved = Buffer.concat([head,Buffer.from(marker(total-head.length-tail.length)),tail]);
        write(saved); evidence.logBytes = saved.length;
      }
      evidence.omittedBytes = suppressed + (overflow ? total-head.length-tail.length : 0);
      evidence.truncated = evidence.omittedBytes > 0;
    },
  };
}
