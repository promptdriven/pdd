// Owned by prompts/cli/test-suite-queue.prompt.md.
import {StringDecoder} from 'node:string_decoder';
import {redactSecrets} from './secret-redaction.mjs';

export const MAX_VALIDATION_LOG_BYTES = 1048576;
export const MAX_VALIDATION_RECEIPT_BYTES = 65536;
export const MAX_RECEIPT_TEXT_BYTES = 4096;
export const MAX_EVIDENCE_LINE_BYTES = 262144;
const marker = n => `\n[${n} bytes omitted]\n`;
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

// Recognition has constant space, separate from the bounded retained line.
// In particular, long whitespace in an assignment or PEM label cannot erase
// its opener when a window or the retained line ends.
function multilineSecrets() {
  let tail='', field=null, quote=null, escaped=false, privateKey=false;
  let header=null, label='', dashes=0, suppressed=false, continuedField=false;
  return {
    write(text) {
      for(const char of text) {
        tail=(tail+char).slice(-32);
        if(header) {
          if(char==='-') {
            if(!dashes && !label.endsWith('PRIVATE KEY')) header=null;
            else if(++dashes===5) {
              privateKey=header==='BEGIN';header=null;field=null;suppressed=true;
            }
          } else if(dashes) header=null;
          else label=(label+char).slice(-11);
        }
        if(char===' ' && /-----BEGIN $|-----END $/.test(tail)) {
          header=tail.endsWith('BEGIN ')?'BEGIN':'END';label='';dashes=0;
        }
        if(quote) {
          if(escaped) escaped=false;
          else if(char==='\\') escaped=true;
          else if(char===quote) quote=null;
        } else if(!privateKey) {
          if(field==='separator') {
            // A value on a later line has no local field name for the shared
            // string redactor. Suppress it before this line can be emitted.
            if(continuedField && !/\s/.test(char)) suppressed=true;
            if(char==='"'||char==="'") {quote=char;field=null;}
            else if(!/\s/.test(char)) field='value';
          } else if(field==='value') {
            if(/[\s,;]/.test(char)) field=null;
          } else if(field) {
            if(char===':'||char==='=') field='separator';
            else if(field==='name'&&(char==='"'||char==="'")) field='space';
            else if(!/\s/.test(char)) field=null;
          }
          if(!quote && /[\s:="']/.test(char) &&
            /\b(?:key|token|password|secret|api[_-]?key|authorization|cookie|credential)$/i.test(tail.slice(0,-1))) {
            field=char===':'||char==='='?'separator':char==='"'||char==="'"?'space':'name';
          }
        }
      }
    },
    finishLine() {
      const redact=suppressed||Boolean(header);
      suppressed=Boolean(quote||privateKey||header);
      // Whitespace, including LF and discarded oversized lines, can separate
      // a recognized field from its separator and its value. Keep only this
      // bounded recognition state, never the raw assignment or secret body.
      continuedField=Boolean(field);tail='';
      return redact;
    },
  };
}

// Hold whole lines across transport chunks. Scan discarded bytes too, without
// retaining their raw contents or losing multiline suppression state.
export function redactingLines(emit) {
  const decoder = new StringDecoder('utf8');
  const secrets=multilineSecrets();
  let pending = [], length = 0, oversized = false;
  const line = ended => {
    const suppressed=secrets.finishLine();
    if (oversized) emit(marker(length),length);
    else if(suppressed) emit(`[redacted]${ended?'\n':''}`,0);
    else emit(redactSecrets(Buffer.concat(pending).toString('utf8')),0);
    pending = []; length = 0; oversized = false;
  };
  return {
    write(bytes) {
      let start = 0;
      while (start < bytes.length) {
        const newline = bytes.indexOf(10,start), end = newline < 0 ? bytes.length : newline+1;
        for(let offset=start;offset<end;offset+=4096) {
          const part=bytes.subarray(offset,Math.min(offset+4096,end));
          secrets.write(decoder.write(part));length+=part.length;
          if (length > MAX_EVIDENCE_LINE_BYTES) { oversized = true; pending = []; }
          else if (!oversized) pending.push(Buffer.from(part));
        }
        if (newline >= 0) line(true);
        start = end;
      }
    },
    end() { secrets.write(decoder.end());if (length) line(false); },
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
