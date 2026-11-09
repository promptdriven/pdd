// Owned by prompts/cli/secret-redaction.prompt.md.
const SECRET = /token|password|secret|api[_-]?key|authorization|cookie|credential/i;
const remembered = new Set();
const secretName = /token|secret|password|passwd|credential|authorization|cookie|api[_-]?key|_key$/i;
export function rememberSecrets(...values) {
  for (const value of values) if (typeof value === 'string' && value) remembered.add(value);
}
export function knownSecretValues(env = process.env, secrets = []) {
  return [...new Set([...remembered, ...secrets,
    ...[process.env, env].flatMap(source => Object.entries(source ?? {})
      .filter(([name,value]) => secretName.test(name) && typeof value === 'string' && value)
      .map(([,value]) => value))])].filter(value => typeof value === 'string' && value);
}

// Keep undecided raw text only for the longest possible match. The second
// callback argument lets evidence consumers count original bytes and lines.
export function redactingValues(emit, secrets) {
  const values = [...new Set(secrets)].filter(value => typeof value === 'string' && value);
  const overlap = Math.max(0, ...values.map(value => value.length - 1));
  let pending = '';
  const drain = final => {
    const limit = final ? pending.length : Math.max(0, pending.length - overlap);
    let offset = 0;
    while (offset < limit) {
      let start = -1, matched = '';
      for (const value of values) {
        const index = pending.indexOf(value, offset);
        if (index >= 0 && (start < 0 || index < start || index === start && value.length > matched.length)) {
          start = index; matched = value;
        }
      }
      if (start < 0 || start >= limit) break;
      if (start > offset) emit(pending.slice(offset,start), pending.slice(offset,start));
      emit('[redacted]', matched);
      offset = start + matched.length;
    }
    if (offset < limit) { emit(pending.slice(offset,limit), pending.slice(offset,limit)); offset = limit; }
    pending = pending.slice(offset);
  };
  return {write(text) { pending += text; drain(false); }, end() { drain(true); }};
}

export function redactSecrets(value, secrets = []) {
  let redacted = '';
  const stream = redactingValues(text => { redacted += text; }, knownSecretValues(process.env,secrets));
  stream.write(String(value ?? '')); stream.end();
  value = redacted;
  value=value.replace(/https?:\/\/[^\s"'<>]+/g,text=>{try{const url=new URL(text);let changed=false;if(url.username||url.password){url.username='';url.password='';changed=true;}for(const key of [...url.searchParams.keys()])if(SECRET.test(key)||/^(?:key|auth|signature)$/i.test(key)){url.searchParams.set(key,'[redacted]');changed=true;}return changed?url.href:text;}catch{return text.replace(/(https?:\/\/)[^\s/@]+(?::[^\s/@]*)?@/gi,'$1[redacted]@');}});
  value = value.replace(/-----BEGIN [^-]*PRIVATE KEY-----[\s\S]*?(?:-----END [^-]*PRIVATE KEY-----|$)/g,'[redacted]');
  value = value.replace(/\b(authorization)["']?\s*[:=]\s*[^\r\n]+/gi, '$1=[redacted]');
  return value.replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,}|AIza[A-Za-z0-9_-]+|ya29\.[A-Za-z0-9_.-]+)\b/g,'[redacted]').replace(/\b(?:Bearer|Basic)\s+\S+/gi,'[redacted]').replace(/\b(key|token|password|secret|api[_-]?key|authorization|cookie|credential)["']?\s*[:=]\s*(?:"(?:\\.|[^"\\])*(?:"|$)|'(?:\\.|[^'\\])*(?:'|$)|[^\s,;]+)/gi,'$1=[redacted]').replace(/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g,'');
}
