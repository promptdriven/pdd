// Owned by prompts/cli/secret-redaction.prompt.md.
const SECRET = /token|password|secret|api[_-]?key|authorization|cookie|credential/i;
export function redactSecrets(value, secrets = []) {
  value = String(value ?? '');
  for(const secret of secrets)if(typeof secret==='string'&&secret)value=value.split(secret).join('[redacted]');
  value=value.replace(/https?:\/\/[^\s"'<>]+/g,text=>{try{const url=new URL(text);let changed=false;if(url.username||url.password){url.username='';url.password='';changed=true;}for(const key of [...url.searchParams.keys()])if(SECRET.test(key)||/^(?:key|auth|signature)$/i.test(key)){url.searchParams.set(key,'[redacted]');changed=true;}return changed?url.href:text;}catch{return text.replace(/(https?:\/\/)[^\s/@]+(?::[^\s/@]*)?@/gi,'$1[redacted]@');}});
  value = value.replace(/-----BEGIN [^-]*PRIVATE KEY-----[\s\S]*?(?:-----END [^-]*PRIVATE KEY-----|$)/g,'[redacted]');
  value = value.replace(/\b(authorization)["']?\s*[:=]\s*[^\r\n]+/gi, '$1=[redacted]');
  return value.replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,}|AIza[A-Za-z0-9_-]+|ya29\.[A-Za-z0-9_.-]+)\b/g,'[redacted]').replace(/\b(?:Bearer|Basic)\s+\S+/gi,'[redacted]').replace(/\b(key|token|password|secret|api[_-]?key|authorization|cookie|credential)["']?\s*[:=]\s*(?:"(?:\\.|[^"\\])*(?:"|$)|'(?:\\.|[^'\\])*(?:'|$)|[^\s,;]+)/gi,'$1=[redacted]').replace(/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g,'');
}
