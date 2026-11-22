// Layer-1 read-only formatter for CHECK receipt reconciliation responses.
const cleanText = (value, max = 240) =>
  String(value ?? '')
    .replace(/[\u0000-\u001f\u007f-\u009f]+/g, ' ')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, max);

export function formatCheckReconciliation(record) {
  if (!record || typeof record !== 'object' || Array.isArray(record)) {
    return 'CHECK reconciliation: unavailable (malformed response).';
  }
  const reqId = cleanText(record.request_id || 'unknown', 64);
  const httpStatus = Number.isSafeInteger(record.http_status) ? record.http_status : 0;
  const disp = record.disposition && typeof record.disposition === 'object' ? record.disposition : {};
  const dispatch = record.dispatch && typeof record.dispatch === 'object' ? record.dispatch : {};
  const acct = record.accounting && typeof record.accounting === 'object' ? record.accounting : {};
  const retry = record.retry && typeof record.retry === 'object' ? record.retry : {};
  const ev = record.evidence && typeof record.evidence === 'object' ? record.evidence : {};
  const prov = record.provenance && typeof record.provenance === 'object' ? record.provenance : {};

  const lines = [`CHECK reconciliation ${reqId} (read-only; HTTP ${httpStatus})`];
  const dispParts = [`state=${cleanText(disp.state ?? 'unknown', 64)}`];
  if (disp.verdict && disp.verdict !== disp.state) dispParts.push(`verdict=${cleanText(disp.verdict, 64)}`);
  if (disp.refusal_code) dispParts.push(`refusal=${cleanText(disp.refusal_code, 96)}`);
  if (disp.expired === true) dispParts.push('expired=yes');
  if (disp.purged === true) dispParts.push('purged=yes');
  lines.push(`Disposition: ${dispParts.join(', ')}`);

  lines.push(`Dispatch: ${cleanText(dispatch.status ?? 'unproved', 64)} (${dispatch.proven === true ? 'proven' : 'unproved'})`);

  const fmtCount = value =>
    value === 'unknown' || value === undefined || value === null
      ? 'unknown'
      : Number.isSafeInteger(value) && value >= 0
        ? String(value)
        : cleanText(value, 32);
  const acctParts = [
    `complete=${acct.accounting_complete === true ? 'yes' : 'no'}`,
    `calls=${fmtCount(acct.calls)}`,
    `known=${fmtCount(acct.known_calls)}`,
    `unknown=${fmtCount(acct.unknown_calls)}`,
  ];
  if (Number.isSafeInteger(acct.cap)) acctParts.push(`cap=${acct.cap}`);
  lines.push(`Accounting: ${cleanText(acct.status ?? 'unknown', 64)} (${acctParts.join(', ')})`);

  lines.push(`Retry blocked: ${retry.blocked === false ? 'no' : 'yes'}`);
  if (retry.safe_next_action) lines.push(`Next: ${cleanText(retry.safe_next_action, 512)}`);
  if (record.error_code) lines.push(`Error: ${cleanText(record.error_code, 96)}`);
  if (Array.isArray(ev.proof_basis) && ev.proof_basis.length) {
    lines.push(`Proof basis: ${ev.proof_basis.map(item => cleanText(item, 96)).join(', ')}`);
  }
  if (Array.isArray(ev.contradictions) && ev.contradictions.length) {
    lines.push(`Contradictions: ${ev.contradictions.map(item => cleanText(item, 96)).join(', ')}`);
  }
  const provParts = [];
  if (prov.source_sha256) provParts.push(`source=${cleanText(prov.source_sha256, 64).slice(0, 12)}`);
  if (prov.engine_sha) provParts.push(`engine=${cleanText(prov.engine_sha, 64).slice(0, 12)}`);
  if (prov.server_commit) provParts.push(`server=${cleanText(prov.server_commit, 64).slice(0, 12)}`);
  if (Array.isArray(prov.sources_consulted) && prov.sources_consulted.length) {
    provParts.push(`sources=${prov.sources_consulted.map(item => cleanText(item, 64)).join(',')}`);
  }
  if (provParts.length) lines.push(`Provenance: ${provParts.join(', ')}`);
  return lines.join('\n');
}
