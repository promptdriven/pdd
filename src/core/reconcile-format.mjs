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

export function formatBatchReconciliation(record) {
  if (!record || typeof record !== 'object' || Array.isArray(record)) {
    return 'Batch reconciliation: unavailable (malformed response).';
  }
  const batch = cleanText(record.batch || 'unknown', 64);
  const rows = Array.isArray(record.rows) ? record.rows : [];
  if (!rows.length && record.status === 'already-resolved') {
    return `Batch ${batch}: no unresolved prior reservations remain.`;
  }
  const parts = [];
  if (Number.isSafeInteger(record.settled_count) && record.settled_count > 0) parts.push(`${record.settled_count} settled`);
  if (Number.isSafeInteger(record.terminated_count) && record.terminated_count > 0) parts.push(`${record.terminated_count} terminated`);
  if (Number.isSafeInteger(record.expired_count) && record.expired_count > 0) parts.push(`${record.expired_count} expired`);
  const breakdown = parts.length ? ` (${parts.join(', ')})` : '';
  const cleared = Number.isSafeInteger(record.cleared_count) ? record.cleared_count : 0;
  const remaining = Number.isSafeInteger(record.remaining_unresolved_count) ? record.remaining_unresolved_count : 0;
  const lines = [
    `Reconciled batch ${batch}: ${cleared} cleared${breakdown}, ${remaining} remaining unresolved.`,
  ];
  for (const row of rows) {
    if (!row || typeof row !== 'object') continue;
    const testName = cleanText(row.test ?? '-', 160);
    const status = cleanText(row.status ?? 'unknown', 64);
    const calls = row.calls === 'unknown' || row.calls === undefined || row.calls === null
      ? 'unknown'
      : Number.isSafeInteger(row.calls) && row.calls >= 0
        ? String(row.calls)
        : cleanText(row.calls, 32);
    const reason = cleanText(row.reason ?? '', 240);
    lines.push(`  ${testName}: ${status} (calls: ${calls}; cleared: ${row.cleared ? 'yes' : 'no'})${reason ? ` — ${reason}` : ''}`);
  }
  return lines.join('\n');
}

export function formatStaleReconciliation(record) {
  if (!record || typeof record !== 'object' || Array.isArray(record)) {
    return 'Stale reservation reconciliation: unavailable (malformed response).';
  }
  const batches = Array.isArray(record.batches) ? record.batches : [];
  const inspected = Number.isSafeInteger(record.batches_inspected) ? record.batches_inspected : batches.length;
  if (inspected === 0) {
    return 'No unresolved prior reservations found for this repository.';
  }
  const cleared = Number.isSafeInteger(record.cleared_count) ? record.cleared_count : 0;
  const remaining = Number.isSafeInteger(record.remaining_unresolved_count) ? record.remaining_unresolved_count : 0;
  const lines = [
    `Reconciled ${inspected} prior batch${inspected === 1 ? '' : 'es'}: ${cleared} reservation${cleared === 1 ? '' : 's'} cleared, ${remaining} remaining unresolved.`,
  ];
  for (const batch of batches) {
    if (!batch || typeof batch !== 'object') continue;
    const batchId = cleanText(batch.batch ?? 'unknown', 64);
    const status = cleanText(batch.status ?? 'unknown', 64);
    if (batch.reason) {
      lines.push(`  ${batchId}: ${status} — ${cleanText(batch.reason, 240)}`);
    } else {
      const bCleared = Number.isSafeInteger(batch.cleared_count) ? batch.cleared_count : 0;
      const bRem = Number.isSafeInteger(batch.remaining_unresolved_count) ? batch.remaining_unresolved_count : 0;
      lines.push(`  ${batchId}: ${status} (${bCleared} cleared, ${bRem} remaining)`);
    }
  }
  return lines.join('\n');
}
