// Generated from prompts/cli/issue-dependencies-events.prompt.md (sha256: bf88de2d704a5cac15d91cef02a553076281acd94441adce599ec745d6850a9a).
import { createHmac, timingSafeEqual } from 'node:crypto';

export function dependencyEventStatus({ configured = false, installed = false, verified = false, error = '' } = {}) {
  return { state: !configured ? 'disabled' : error ? 'degraded' : installed && verified ? 'active' : 'configured', configured, installed, verified };
}

export async function acceptDependencyEvent({ repository, delivery, event, body, signature }, ports = {}) {
  const verify = ports.signature?.verify ?? (async ({ body, signature }) => {
    const secret = ports.secret;
    if (!secret || !/^sha256=[0-9a-f]{64}$/i.test(signature)) return { valid: false };
    const expected = createHmac('sha256', secret).update(body).digest();
    const supplied = Buffer.from(signature.slice(7), 'hex');
    return { valid: supplied.length === expected.length && timingSafeEqual(expected, supplied) };
  });
  try {
    if (!(await verify({ body, signature })).valid) return { accepted: false, reason: 'signature' };
    if (!['issues', 'issue_dependencies', 'issue_comment', 'pull_request'].includes(event)) return { accepted: false, reason: 'unsupported' };
    const payload = JSON.parse(body);
    const origin = payload.repository?.full_name;
    if (typeof origin !== 'string') return { accepted: false, reason: 'scope' };
    if (origin.toLowerCase() !== repository.toLowerCase()) {
      const scope = await ports.scope.read({ repository });
      const keys = [payload.issue?.html_url, payload.blocked_issue?.html_url, payload.blocking_issue?.html_url, payload.pull_request?.issue_url, payload.pull_request?.html_url].filter(Boolean).map(x => x.replace(/^https:\/\/api\.github\.com\/repos\/(.+)\/issues\/(\d+)$/, 'https://github.com/$1/issues/$2'));
      if (!keys.some(key => scope.issues.some(x => x.toLowerCase() === key.toLowerCase()))) return { accepted: false, reason: 'scope' };
    }
    const existing = JSON.parse((await ports.events.read({ repository })).json || '{}');
    const delivered = Array.isArray(existing.seen) ? existing.seen : [];
    if (delivered.includes(delivery)) return { accepted: false, reason: 'duplicate' };
    const pending = [...new Set([...(existing.pending || []), delivery])];
    if (!(await ports.events.save({ repository, json: JSON.stringify({ ...existing, seen: delivered, pending }) })).ok) return { accepted: false, reason: 'pending' };
    if (!(await ports.reconcile.hint({ repository, delivery })).ok) return { accepted: false, reason: 'pending' };
    const saved = await ports.events.save({ repository, json: JSON.stringify({ ...existing, seen: [...delivered, delivery].slice(-1000), pending: pending.filter(x => x !== delivery) }) });
    return saved.ok ? { accepted: true, reason: 'queued' } : { accepted: false, reason: 'pending' };
  } catch { return { accepted: false, reason: 'pending' }; }
}
