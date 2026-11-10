// Synthetic public-intake consumer. No AI, GitHub or runtime service is called.
import { fixture, repository, key } from './issue-sort-fixture.mjs';
import { prepareDependencyIntake, completeDependencyIntake } from '../../src/issue-dependencies-intake.mjs';
export { repository, key };
const reply = value => ({ json: JSON.stringify(value) });
export function reviewWorld(count = 40) {
  const w = fixture(Array.from({ length: count }, (_, i) => i + 1), { context: { areas: [{ name: 'cli', owner: 'autopilot', match: { paths: ['src/**'] } }] } });
  w.counts = { ai: 0, github: 0, bytes: 0, maxBytes: 0 };
  for (const [name, fn] of Object.entries(w.ports.github)) w.ports.github[name] = async (...args) => { w.counts.github++; return fn(...args); };
  w.files.set(`https://github.com/${repository}/blob/HEAD/src/cli.mjs`, 'source-v1');
  w.background = `https://github.com/${repository}/blob/HEAD/src/background.mjs`;
  w.files.set(w.background, 'background-v1');
  w.ports.evidence = { read: async ({ issues }) => reply({ source: issues.flatMap(subject => {
    const raw = w.issues.find(i => i.html_url === subject);
    return [...w.files].filter(([key]) => raw.body.includes(key.split('/').pop())).map(([key, revision]) => ({ key, revision, path: key.split('/HEAD/')[1], text: 'synthetic source', issues: [subject] }));
  }), requirements: [] }) };
  w.resetCounts = () => { w.counts = { ai: 0, github: 0, bytes: 0, maxBytes: 0 }; };
  return w;
}
export function analysisFor(w, request, { background = false } = {}) {
  const snapshot = JSON.parse(request.snapshotJson), context = JSON.parse(request.contextJson);
  const row = ({ key, revision }) => ({ key, revision });
  const reviews = request.issues.map(issue => ({ analysis: 'Synthetic dependency assessment.', base: snapshot.reviews.filter(r => r.issue === issue && !snapshot.reviews.some(other => other.base.includes(r.id))).map(r => r.id), continuation: '', issue,
    inputs: [...new Map([row(snapshot.issues.find(i => i.key === issue)), ...(context.source ?? []).filter(x => x.issues.includes(issue)).map(row),
      ...(snapshot.issues.find(i => i.key === issue)?.namedSources ?? []).map(key => row(snapshot.inputs.find(x => x.key === key))),
      ...snapshot.inputs.filter(x => x.key.startsWith(`${issue}#issuecomment-`)), ...(background ? [{ key: w.background, revision: w.files.get(w.background) }] : [])].map(r => [r.key, r])).values()],
    candidates: snapshot.issues.filter(i => i.key.startsWith(`https://github.com/${repository}/issues/`)).map(row), outcome: 'complete', dependencies: [], questions: [], effects: 'none' }));
  const sorts = request.issues.map(issue => {
    const current = context.sort.records.find(r => r.issue === issue); if (current) return current;
    const subject = snapshot.issues.find(i => i.key === issue), old = subject.sorts ?? [];
    const r = w.record(Number(issue.split('/').pop()), { base: old.filter(x => !old.some(y => y.record?.base.includes(x.id))).map(x => x.id), rootCause: `cause-${issue.split('/').pop()}` });
    r.inputs = r.inputs.map(x => x.key === context.sort.key ? { key: x.key, revision: context.sort.revision } : x);
    r.inputs.push(...snapshot.inputs.filter(x => x.key.startsWith(`${issue}#issuecomment-`)));
    return r;
  });
  return { reviews, sorts, impactJson: '' };
}
export async function reviewOnce(w, options = {}) {
  const { request, queued } = await prepareDependencyIntake({ repository }, w.ports);
  if (!queued.length) return { request, queued };
  w.counts.ai++;
  const bytes = Buffer.byteLength(JSON.stringify(request)); w.counts.bytes += bytes; w.counts.maxBytes = Math.max(w.counts.maxBytes, bytes);
  const analysis = analysisFor(w, request, options);
  const result = await completeDependencyIntake({ request, analysis }, w.ports);
  return { request, queued, result };
}
export async function reviewAll(w, options = {}) {
  for (let i = 0; i < w.issues.length + 1; i++) {
    const r = await reviewOnce(w, options);
    if (!r.queued.length) return;
    if (r.result.state !== 'complete') throw Error(`Synthetic completion failed: ${JSON.stringify(r.result)}`);
  }
  throw Error('Synthetic backlog did not converge');
}
