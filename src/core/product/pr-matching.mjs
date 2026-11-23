// Generated from prompts/cli/product.prompt.md.
// Layer 1 core: canonical GitHub URL validation, planned-run markers, PR eligibility, and stage completion matching (ZERO legacy workflow imports).
import { sameRepo } from '../../shared/github-repo.mjs';
import { invalid } from './markdown-utils.mjs';

const THROUGH = ['prompt-pr', 'code'];
const PAGE_SIZE = 10;
const PRODUCT_LINE_RE = /^<!-- pdd-product: run=([^\s\r\n]+?)(?: stage=(prompt-pr|prompt|code))? -->$/;
const PRODUCT_TOKEN_RE = /<!-- pdd-product: run=[^\r\n]+? -->/g;

export const productPrefix = '<!-- pdd-product: run=';
export const marker = run => `<!-- pdd-product: run=${run} -->`;

export function canonicalGithubUrl(value, repository, kind, number) {
  const match = typeof value === 'string' && /^https:\/\/github\.com\/([^/]+\/[^/]+)\/(issues|pull)\/([1-9][0-9]*)$/.exec(value);
  const n = match ? Number(match[3]) : 0;
  if (!Number.isSafeInteger(n) || n <= 0 || !sameRepo(match[1], repository) || match[2] !== kind) return 0;
  try {
    const url = new URL(value);
    const found = url.host === 'github.com' && !url.search && !url.hash && url.pathname === `/${match[1]}/${kind}/${match[3]}` ? n : 0;
    return number === undefined || found === number ? found : 0;
  } catch { return 0; }
}

export function ownProductMarker(body, run) {
  const tokens = String(body ?? '').match(PRODUCT_TOKEN_RE) ?? [];
  if (!tokens.length) return false;
  for (const token of tokens) {
    const match = PRODUCT_LINE_RE.exec(token);
    if (!match || match[1] !== run) return false;
  }
  return String(body).split(/\r?\n/).some(line => {
    const match = PRODUCT_LINE_RE.exec(line);
    return Boolean(match && match[1] === run);
  });
}

export function foreignProductMarkerOnly(body, run) {
  const tokens = String(body ?? '').match(PRODUCT_TOKEN_RE) ?? [];
  return tokens.length > 0 && !String(body).split(/\r?\n/).some(line => {
    const match = PRODUCT_LINE_RE.exec(line);
    return Boolean(match && match[1] === run);
  });
}

function stripCodeForClosingScan(body) {
  const lines = String(body ?? '').split(/\r?\n/), out = [];
  let fence = null;
  for (const line of lines) {
    const m = /^ {0,3}(`{3,}|~{3,})/.exec(line);
    if (m) {
      if (!fence) fence = m[1];
      else if (m[1][0] === fence[0] && m[1].length >= fence.length) fence = null;
      continue;
    }
    if (!fence) out.push(line.replace(/`[^`\r\n]*`/g, ' '));
  }
  return out.join('\n');
}

export function closesIssueReference(body, issueNumber) {
  if (!Number.isSafeInteger(issueNumber) || issueNumber < 1) return false;
  const text = stripCodeForClosingScan(body);
  return new RegExp(`(?:^|[\\s(])(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?):?[ \\t]+#${issueNumber}(?![0-9])`, 'im').test(text);
}

export function sameRepoPr(pr, number, repository) {
  if (!pr || pr.number !== number || typeof pr.body !== 'string' || !['OPEN', 'MERGED', 'CLOSED'].includes(pr.state)
    || !canonicalGithubUrl(pr.url, repository, 'pull', number)) return false;
  const [owner, name] = repository.split('/');
  const headOwner = pr.headRepositoryOwner?.login, headName = pr.headRepository?.name;
  if (pr.isCrossRepository === true || (typeof headOwner === 'string' && !sameRepo(headOwner, owner))
    || (typeof headName === 'string' && !sameRepo(headName, name))) return false;
  return Boolean(pr.isCrossRepository === false || (sameRepo(headOwner, owner) && sameRepo(headName, name)));
}

export function eligiblePr(pr, number, repository, run, local, warning, issueNumber) {
  const reject = () => {
    if (typeof pr?.body === 'string' && pr.body.split(/\r?\n/).some(line => { const m = PRODUCT_LINE_RE.exec(line); return Boolean(m && m[1] === run); })) {
      warning.push(`Warning: PR #${number} could not be verified as ${run}'s PR.`);
    }
    return false;
  };
  if (!sameRepoPr(pr, number, repository)) return reject();
  const branches = [local?.branch, ...(local?.pr ?? []).map(saved => saved.branch)].filter(branch => typeof branch === 'string');
  return ownProductMarker(pr.body, run)
    || branches.includes(pr.headRefName)
    || (closesIssueReference(pr.body, issueNumber) && !foreignProductMarkerOnly(pr.body, run))
    || reject();
}

export async function pullRequests(p, cwd, repository, issue, local, run, warning) {
  const numbers = new Set((local?.pr ?? []).map(pr => pr.number).filter(number => Number.isSafeInteger(number) && number > 0));
  for (let page = 1; ; page++) {
    const events = await p.timelinePage({ cwd, repository, issue: issue.number, page, perPage: PAGE_SIZE });
    if (!Array.isArray(events) || events.length > PAGE_SIZE) invalid(`GitHub returned an invalid timeline for issue #${issue.number}.`);
    for (const event of events) {
      if (event?.event !== 'cross-referenced') continue;
      const number = canonicalGithubUrl(event.source?.issue?.pull_request?.html_url, repository, 'pull');
      if (number) numbers.add(number);
    }
    if (events.length < PAGE_SIZE) break;
  }
  const prs = [];
  let hasMergedSameRepoPr = false;
  for (const number of numbers) {
    const pr = await p.pullRequest({ cwd, repository, number });
    const eligible = eligiblePr(pr, number, repository, run, local, warning, issue.number);
    if (eligible) prs.push(pr);
    if (pr?.state === 'MERGED' && (eligible || (sameRepoPr(pr, number, repository) && !foreignProductMarkerOnly(pr.body, run)))) {
      hasMergedSameRepoPr = true;
    }
  }
  return { prs, hasMergedSameRepoPr };
}

export const validThrough = value => {
  if (value === undefined) return undefined;
  if (!THROUGH.includes(value)) invalid('Use --through prompt-pr or --through code.');
  return value;
};

export const validBase = value => {
  if (value === undefined) return undefined;
  if (
    typeof value !== 'string' || !value || /[\x00-\x1f\x7f\s~^:?*[\\]/.test(value)
    || value === 'HEAD' || value === '@' || value.startsWith('-') || value.startsWith('refs/')
    || value.startsWith('/') || value.endsWith('/') || value.endsWith('.') || value.includes('..')
    || value.includes('@{') || value.includes('//')
    || value.split('/').some(seg => !seg || seg.startsWith('.') || seg.endsWith('.lock'))
  ) invalid('Use --base with a branch name, for example feature/checkout.');
  return value;
};

const localStageMatch = (pr, local, stages) => Boolean(local?.pr?.some(saved => saved.number === pr.number
  && stages.includes(saved.stage) && typeof saved.branch === 'string' && saved.branch === pr.headRefName));

function productStageMatch(body, run, stages) {
  const stageLines = String(body ?? '').split(/\r?\n/).map(line => PRODUCT_LINE_RE.exec(line)).filter(m => m && m[2]);
  if (stageLines.length !== 1) return false;
  const [, foundRun, foundStage] = stageLines[0];
  return foundRun === run && stages.includes(foundStage) && ownProductMarker(body, run);
}

const legacyWorkflowStageMatch = (body, stages) => (body.match(/pdd-workflow:/g) ?? []).length === 1
  && (body.match(/pdd-workflow:[A-Za-z0-9_.-]+:[A-Za-z0-9_.-]+/g) ?? []).length === 1
  && body.split(/\r?\n/).filter(line => {
    const match = /^<!-- pdd-workflow:[A-Za-z0-9_.-]+:([A-Za-z0-9_.-]+) -->$/.exec(line);
    return Boolean(match && stages.includes(match[1]));
  }).length === 1;

const isExplicitPromptOnlyPr = (pr, local, run) => (localStageMatch(pr, local, ['prompt-pr', 'prompt']) && !localStageMatch(pr, local, ['code']))
  || productStageMatch(pr.body, run, ['prompt-pr', 'prompt'])
  || legacyWorkflowStageMatch(pr.body, ['prompt-pr', 'prompt']);

export function stagePr(pr, local, stages, run, issueNumber) {
  if (localStageMatch(pr, local, stages)) return true;
  if (productStageMatch(pr.body, run, stages)) return true;
  if (legacyWorkflowStageMatch(pr.body, stages)) return true;
  if (stages.includes('code') && closesIssueReference(pr.body, issueNumber)
    && !foreignProductMarkerOnly(pr.body, run) && !isExplicitPromptOnlyPr(pr, local, run)) {
    return true;
  }
  return false;
}

export const completedPr = (pr, local, target, run, issueNumber) => target === 'prompt-pr'
  ? stagePr(pr, local, ['prompt-pr', 'prompt'], run, issueNumber) || stagePr(pr, local, ['code'], run, issueNumber)
  : stagePr(pr, local, ['code'], run, issueNumber);
