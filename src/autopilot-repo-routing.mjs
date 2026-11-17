// Generated from prompts/cli/autopilot-repo-routing.prompt.md.
const PDD_REPO = 'promptdriven/pdd';
const PDD_ALIASES = ['pdd', 'prompt-runtime', 'runtime-client', 'pdd_cloud'];
const ROUTING_LABEL = 'pdd:elsewhere';
const NO_ROUTE = Object.freeze({ targetRepository: null, label: null });
const SLUG = /^[a-z0-9_.-]+\/[a-z0-9_.-]+$/;
const TITLE_TARGET = /^\[([^\]\n]+)\]|^((?:https:\/\/github\.com\/)?[\w./-]+)\s*:/i;
const TARGET_FIELD = /^ {0,3}(?:target )?(repository|service|files?):[ \t]*(.*)$/i;

function repositoryTarget(value, aliases) {
  const normalized = value.toLowerCase();
  if (aliases.includes(normalized)) return `promptdriven/${normalized}`;
  const slug = normalized.replace(/^https:\/\/github\.com\/(.+?)\/?$/, '$1');
  return SLUG.test(slug) && slug.split('/').every(part => part !== '.' && part !== '..') ? slug : null;
}

function fileTarget(value, aliases) {
  if (/[\s,;]/.test(value)) return null;
  const github = /^https:\/\/github\.com\/([^/]+\/[^/]+)\/(?:blob|tree)\/[^/]+\/.+$/i.exec(value);
  if (github) return repositoryTarget(github[1], []);
  const normalized = value.toLowerCase().replace(/^promptdriven\//, '');
  const slash = normalized.indexOf('/');
  return slash >= 0 && normalized.length > slash + 1 ? repositoryTarget(normalized.slice(0, slash), aliases) : null;
}

export function planIssueRouting({ repository, title, body }) {
  const local = repository.toLowerCase();
  const aliases = local === PDD_REPO ? PDD_ALIASES : [];
  const targets = new Set();
  const prefix = TITLE_TARGET.exec(title.trimStart());
  const titleTarget = prefix && repositoryTarget((prefix[1] ?? prefix[2]).trim(), aliases);
  if (titleTarget) targets.add(titleTarget);

  let fence = null;
  for (const line of body.replace(/<!--[\s\S]*?(?:-->|$)/g, '').split(/\r?\n/)) {
    const boundary = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(line);
    if (fence) {
      if (boundary && boundary[1].startsWith(fence) && !boundary[2].trim()) fence = null;
      continue;
    }
    if (boundary) { fence = boundary[1]; continue; }
    const field = TARGET_FIELD.exec(line);
    if (!field) continue;
    const value = field[2].trim().replace(/^`([^`]+)`$/, '$1');
    const target = /^files?$/i.test(field[1]) ? fileTarget(value, aliases) : repositoryTarget(value, aliases);
    if (!target) return NO_ROUTE;
    targets.add(target);
  }
  if (targets.size !== 1 || targets.has(local)) return NO_ROUTE;
  return { targetRepository: targets.values().next().value, label: ROUTING_LABEL };
}
