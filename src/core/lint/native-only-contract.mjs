// Prompt: prompts/cli/repo-hygiene-lint.prompt.md

// Native-only prompt contract completeness check (`native-only-contract-incomplete`).
import { isMarkdownTableSeparator, isNativeOnlyPrompt, scanMarkdownLinesAndFences, stripPromptMetadataPreservingLines } from './prompt-metadata.mjs';
import { DECLARATIVE_SCHEMA_FENCE_LANGS } from './prompt-rules.mjs';

const NETWORK_PORT_HEADING_RE = /\b(?:tcp|udp|http|https|grpc|listen(?:ing)?|network|socket|server|tls|ssl|firewall|docker|container|kubernetes|k8s|ingress|expos(?:e|ed))\b/i;
const DOMAIN_PORT_HEADING_RE = /\b(?:port\s+wiring|port\s+bindings?|bound\s+ports?|wired\s+ports?|injected\s+ports?|external\s+ports?|port\s+adapters?|port\s+map(?:ping)?|port\s+interface|port\s+contract|dependency\s+wiring|ports?)\b/i;
const PORT_WIRING_PHRASE_RE = /\b(?:port\s+wiring|port\s+bindings?|bound\s+ports?|wired\s+ports?|injected\s+ports?|external\s+ports?|port\s+adapters?|port\s+map(?:ping)?|port\s+interface|port\s+contract|dependency\s+wiring|ports?)\b/gi;
const NATIVE_CONTRACT_BOUNDARY_HEADING_RE = /\b(?:boundary|runtime|storage|schema|ddl|database|table|tables|sqlite|postgres|transaction|transactions|locking|lock|concurrency|http|https|wire|route|routes|endpoint|endpoints|api|protocol|cli|subcommands?|flags?|commands?|os|process|subprocess|sandbox|tty|pty|socket|filesystem|file\s+layout|auth|authentication|authorization|crypto|kms|tls|execution|adapter|driver|transport|persistence|layout|contract|interface)\b/i;
const NATIVE_CONTRACT_ERROR_HEADING_RE = /\b(?:errors?|failures?|failure\s+modes?|error\s+mapping|degradation|refusals?|recovery|fallback|timeouts?|retries|exceptions?)\b/i;
const NATIVE_CONTRACT_VERIFY_HEADING_RE = /\b(?:verification|verify|native\s+tests?|native\s+test\s+cases?|native\s+verification|smoke\s+tests?|smoke\s+checks?|integration\s+tests?|real[- ]host|live[- ]host|end[- ]to[- ]end|e2e|test\s+cases?|testing)\b/i;
const NATIVE_CONTRACT_ERROR_CUE_RE = /\b(?:exit\s+code|status\s+code|(?:http|status(?:\s+code)?|error)\s+[45]\d\d|stderr|error\s+mapping|error\s+code|fail(?:s|ed|ure)?\s+closed|rollback|timeout|timed?\s+out|retry|retries|reject(?:s|ed)?|refus(?:e|es|ed)|never\s+throws?|throws?\s+on|unreadable|unavailable|degrade(?:s|d)?|offline|permission\s+denied|enoent|eperm|eacces|econnrefused|deadlock|busy|conflict|lock\s+contention|atomic(?:ally)?)\b/i;
const NATIVE_CONTRACT_VERIFY_CUE_RE = /\b(?:real[- ]host|live[- ]host|live[- ]local|--live-local|smoke\s+(?:test|tests|check|checks)|integration\s+(?:test|tests)|native\s+(?:test|tests|verification|smoke|probe|probes)|non[- ]mocked|real\s+(?:binary|subprocess|process|sandbox|tty|device|sqlite|postgres|database|driver|server|http|socket|filesystem|kernel|host))\b/i;

function isThematicBreak(trimmed) {
  if (trimmed.length < 3) return false;
  let marker = null;
  let count = 0;
  for (let i = 0; i < trimmed.length; i++) {
    const ch = trimmed[i];
    if (ch === ' ' || ch === '\t') continue;
    if (ch !== '-' && ch !== '*' && ch !== '_') return false;
    if (marker === null) marker = ch;
    else if (ch !== marker) return false;
    count++;
  }
  return count >= 3;
}

function isPortOnlyContractHeading(title) {
  if (NETWORK_PORT_HEADING_RE.test(title) || !DOMAIN_PORT_HEADING_RE.test(title)) return false;
  return !NATIVE_CONTRACT_BOUNDARY_HEADING_RE.test(title.replace(PORT_WIRING_PHRASE_RE, ' '));
}

export function collectNativeOnlyContractFindings(text, { path = 'prompts/service.prompt.md' } = {}) {
  if (!isNativeOnlyPrompt(text)) return [];
  const cleaned = stripPromptMetadataPreservingLines(text);
  const { fences, proseLines } = scanMarkdownLinesAndFences(cleaned);

  const emptyFlags = { depth: 0, inDependencies: false, inPortOnly: false, boundary: false, error: false, verify: false };
  const sectionStack = [];
  const currentFlags = () => sectionStack.at(-1) ?? emptyFlags;
  let hasBoundarySurface = false;
  let hasErrorMapping = false;
  let hasNativeVerification = false;
  const headingEvents = [];

  for (let idx = 0; idx < proseLines.length; idx++) {
    const { lineNo, text: line } = proseLines[idx];
    const heading = /^ {0,3}(#{2,6})\s+(.+)$/.exec(line);
    if (heading) {
      const depth = heading[1].length;
      const title = heading[2].trim();
      while (sectionStack.length > 0 && sectionStack.at(-1).depth >= depth) sectionStack.pop();
      const parent = currentFlags();
      const inDependencies = parent.inDependencies || (depth === 2 && /^dependencies\b/i.test(title));
      let nextFlags;
      if (inDependencies) {
        nextFlags = { depth, inDependencies: true, inPortOnly: false, boundary: false, error: false, verify: false };
      } else {
        const portOnly = isPortOnlyContractHeading(title);
        const ownBoundary = !portOnly && NATIVE_CONTRACT_BOUNDARY_HEADING_RE.test(title);
        nextFlags = {
          depth,
          inDependencies: false,
          inPortOnly: portOnly ? true : (ownBoundary ? false : parent.inPortOnly),
          boundary: parent.boundary || ownBoundary,
          error: parent.error || NATIVE_CONTRACT_ERROR_HEADING_RE.test(title),
          verify: parent.verify || NATIVE_CONTRACT_VERIFY_HEADING_RE.test(title),
        };
      }
      sectionStack.push(nextFlags);
      headingEvents.push({ lineNo, flags: nextFlags });
      continue;
    }

    const active = currentFlags();
    if (active.inDependencies) continue;
    const trimmed = line.trim();
    if (!trimmed || /^ {0,3}#\s+/.test(line) || isThematicBreak(trimmed)) continue;

    if (active.boundary) hasBoundarySurface = true;
    if (active.error) hasErrorMapping = true;
    if (active.verify) hasNativeVerification = true;
    if (!active.inPortOnly && !hasBoundarySurface && line.includes('|') && idx + 1 < proseLines.length && isMarkdownTableSeparator(proseLines[idx + 1].text)) hasBoundarySurface = true;
    if (!hasErrorMapping && NATIVE_CONTRACT_ERROR_CUE_RE.test(trimmed)) hasErrorMapping = true;
    if (!hasNativeVerification && NATIVE_CONTRACT_VERIFY_CUE_RE.test(trimmed)) hasNativeVerification = true;
  }

  let headingIdx = -1;
  for (const fence of fences) {
    if (!fence.bodyLines.some(item => item.text.trim().length > 0)) continue;
    while (headingIdx + 1 < headingEvents.length && headingEvents[headingIdx + 1].lineNo < fence.openLine) headingIdx++;
    const active = headingIdx >= 0 ? headingEvents[headingIdx].flags : emptyFlags;
    if (active.inDependencies) continue;
    if (active.boundary) hasBoundarySurface = true;
    if (active.error) hasErrorMapping = true;
    if (active.verify) hasNativeVerification = true;
    if (!active.inPortOnly && DECLARATIVE_SCHEMA_FENCE_LANGS.has(fence.lang)) hasBoundarySurface = true;
    if (!hasErrorMapping || !hasNativeVerification) {
      for (const item of fence.bodyLines) {
        if (!hasErrorMapping && NATIVE_CONTRACT_ERROR_CUE_RE.test(item.text)) hasErrorMapping = true;
        if (!hasNativeVerification && NATIVE_CONTRACT_VERIFY_CUE_RE.test(item.text)) hasNativeVerification = true;
        if (hasErrorMapping && hasNativeVerification) break;
      }
    }
  }

  const missing = [];
  if (!hasBoundarySurface) missing.push('boundary/runtime contract (storage/DDL, transaction/locking, wire/HTTP/CLI/OS/auth surface)');
  if (!hasErrorMapping) missing.push('error mapping / failure behavior');
  if (!hasNativeVerification) missing.push('real-host / native verification cases');
  if (!missing.length) return [];

  const detail = `Native-only prompt is missing required specification sections: ${missing.join('; ')}. Document the concrete boundary/runtime contract, error mapping, and executable non-mocked real-host verification cases.`;
  return [{
    filePath: path,
    line: 1,
    order: 3,
    code: 'native-only-contract-incomplete',
    category: 'native-only contract',
    defaultSeverity: 'warn',
    detail,
    fix: `Add ${missing.join(', ')} sections to ${path}`,
    warning: `Warning: native-only contract: ${path}:1 [native-only-contract-incomplete] ${detail}`,
  }];
}

export const lintNativeOnlyContract = (text, opts = {}) => collectNativeOnlyContractFindings(text, opts).map(r => r.warning);
