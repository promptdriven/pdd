// Standard dependency-cruiser architecture rules replacing scripts/check-architecture.mjs (895 LOC).
// Enforces circular-import freedom, unresolved/undeclared import checks, and PDD's 6 layers:
//   cli -> {cli, setup, core, accounts, autopilot, shared}
//   autopilot -> {autopilot, core, accounts, shared}
//   core -> {core, shared}
//   setup -> {setup, shared}
//   accounts -> {accounts, shared}
//   shared -> {shared}

const CLI =
  '(?:^bin/pdd\\.mjs$|^src/cli/|^src/(?:pdd-cli|command-catalog|argument-parser|completion|try-doors)\\.mjs$)';
const SETUP =
  '(?:^src/setup/|^src/(?:skills-install|agent-mcp-setup|project-setup|setup-interaction|cli-upgrade)\\.mjs$)';
const CORE =
  '(?:^src/core/|^src/(?:interpreter-version|project-files|file-owner|repo-hygiene-lint|story-lint|runtime-seam|scenario-compile|test-selection|compiled-test|svg-layout|screen-compare|screen-design-check|update-sync|product|product-documents|prompt-tests-words|approval-evidence)\\.mjs$|^src/(?:product|screen-)[^/]*\\.mjs$)';
const ACCOUNTS =
  '(?:^bin/pdd-(?:codex|claude)\\.mjs$|^src/accounts/|^src/(?:accounts-cli|login-pool|pdd-codex|pdd-claude|codex-limits)\\.mjs$)';
const AUTOPILOT =
  '(?:^src/autopilot/|^src/(?:autopilot|agent-adapters|agent-job|codex-lint|cost-ledger|machine-guard)\\.mjs$|^src/(?:autopilot-|issue-|metrics-|test-suite-)[^/]*\\.mjs$)';
const SHARED =
  '(?:^src/shared/|^src/(?:toml-string|secret-redaction|process-lifecycle|runtime-exit|path-diagnostic|release-notice|github-calls|agent-config|validation-evidence|machine-resources)\\.mjs$)';

/** @type {import('dependency-cruiser').IConfiguration} */
module.exports = {
  forbidden: [
    {
      name: 'no-circular',
      severity: 'error',
      comment: 'No circular module dependencies across src/ and bin/.',
      from: {},
      to: { circular: true },
    },
    {
      name: 'not-to-unresolvable',
      severity: 'error',
      comment: 'Every local relative import must resolve to an existing file.',
      from: { path: '^(?:src|bin)/' },
      to: { couldNotResolve: true },
    },
    {
      name: 'no-disallowed-npm-deps',
      severity: 'error',
      comment: 'Runtime src/ and bin/ modules may only import Node built-ins or declared production dependencies.',
      from: { path: '^(?:src|bin)/' },
      to: {
        dependencyTypes: ['npm-dev', 'npm-optional', 'npm-peer', 'npm-no-pkg'],
        pathNot: '^smol-toml(?:$|/)',
      },
    },
    {
      name: 'layer-shared-only-shared',
      severity: 'error',
      comment: 'Layer shared may only import from shared.',
      from: { path: SHARED },
      to: { path: '^(?:src|bin)/', pathNot: SHARED },
    },
    {
      name: 'layer-core-only-core-and-shared',
      severity: 'error',
      comment: 'Layer core may only import from core and shared.',
      from: { path: CORE },
      to: { path: '^(?:src|bin)/', pathNot: `${CORE}|${SHARED}` },
    },
    {
      name: 'layer-setup-only-setup-and-shared',
      severity: 'error',
      comment: 'Layer setup may only import from setup and shared.',
      from: { path: SETUP },
      to: { path: '^(?:src|bin)/', pathNot: `${SETUP}|${SHARED}` },
    },
    {
      name: 'layer-accounts-only-accounts-and-shared',
      severity: 'error',
      comment: 'Layer accounts may only import from accounts and shared.',
      from: { path: ACCOUNTS },
      to: { path: '^(?:src|bin)/', pathNot: `${ACCOUNTS}|${SHARED}` },
    },
    {
      name: 'layer-autopilot-no-cli-or-setup',
      severity: 'error',
      comment: 'Layer autopilot may only import from autopilot, core, accounts, and shared (never cli or setup).',
      from: { path: AUTOPILOT },
      to: { path: `${CLI}|${SETUP}` },
    },
  ],
  options: {
    doNotFollow: { path: 'node_modules' },
    includeOnly: '^(?:src|bin)/',
    enhancedResolveOptions: {
      exportsFields: ['exports'],
      conditionNames: ['node', 'import', 'default'],
      extensions: ['.mjs', '.js', '.cjs', '.json'],
    },
    reporterOptions: {
      text: { highlightFocused: true },
    },
  },
};
