// Generated from prompts/cli/runtime/runtime-lint-receipt.prompt.md (sha256: 874f9e5bdd935ce6f0996252f5498db4ed28e689235c85eaa7a2a83a35b62ade).
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const text = value => typeof value === 'string' && value.trim().length > 0;
const knownEngine = value => text(value) && value.trim().toLowerCase() !== 'unknown';
const keys = ['root', 'origin', 'login', 'user_id', 'source_sha256', 'tests', 'version', 'selected_cap'];
function validScope(scope) {
  return object(scope) && Object.keys(scope).length === keys.length && keys.every(key => Object.hasOwn(scope, key))
    && ['root', 'origin', 'login', 'user_id', 'version'].every(key => text(scope[key]))
    && /^\d+$/.test(scope.user_id) && /^[a-f0-9]{64}$/.test(scope.source_sha256)
    && Array.isArray(scope.tests) && scope.tests.length > 0
    && scope.tests.every((path, index) => text(path) && (index === 0 || scope.tests[index - 1] < path))
    && (scope.selected_cap === null || Number.isInteger(scope.selected_cap) && scope.selected_cap >= 1 && scope.selected_cap <= 1000);
}

export function isRecentLintReceipt({ receipt, scope, now, engineSha = null }) {
  if (!object(receipt) || receipt.schema_version !== 'pdd.lint-receipt.v1'
    || !validScope(scope) || !validScope(receipt.scope) || !knownEngine(receipt.engine_sha)
    || !Number.isFinite(now) || !Number.isFinite(receipt.received_at)
    || now < receipt.received_at || now - receipt.received_at > 600_000
    || engineSha !== null && (!knownEngine(engineSha) || engineSha !== receipt.engine_sha)) return false;
  return keys.every(key => key === 'tests'
    ? scope.tests.length === receipt.scope.tests.length && scope.tests.every((path, index) => path === receipt.scope.tests[index])
    : scope[key] === receipt.scope[key]);
}
