// Generated from prompts/cli/runtime/lint-call-preflight.prompt.md (sha256: 0d9ea82c1fa4713dcead621642590e65aeca1ffee8e2f99bb3aa23ae284f3a85).
// The Runtime supplies all costs. Association gates display only, never paid admission.
export function describeCallPreflight({ test, preflight, context, sourceSha256, requestedCap }) {
  const trusted = preflight && context && context.source_sha256 === sourceSha256
    && /^[a-f0-9]{40}$/.test(context.engine_build ?? '')
    && context.selected_cap === requestedCap && preflight.selected_cap === requestedCap;
  const quantity = value => value ?? 'unknown';
  const lines = [trusted
    ? `Call preflight (${test}): ${preflight.status}; structural catalog estimate ${quantity(preflight.estimated_calls)} calls; selected cap ${preflight.selected_cap ?? 'not selected'}; complete ${preflight.complete}.`
    : `Call preflight (${test}): unavailable; no estimate or cap-fit claim.`];
  if (trusted) for (const step of preflight.steps ?? []) lines.push(
    `  Step ${step.step_id} (${step.entry_path} :: ${step.operation}): catalog ${quantity(step.catalog_calls)}; cumulative ${quantity(step.cumulative_catalog_calls)}; external resources ${step.has_external_resources}.`);
  lines.push(context
    ? `  Source ${context.source_sha256}; engine ${context.engine_build}; configured maximum ${context.max_cap}.`
    : '  Source and engine identity unavailable.');
  if (trusted && preflight.status === 'warning') lines.push('  Warning: the structural estimate exceeds the selected cap; the cap is unchanged.');
  lines.push('  Advisory only: no guarantee of actual calls or completion; resource continuations are not included. Lint uses 0 AI calls.');
  return { text: lines.join('\n') };
}
