// Generated from prompts/cli/lint-compatibility-display.prompt.md (sha256: 78f684d7e78df2b6868258a576155c95208157f03b64223a3c67b192581013f2).

const countText = (count, singular) => count === 1 ? `1 ${singular}` : `${count} ${singular}s`;
const nonblank = value => typeof value === 'string' && value.trim().length > 0;
const distinct = values => [...new Set(values)];

export function describeCompatibility({ label, compatibility, clientAdvice = null, details = false }) {
  if (details) {
    const lines = [`Compatibility (${label}): ${JSON.stringify(compatibility, null, 2)}`];
    if (clientAdvice !== null && clientAdvice !== undefined) lines.push(`  Client advice: ${JSON.stringify(clientAdvice)}`);
    return { text: lines.join('\n') };
  }
  const reported = compatibility?.reported;
  const structured = reported !== null && typeof reported === 'object' && !Array.isArray(reported)
    && Array.isArray(reported.operations) && Array.isArray(reported.edges);
  let summary;
  if (structured) {
    const items = [...reported.operations, ...reported.edges];
    const stepCount = countText(distinct(items.map(item => item.selection.step_id)).length, 'step');
    const opCount = countText(reported.operations.length, 'operation');
    const edgeCount = countText(reported.edges.length, 'edge');
    const execModes = items.length ? distinct(items.map(item => item.execution_mode)).join(', ') : 'none';
    const resModes = items.length ? distinct(items.map(item => item.resource_mode)).join(', ') : 'none';
    const engine = reported.engine_build === 'unknown' ? 'unknown' : String(reported.engine_build ?? '').slice(0, 12);
    summary = `Compatibility (${label}): ${compatibility.state} (association ${compatibility.association}); ${stepCount} (${opCount}, ${edgeCount}); execution ${execModes}; resources ${resModes}; complete ${reported.complete}; engine ${engine}`;
    if (nonblank(compatibility.issue)) summary += `; issue ${compatibility.issue}`;
    const nonSupported = distinct(items.filter(item => item.verdict !== 'supported').map(item => item.reason_code));
    if (nonSupported.length > 0) summary += `; non-supported: ${nonSupported.join(', ')}`;
    summary += '.';
  } else {
    summary = `Compatibility (${label}): ${compatibility.state} (association ${compatibility.association})`;
    if (typeof reported?.complete === 'boolean') summary += `; complete ${reported.complete}`;
    if (typeof reported?.engine_build === 'string' && reported.engine_build.length > 0) {
      summary += `; engine ${reported.engine_build === 'unknown' ? 'unknown' : reported.engine_build.slice(0, 12)}`;
    }
    if (nonblank(compatibility.issue)) summary += `; issue ${compatibility.issue}`;
    summary += '.';
  }
  const lines = [summary];
  if (clientAdvice !== null && clientAdvice !== undefined) {
    lines.push(`  Client advice (${clientAdvice.owner}): ${clientAdvice.next_step}`);
  }
  return { text: lines.join('\n') };
}

export function describeLintDiagnostics({ problems, localOnly = false }) {
  if (!problems.length) return { text: '' };
  const blocking = problems.filter(item => item.severity !== 'warning');
  const advisories = problems.filter(item => item.severity === 'warning');
  const lines = [];
  const emitGroup = (heading, items) => {
    if (!items.length) return;
    lines.push(heading);
    for (const item of items) {
      lines.push(`  ${[item.code, item.path, item.section, item.message].filter(Boolean).join('  ')}`);
      if (nonblank(item.hint)) lines.push(`    ${item.hint}`);
    }
  };
  emitGroup(localOnly ? 'Local lint problems:' : 'Lint problems (from the PDD interpreter):', blocking);
  emitGroup(localOnly ? 'Local lint advisories:' : 'Lint advisories (from the PDD interpreter):', advisories);
  return { text: lines.join('\n') };
}
