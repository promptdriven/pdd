// Generated from prompts/cli/try-session.prompt.md (sha256: 135b765aee6b0dcac513a445679f302c871d648aaa45142a4129e2d3d0090ada).

function fail(code, message = code) {
  const error = new Error(message);
  error.code = code;
  throw error;
}

export function bindExistingTry({ try_id, story, records, drift, model }) {
  const hits = records.filter(record => record.id === try_id);
  if (hits.length !== 1) fail('try-not-found', `No open Try with ID "${try_id}". No new Try was opened.`);
  const record = hits[0];
  if (story !== undefined && story !== '' && ![record.story, record.story_path, record.test_path, record.test_name].includes(story)) {
    fail('story-mismatch', `Try "${try_id}" belongs to "${record.story_path}", not "${story}".`);
  }
  if (drift !== null) fail('source-drift', drift || 'The Story or prompt changed since this Try started.');
  if (model.status !== 200) {
    fail('session-not-running', `Try "${try_id}" is not running (HTTP ${model.status}${model.error_code ? `: ${model.error_code}` : ''}). No new Try or reopen was sent.`);
  }
  if (record.max_calls !== null && model.cap !== null && record.max_calls !== model.cap) {
    fail('cap-mismatch', `Try "${try_id}" reported call cap ${model.cap} instead of pinned cap ${record.max_calls}.`);
  }
  return {
    try_id: record.id,
    test_path: record.test_path,
    story_path: record.story_path,
    source_sha256: record.source_sha256,
    engine_sha: record.engine_sha,
    server_commit: record.server_commit,
    cap: model.cap !== null ? model.cap : record.max_calls,
    remaining: model.remaining,
  };
}

export function projectTryCall({ request_id, declared_errors, state, has_program_result, usage_calls, report }) {
  if (state === 'queued' || state === 'running' || state === 'unknown') {
    fail('unknown-outcome', 'The command result is unknown. Do not repeat it automatically.');
  }
  if (state === 'passed') {
    if (!has_program_result) fail('unknown-outcome', 'The command result is unknown. Do not repeat it automatically.');
    return {
      outcome: 'result',
      run_id: request_id,
      action_id: report !== null ? report.action_id : null,
      error_code: null,
      replayed: report !== null ? Boolean(report.replayed) : false,
      calls: usage_calls,
      remaining_calls: report !== null ? report.remaining_calls : null,
    };
  }
  if ((state === 'failed' || state === 'refused') && report !== null && report.verdict === 'failed' && report.error_code !== null && declared_errors.includes(report.error_code)) {
    return {
      outcome: 'program_error',
      run_id: request_id,
      action_id: report.action_id,
      error_code: report.error_code,
      replayed: Boolean(report.replayed),
      calls: usage_calls,
      remaining_calls: report.remaining_calls,
    };
  }
  fail('call-refused', 'The interpreter refused the command.');
}

export function projectTryObservation({ try_id, run_id, status, body }) {
  if (status === 404) fail('run-not-found', `No call "${run_id}" was found on Try "${try_id}".`);
  if (status === 410) fail('result-expired', `Call "${run_id}" on Try "${try_id}" has expired.`);
  if (status !== 200 || body === null || body.session_id !== try_id || body.request_id !== run_id) {
    fail('observation-unavailable', `Observation for call "${run_id}" on Try "${try_id}" is unavailable${status ? ` (HTTP ${status})` : ''}.`);
  }
  return {
    try_id: body.session_id,
    run_id: body.request_id,
    action_id: body.action_id,
    state: body.state,
    session_state: body.session_state,
    terminal: body.state === 'passed' || body.state === 'failed' || body.state === 'refused',
    unknown_outcome: body.state === 'unknown',
    source_sha256: body.source_sha256,
    server_commit: body.server_commit,
    engine_sha: body.engine_sha,
  };
}

export function selectTryToStop({ selector, records }) {
  if (selector === undefined || selector === '') {
    if (records.length === 0) fail('stop-not-found', 'No open Try in this repository.');
    if (records.length > 1) fail('stop-ambiguous', 'Name the Try to stop.');
    return { id: records[0].id, test_path: records[0].test_path, story_path: records[0].story_path };
  }
  const hits = records.filter(record => [record.id, record.story_path, record.story, record.test_path, record.test_name].includes(selector));
  if (hits.length === 0) fail('stop-not-found', `No open Try for "${selector}".`);
  if (hits.length > 1) fail('stop-ambiguous', `More than one open Try matches "${selector}".`);
  return { id: hits[0].id, test_path: hits[0].test_path, story_path: hits[0].story_path };
}
