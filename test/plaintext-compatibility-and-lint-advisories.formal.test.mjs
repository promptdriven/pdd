import test from 'node:test';
import assert from 'node:assert/strict';

async function loadDisplayModule() {
  try {
    return await import('../src/lint-compatibility-display.mjs');
  } catch (error) {
    if (error?.code === 'ERR_MODULE_NOT_FOUND') {
      assert.fail(
        'lint-compatibility-display module is missing; plain-text compatibility summary and severity-split lint advisories are unimplemented',
      );
    }
    throw error;
  }
}

// Independent formal oracle derived strictly from the approved Story
// user_stories/plaintext-compatibility-and-lint-advisories.md
// ("## Acceptance criteria", "## What must not change", "## Rules to check")
// and the approved contract prompts/cli/lint-compatibility-display.prompt.md.

const LABELS = ['tests/place-order.json'];
const STATES = ['supported', 'unsupported', 'unknown'];
const ASSOCIATIONS = ['matched', 'unmatched', 'unavailable'];
const ISSUES = [null, 'capability-association-mismatch'];
const CLIENT_ADVICES = [
  null,
  {
    // Put next_step before owner to verify key-order preservation in detailed
    // mode and named-field formatting in default single-line mode.
    next_step: 'Behavioral execution remains required.',
    owner: 'application author',
  },
];
const COMPLETE_VALUES = [true, false];
const ENGINE_BUILDS = ['unknown', '088d558b937300e552386b0f81e0bd5e2ce782fb'];
const OP_COUNTS = [0, 1, 2, 3];
const EDGE_COUNTS = [0, 1, 2];
const STEP_PATTERNS = ['distinct', 'shared'];
const ITEM_PROFILES = ['all-supported', 'mixed-modes-and-verdicts'];

function deepFreeze(value) {
  if (value === null || typeof value !== 'object') return value;
  if (Array.isArray(value)) {
    for (const item of value) deepFreeze(item);
  } else {
    for (const key of Object.keys(value)) deepFreeze(value[key]);
  }
  return Object.freeze(value);
}

function buildOperation(index, stepPattern, profile) {
  const stepId = stepPattern === 'shared' ? 'step-shared' : `op-step-${index}`;
  const isMixed = profile === 'mixed-modes-and-verdicts';
  const executionModes = ['ordinary', 'delegated', 'ordinary'];
  const resourceModes = ['simulated', 'host', 'none'];
  const verdicts = ['missing-binding', 'supported', 'unsupported'];
  const reasons = ['binding-missing', 'supported', 'feature-unsupported'];
  return {
    binding_kind: isMixed && index === 0 ? 'missing' : 'none',
    evaluator_mode: 'codex-subscription',
    execution_mode: isMixed ? executionModes[index % executionModes.length] : 'ordinary',
    feature: 'ordinary',
    reason_code: isMixed ? reasons[index % reasons.length] : 'supported',
    resource_mode: isMixed ? resourceModes[index % resourceModes.length] : 'simulated',
    selection: {
      node_id: `node_${index}`,
      operation: 'run_op',
      prompt_path: `prompts/op_${index}.prompt.md`,
      step_id: stepId,
    },
    verdict: isMixed ? verdicts[index % verdicts.length] : 'supported',
  };
}

function buildEdge(index, stepPattern, profile) {
  const stepId = stepPattern === 'shared' ? 'step-shared' : `edge-step-${index}`;
  const isMixed = profile === 'mixed-modes-and-verdicts';
  const executionModes = ['ordinary', 'delegated'];
  const resourceModes = ['simulated', 'host'];
  const verdicts = ['missing-binding', 'supported'];
  const reasons = ['binding-missing', 'supported'];
  return {
    binding_kind: isMixed && index === 0 ? 'missing' : 'simulated',
    evaluator_mode: 'codex-subscription',
    execution_mode: isMixed ? executionModes[index % executionModes.length] : 'ordinary',
    feature: 'ordinary',
    reason_code: isMixed ? reasons[index % reasons.length] : 'supported',
    resource_mode: isMixed ? resourceModes[index % resourceModes.length] : 'simulated',
    selection: {
      edge: {
        call_operation: `res.op_${index}`,
        edge_id: `edge-${index}`,
        kind: 'resource',
        resource_operation: `res.op_${index}`,
        target_node_id: '',
        target_operation: '',
        target_path: '',
      },
      node_id: `node_edge_${index}`,
      operation: 'run_op',
      prompt_path: 'prompts/place_order.prompt.md',
      step_id: stepId,
    },
    verdict: isMixed ? verdicts[index % verdicts.length] : 'supported',
  };
}

function buildReportedDomain() {
  const reports = [
    null,
    { complete: false, engine_build: 'unknown' },
    { complete: true, engine_build: '088d558b937300e552386b0f81e0bd5e2ce782fb' },
  ];
  for (const opCount of OP_COUNTS) {
    for (const edgeCount of EDGE_COUNTS) {
      for (const stepPattern of STEP_PATTERNS) {
        for (const profile of ITEM_PROFILES) {
          for (const complete of COMPLETE_VALUES) {
            for (const engineBuild of ENGINE_BUILDS) {
              const operations = Array.from({ length: opCount }, (_, i) =>
                buildOperation(i, stepPattern, profile),
              );
              const edges = Array.from({ length: edgeCount }, (_, i) =>
                buildEdge(i, stepPattern, profile),
              );
              reports.push({
                schema_version: 'prompt-runtime.program-capabilities.v1',
                capability_version: `program-capabilities.v1@${engineBuild}`,
                engine_build: engineBuild,
                complete,
                verdict: profile === 'all-supported' ? 'supported' : 'missing-binding',
                provider_calls: 0,
                resource_calls: 0,
                diagnostics: [{ code: 'diag-sample', path: null, section: 'graph' }],
                operations,
                edges,
              });
            }
          }
        }
      }
    }
  }
  return reports;
}

function uniqueInOrder(values) {
  const out = [];
  for (const value of values) {
    if (!out.includes(value)) out.push(value);
  }
  return out;
}

function countLabel(count, singular, plural) {
  return count === 1 ? `1 ${singular}` : `${count} ${plural}`;
}

function storyOracleCompatibility({ label, compatibility, clientAdvice, details }) {
  if (details) {
    const first = `Compatibility (${label}): ${JSON.stringify(compatibility, null, 2)}`;
    return clientAdvice === null
      ? first
      : `${first}\n  Client advice: ${JSON.stringify(clientAdvice)}`;
  }

  const reported = compatibility.reported;
  const parts = [`${compatibility.state} (association ${compatibility.association})`];

  if (
    reported !== null &&
    typeof reported === 'object' &&
    Array.isArray(reported.operations) &&
    Array.isArray(reported.edges)
  ) {
    const items = [...reported.operations, ...reported.edges];
    const stepCount = uniqueInOrder(items.map(item => item.selection.step_id)).length;
    const execModes = items.length
      ? uniqueInOrder(items.map(item => item.execution_mode)).join(', ')
      : 'none';
    const resModes = items.length
      ? uniqueInOrder(items.map(item => item.resource_mode)).join(', ')
      : 'none';
    const engine =
      reported.engine_build === 'unknown'
        ? 'unknown'
        : reported.engine_build.slice(0, 12);
    parts.push(
      `${countLabel(stepCount, 'step', 'steps')} (${countLabel(reported.operations.length, 'operation', 'operations')}, ${countLabel(reported.edges.length, 'edge', 'edges')})`,
      `execution ${execModes}`,
      `resources ${resModes}`,
      `complete ${reported.complete}`,
      `engine ${engine}`,
    );
    if (typeof compatibility.issue === 'string' && compatibility.issue.trim().length > 0) {
      parts.push(`issue ${compatibility.issue}`);
    }
    const nonSupported = uniqueInOrder(
      items.filter(item => item.verdict !== 'supported').map(item => item.reason_code),
    );
    if (nonSupported.length > 0) {
      parts.push(`non-supported: ${nonSupported.join(', ')}`);
    }
  } else {
    if (typeof reported?.complete === 'boolean') {
      parts.push(`complete ${reported.complete}`);
    }
    if (typeof reported?.engine_build === 'string' && reported.engine_build.length > 0) {
      parts.push(
        `engine ${reported.engine_build === 'unknown' ? 'unknown' : reported.engine_build.slice(0, 12)}`,
      );
    }
    if (typeof compatibility.issue === 'string' && compatibility.issue.trim().length > 0) {
      parts.push(`issue ${compatibility.issue}`);
    }
  }

  const summaryLine = `Compatibility (${label}): ${parts.join('; ')}.`;
  return clientAdvice === null
    ? summaryLine
    : `${summaryLine}\n  Client advice (${clientAdvice.owner}): ${clientAdvice.next_step}`;
}

const DIAGNOSTIC_TEMPLATES = [
  {
    kind: 'warning',
    build: slot => ({
      code: `warn-no-hint-${slot}`,
      path: 'prompts/place_order.prompt.md',
      section: 'Runtime interface',
      message: `Advisory message ${slot}.`,
      hint: null,
      severity: 'warning',
    }),
  },
  {
    kind: 'warning',
    build: slot => ({
      code: `warn-with-hint-${slot}`,
      path: 'prompts/checkout.prompt.md',
      section: '/kind',
      message: `Advisory with hint ${slot}.`,
      hint: `Hint for warning ${slot}.`,
      severity: 'warning',
      local_findings: [{ code: `nested-warn-${slot}`, section: '/kind', message: 'Nested local note.' }],
    }),
  },
  {
    kind: 'warning',
    build: slot => ({
      code: `warn-no-path-${slot}`,
      path: null,
      section: 'Story',
      message: `Unscoped warning ${slot}.`,
      hint: '',
      severity: 'warning',
    }),
  },
  {
    kind: 'blocking',
    build: slot => ({
      code: `err-explicit-${slot}`,
      path: 'prompts/place_order.prompt.md',
      section: 'Runtime interface',
      message: `Blocking error ${slot}.`,
      hint: `Run pdd test --fill-hash (${slot}).`,
      severity: 'error',
    }),
  },
  {
    kind: 'blocking',
    build: slot => ({
      code: `err-null-sev-${slot}`,
      path: 'prompts/helper.prompt.md',
      section: null,
      message: `Blocking null-severity ${slot}.`,
      hint: null,
      severity: null,
      local_findings: [{ code: `nested-block-${slot}`, message: 'Nested blocking note.' }],
    }),
  },
  {
    kind: 'blocking',
    build: slot => ({
      code: `err-omitted-sev-${slot}`,
      path: 'prompts/pricing.prompt.md',
      section: 'Dependencies',
      message: `Blocking omitted-severity ${slot}.`,
      hint: '',
    }),
  },
];

function enumerateSequences(alphabetSize, maxLength) {
  const sequences = [[]];
  for (let len = 1; len <= maxLength; len++) {
    const prev = sequences.filter(seq => seq.length === len - 1);
    for (const prefix of prev) {
      for (let symbol = 0; symbol < alphabetSize; symbol++) {
        sequences.push([...prefix, symbol]);
      }
    }
  }
  return sequences;
}

function storyOracleDiagnostics({ problems, localOnly }) {
  if (problems.length === 0) return '';
  const blocking = problems.filter(item => item.severity !== 'warning');
  const advisories = problems.filter(item => item.severity === 'warning');
  const lines = [];

  if (blocking.length > 0) {
    lines.push(localOnly ? 'Local lint problems:' : 'Lint problems (from the PDD interpreter):');
    for (const item of blocking) {
      lines.push(`  ${[item.code, item.path, item.section, item.message].filter(Boolean).join('  ')}`);
      if (typeof item.hint === 'string' && item.hint.trim().length > 0) {
        lines.push(`    ${item.hint}`);
      }
    }
  }

  if (advisories.length > 0) {
    lines.push(localOnly ? 'Local lint advisories:' : 'Lint advisories (from the PDD interpreter):');
    for (const item of advisories) {
      lines.push(`  ${[item.code, item.path, item.section, item.message].filter(Boolean).join('  ')}`);
      if (typeof item.hint === 'string' && item.hint.trim().length > 0) {
        lines.push(`    ${item.hint}`);
      }
    }
  }

  return lines.join('\n');
}

test('FORMAL Rule 1 & Rule 3: single-line default compatibility summary, detailed full JSON preservation, and input immutability (7020 configurations, 14040 evaluations)', async () => {
  const { describeCompatibility } = await loadDisplayModule();
  const reports = buildReportedDomain();
  assert.equal(reports.length, 195);

  let configurations = 0;
  let evaluations = 0;
  for (const label of LABELS) {
    for (const state of STATES) {
      for (const association of ASSOCIATIONS) {
        for (const issue of ISSUES) {
          for (const reported of reports) {
            for (const clientAdvice of CLIENT_ADVICES) {
              const plainInput = {
                label,
                compatibility: {
                  state,
                  association,
                  issue,
                  reported: structuredClone(reported),
                },
                clientAdvice: structuredClone(clientAdvice),
                details: false,
              };
              const plainSnapshot = structuredClone(plainInput);
              const plainActual = describeCompatibility(plainInput);

              // Rule 3: purity & zero mutation of supplied inputs and nested arrays/objects.
              assert.deepEqual(plainInput, plainSnapshot, 'describeCompatibility mutated its input');
              let frozenPlainActual;
              assert.doesNotThrow(() => {
                frozenPlainActual = describeCompatibility(deepFreeze(structuredClone(plainSnapshot)));
              }, 'describeCompatibility attempted transient mutation on frozen input');
              assert.deepEqual(frozenPlainActual, plainActual, 'describeCompatibility must be deterministic');

              assert.deepEqual(Object.keys(plainActual), ['text']);
              assert.equal(typeof plainActual.text, 'string');
              assert.equal(plainActual.text.endsWith('\n'), false);

              // Rule 1 forbidden states when detailed mode is off:
              const lines = plainActual.text.split('\n');
              const expectedLineCount = clientAdvice === null ? 1 : 2;
              assert.equal(
                lines.length,
                expectedLineCount,
                `default mode must emit ${expectedLineCount} line(s), got ${lines.length}`,
              );
              assert.equal(lines[0].startsWith(`Compatibility (${label}): `), true);
              assert.equal(lines[0].endsWith('.'), true);
              assert.equal(
                /[{}]/.test(lines[0]),
                false,
                'default Compatibility summary line must contain zero JSON braces',
              );
              if (clientAdvice !== null) {
                assert.equal(
                  lines[1],
                  `  Client advice (${clientAdvice.owner}): ${clientAdvice.next_step}`,
                );
              } else {
                const defaulted = describeCompatibility({
                  label: plainSnapshot.label,
                  compatibility: structuredClone(plainSnapshot.compatibility),
                });
                assert.deepEqual(defaulted, plainActual);
              }

              // Full Story & contract oracle comparison for default plain-text mode:
              const expectedPlainText = storyOracleCompatibility(plainSnapshot);
              assert.equal(plainActual.text, expectedPlainText);
              evaluations++;

              // Detailed mode preservation & Rule 3 immutability on the same configuration:
              const detailedInput = {
                label,
                compatibility: {
                  state,
                  association,
                  issue,
                  reported: structuredClone(reported),
                },
                clientAdvice: structuredClone(clientAdvice),
                details: true,
              };
              const detailedSnapshot = structuredClone(detailedInput);
              const detailedActual = describeCompatibility(detailedInput);

              assert.deepEqual(detailedInput, detailedSnapshot, 'describeCompatibility mutated its input');
              let frozenDetailedActual;
              assert.doesNotThrow(() => {
                frozenDetailedActual = describeCompatibility(deepFreeze(structuredClone(detailedSnapshot)));
              }, 'describeCompatibility attempted transient mutation on frozen input');
              assert.deepEqual(frozenDetailedActual, detailedActual, 'describeCompatibility must be deterministic');

              assert.deepEqual(Object.keys(detailedActual), ['text']);
              assert.equal(typeof detailedActual.text, 'string');
              assert.equal(detailedActual.text.endsWith('\n'), false);

              const expectedDetailedText = storyOracleCompatibility(detailedSnapshot);
              assert.equal(detailedActual.text, expectedDetailedText);
              evaluations++;

              configurations++;
            }
          }
        }
      }
    }
  }

  assert.equal(configurations, 7020);
  assert.equal(evaluations, 14040);
});

test('FORMAL Rule 2 & Rule 3: bounded lint severity partitioning, relative order and input immutability (3110 inputs)', async () => {
  const { describeLintDiagnostics } = await loadDisplayModule();
  const sequences = enumerateSequences(DIAGNOSTIC_TEMPLATES.length, 4);
  assert.equal(sequences.length, 1555);

  let checked = 0;
  for (const localOnly of [false, true]) {
    const expectedProblemsHeading = localOnly
      ? 'Local lint problems:'
      : 'Lint problems (from the PDD interpreter):';
    const expectedAdvisoriesHeading = localOnly
      ? 'Local lint advisories:'
      : 'Lint advisories (from the PDD interpreter):';
    const forbiddenProblemsHeading = localOnly
      ? 'Lint problems (from the PDD interpreter):'
      : 'Local lint problems:';
    const forbiddenAdvisoriesHeading = localOnly
      ? 'Lint advisories (from the PDD interpreter):'
      : 'Local lint advisories:';

    for (const seq of sequences) {
      const problems = seq.map((templateIndex, slot) =>
        DIAGNOSTIC_TEMPLATES[templateIndex].build(slot),
      );
      const input = { problems, localOnly };
      const snapshot = structuredClone(input);
      const actual = describeLintDiagnostics(input);

      // Rule 3: purity & zero mutation of problems and nested local_findings.
      assert.deepEqual(input, snapshot, 'describeLintDiagnostics mutated its input');
      let frozenActual;
      assert.doesNotThrow(() => {
        frozenActual = describeLintDiagnostics(deepFreeze(structuredClone(snapshot)));
      }, 'describeLintDiagnostics attempted transient mutation on frozen input');
      assert.deepEqual(frozenActual, actual, 'describeLintDiagnostics must be deterministic');

      if (!localOnly) {
        const defaulted = describeLintDiagnostics({ problems: structuredClone(snapshot.problems) });
        assert.deepEqual(defaulted, actual);
      }

      assert.deepEqual(Object.keys(actual), ['text']);
      assert.equal(typeof actual.text, 'string');
      assert.equal(actual.text.includes(forbiddenProblemsHeading), false);
      assert.equal(actual.text.includes(forbiddenAdvisoriesHeading), false);

      const expectedWarnings = snapshot.problems.filter((_, i) => DIAGNOSTIC_TEMPLATES[seq[i]].kind === 'warning');
      const expectedBlocking = snapshot.problems.filter((_, i) => DIAGNOSTIC_TEMPLATES[seq[i]].kind === 'blocking');

      // Rule 2 structural & forbidden-state checks:
      if (expectedBlocking.length === 0 && expectedWarnings.length === 0) {
        assert.equal(actual.text, '');
      } else if (expectedBlocking.length === 0) {
        assert.equal(
          /lint problems/i.test(actual.text),
          false,
          'warning-only input must emit no Lint problems or Local lint problems heading',
        );
        assert.equal(actual.text.startsWith(expectedAdvisoriesHeading), true);
      } else if (expectedWarnings.length === 0) {
        assert.equal(
          /lint advisories/i.test(actual.text),
          false,
          'blocking-only input must emit no Lint advisories or Local lint advisories heading',
        );
        assert.equal(actual.text.startsWith(expectedProblemsHeading), true);
      } else {
        const problemsIdx = actual.text.indexOf(expectedProblemsHeading);
        const advisoriesIdx = actual.text.indexOf(expectedAdvisoriesHeading);
        assert.equal(problemsIdx, 0, 'blocking problems heading must come first');
        assert.ok(advisoriesIdx > problemsIdx, 'blocking problems must precede advisories');

        const problemsSection = actual.text.slice(problemsIdx, advisoriesIdx);
        const advisoriesSection = actual.text.slice(advisoriesIdx);

        for (const warn of expectedWarnings) {
          assert.equal(
            problemsSection.includes(warn.code),
            false,
            `warning ${warn.code} must never appear under ${expectedProblemsHeading}`,
          );
          assert.equal(advisoriesSection.includes(warn.code), true);
        }
        for (const block of expectedBlocking) {
          assert.equal(
            advisoriesSection.includes(block.code),
            false,
            `blocking finding ${block.code} must never appear under ${expectedAdvisoriesHeading}`,
          );
          assert.equal(problemsSection.includes(block.code), true);
        }

        // Strict relative input order within each group:
        let prevBlockOffset = -1;
        for (const block of expectedBlocking) {
          const offset = problemsSection.indexOf(block.code);
          assert.ok(offset > prevBlockOffset, 'blocking relative order must be preserved');
          prevBlockOffset = offset;
        }
        let prevWarnOffset = -1;
        for (const warn of expectedWarnings) {
          const offset = advisoriesSection.indexOf(warn.code);
          assert.ok(offset > prevWarnOffset, 'advisory relative order must be preserved');
          prevWarnOffset = offset;
        }
      }

      // Full Story & contract oracle comparison:
      const expectedText = storyOracleDiagnostics(snapshot);
      assert.equal(actual.text, expectedText);
      checked++;
    }
  }

  assert.equal(checked, 3110);
});
