import test from 'node:test';
import assert from 'node:assert/strict';
import { evaluateCheckBudget } from '../../src/runtime/runtime-check-plan.mjs';

// Bounded formal state-space check for invocation call-budget conservation and replacement invariants (#793).
test('793 formal invariants: conservation, non-zero uncertainty, single-replacement fuse, and liveness across schedules', () => {
  const attemptStates = [
    { status: 'capacity_refused_zero', known_calls: 0, unknown_calls: 0, reason_code: 'check-capacity' },
    { status: 'settled', known_calls: 0, unknown_calls: 0, reason_code: null },
    { status: 'settled', known_calls: 5, unknown_calls: 0, reason_code: null },
    { status: 'settled', known_calls: 18, unknown_calls: 0, reason_code: null },
    { status: 'in_flight', known_calls: 2, unknown_calls: 0, reason_code: null },
    { status: 'unresolved', known_calls: 0, unknown_calls: 1, reason_code: 'service-restarted' },
    { status: 'unresolved', known_calls: 7, unknown_calls: 2, reason_code: 'service-restarted' }
  ];
  const ceilings = [null, 1, 10, 18, 25, 36, 50];
  const candidates = [
    { test: 't', kind: 'initial', requested_max_calls: 18, restart_used: false, prior_reason_code: null },
    { test: 't', kind: 'restart-replacement', requested_max_calls: 18, restart_used: false, prior_reason_code: 'service-restarted' },
    { test: 't', kind: 'restart-replacement', requested_max_calls: 18, restart_used: true, prior_reason_code: 'service-restarted' },
    { test: 't', kind: 'restart-replacement', requested_max_calls: 18, restart_used: false, prior_reason_code: 'provider-error' }
  ];

  let checked = 0;
  for (const max_total_calls of ceilings) {
    for (const single_attempt of [false, true]) {
      for (const a1 of attemptStates) {
        for (const a2 of attemptStates) {
          for (const candidate of candidates) {
            checked += 1;
            const rows = [
              { test: 'a', max_calls: 18, restart_used: false, attempts: [{ id: '1', kind: 'initial', requested_max_calls: 18, ...a1 }] },
              { test: 'b', max_calls: 12, restart_used: false, attempts: [{ id: '2', kind: 'initial', requested_max_calls: 12, ...a2 }] }
            ];
            const out = evaluateCheckBudget({
              max_total_calls,
              single_attempt,
              unresolved_prior_reservations: { count: 1, reserved_calls: 14 },
              rows,
              candidate
            });

            // Invariant 1: Prior reservations stay separate from current batch committed_calls.
            assert.deepEqual(out.plan.unresolved_prior_reservations, { count: 1, reserved_calls: 14 });
            assert.equal(out.accounting.committed_calls,
              out.accounting.consumed_known + out.accounting.unresolved_reserved + out.accounting.in_flight_reserved);

            // Invariant 2: Unresolved attempts never contribute 0; they reserve at least requested_max_calls.
            const expectedUnresolvedFloor = (a1.status === 'unresolved' ? 18 : 0) + (a2.status === 'unresolved' ? 12 : 0);
            assert.ok(out.accounting.unresolved_reserved >= expectedUnresolvedFloor);

            // Invariant 3: Replacement safety rules hold unconditionally.
            if (candidate.kind === 'restart-replacement') {
              if (candidate.prior_reason_code !== 'service-restarted' || candidate.restart_used || single_attempt) {
                assert.equal(out.decision.action, 'refuse-replacement');
                assert.equal(out.decision.effective_max_calls, 0);
                assert.equal(out.decision.retain_prior_uncertainty, true);
              }
            }

            // Invariant 4: Conservation — sending never exceeds max_total_calls when bounded.
            if (out.decision.action === 'send') {
              assert.ok(out.decision.effective_max_calls >= 1 && out.decision.effective_max_calls <= candidate.requested_max_calls);
              if (max_total_calls !== null) {
                assert.ok(out.accounting.committed_calls + out.decision.effective_max_calls <= max_total_calls,
                  `budget exceeded: committed=${out.accounting.committed_calls} + send=${out.decision.effective_max_calls} > ${max_total_calls}`);
              }
            }

            // Invariant 5: Liveness — wait occurs only when in-flight settlement can strictly increase remaining allowance.
            if (out.decision.action === 'wait') {
              assert.ok(max_total_calls !== null);
              assert.ok(out.accounting.in_flight_reserved > 0);
              const permanent = out.accounting.consumed_known + out.accounting.unresolved_reserved;
              assert.ok(Math.max(0, max_total_calls - permanent) > out.accounting.remaining_calls);
            }
          }
        }
      }
    }
  }
  assert.equal(checked, ceilings.length * 2 * attemptStates.length * attemptStates.length * candidates.length);
});
