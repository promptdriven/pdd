import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  resolveCodexSeatNotice,
  summarizeCodexRuntimeStatus,
} from '../src/accounts/codex-seat-visibility.mjs';

function mulberry32(seed) {
  let state = seed >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function hasControlChar(text) {
  for (let i = 0; i < text.length; i += 1) {
    const code = text.charCodeAt(i);
    if (code < 0x20 || code === 0x7f) return true;
  }
  return false;
}

const EXPECTED_LEASE_KEYS = [
  'access_type',
  'account_id',
  'auto_rotate',
  'expires_at',
  'label',
  'lease_id',
  'live_sessions',
  'mode',
  'owner_login',
  'pinned',
];

test('formal finite-grid invariants: resolveCodexSeatNotice precedence, single-line safety, and rotation/access consistency', () => {
  const argVectors = [
    { args: [], expectedClass: 'interactive' },
    { args: ['resume', '--last'], expectedClass: 'interactive' },
    { args: ['fork'], expectedClass: 'interactive' },
    { args: ['-m', 'gpt-5.4', 'explain the bug'], expectedClass: 'interactive' },
    { args: ['-C', 'exec', '-p', 'review'], expectedClass: 'interactive' },
    { args: ['--format', 'text'], expectedClass: 'interactive' },
    { args: ['--', 'exec', '--json'], expectedClass: 'interactive' },
    { args: ['exec', 'hi'], expectedClass: 'non_interactive_subcommand' },
    { args: ['exec', '--json', 'hi'], expectedClass: 'non_interactive_subcommand' },
    { args: ['--json', 'exec', 'hi'], expectedClass: 'non_interactive_subcommand' },
    { args: ['app-server'], expectedClass: 'non_interactive_subcommand' },
    { args: ['mcp-server'], expectedClass: 'non_interactive_subcommand' },
    { args: ['--json'], expectedClass: 'machine_output_flag' },
    { args: ['resume', '--json'], expectedClass: 'machine_output_flag' },
    { args: ['-o', 'final.txt'], expectedClass: 'machine_output_flag' },
    { args: ['-o=final.txt'], expectedClass: 'machine_output_flag' },
    { args: ['--output-schema=s.json'], expectedClass: 'machine_output_flag' },
    { args: ['--output-format', 'json'], expectedClass: 'machine_output_flag' },
  ];

  const accessVariants = [
    { isOwner: true, ownerLogin: 'alice', expectedTag: 'owner' },
    { isOwner: false, ownerLogin: 'bob', expectedTag: 'shared by bob' },
    { isOwner: false, ownerLogin: null, expectedTag: 'shared' },
    { isOwner: null, ownerLogin: 'ignored', expectedTag: null },
  ];

  let checked = 0;
  for (const isInteractiveTty of [false, true]) {
    for (const vec of argVectors) {
      for (const pinned of [false, true]) {
        for (const autoRotate of [null, false, true]) {
          for (const access of accessVariants) {
            const seat = {
              label: 'cx4',
              pinned,
              ...(autoRotate !== null ? { autoRotate } : {}),
              ...(access.isOwner !== null ? { isOwner: access.isOwner } : {}),
              ...(access.ownerLogin !== null ? { ownerLogin: access.ownerLogin } : {}),
            };
            const res = resolveCodexSeatNotice({ codexArgs: vec.args, isInteractiveTty, seat });
            checked += 1;

            // Strict reason & printing precedence invariant
            if (!isInteractiveTty) {
              assert.equal(res.shouldPrint, false);
              assert.equal(res.reason, 'non_interactive_tty');
              assert.equal(res.notice, null);
              continue;
            }
            if (vec.expectedClass !== 'interactive') {
              assert.equal(res.shouldPrint, false);
              assert.equal(res.reason, vec.expectedClass);
              assert.equal(res.notice, null);
              continue;
            }

            assert.equal(res.shouldPrint, true);
            assert.equal(res.reason, 'interactive');
            assert.equal(typeof res.notice, 'string');
            assert.equal(hasControlChar(res.notice), false, 'notice must never contain control characters');

            const effectiveAutoRotate = autoRotate !== null ? autoRotate : !pinned;
            const expectedPrefix = pinned ? 'pdd-codex: pinned to "cx4" (' : 'pdd-codex: using PDD Cloud seat "cx4" (';
            const expectedRotate = effectiveAutoRotate ? 'auto-rotate on' : 'auto-rotate off';
            const expectedDetails = access.expectedTag ? `${access.expectedTag}, ${expectedRotate}` : expectedRotate;
            assert.equal(res.notice, `${expectedPrefix}${expectedDetails})`);
          }
        }
      }
    }
  }
  assert.ok(checked >= 800, `expected exhaustive grid >= 800 states, checked ${checked}`);
});

test('formal seeded PRNG fuzz (300 worlds): conservation, permutation invariance, zero secret passthrough, zero cross-seat contamination, and single-line sanitization', () => {
  const rand = mulberry32(0x3679c0de);
  const pick = arr => arr[Math.floor(rand() * arr.length)];
  const globalFlags = ['-C', '--cd', '-m', '--model', '-p', '--profile', '-c', '--config', '--color'];
  const nonInteractiveSubs = ['exec', 'e', 'review', 'app-server', 'mcp-server', 'exec-server', 'login', 'logout', 'mcp', 'features'];
  const machineFlags = ['--json', '--experimental-json', '--quiet', '-q', '-o', '--output-last-message', '--output-schema'];
  const dirtyLabels = [
    'cx4',
    'cx-own',
    'cx-shr',
    'team-cx',
    '  spaced\tlabel  ',
    '\u001b[31mred-seat\u001b[0m\nEVIL',
    'line1\r\nline2',
    '   ',
    null,
  ];
  const owners = ['alice', 'bob', 'car\rol', '\u001b[1mdave\u001b[0m\n', null];

  for (let world = 0; world < 300; world += 1) {
    // 1. Fuzz resolveCodexSeatNotice with adversarial argv and control-char inputs
    const argv = [];
    const prefixCount = Math.floor(rand() * 4);
    for (let i = 0; i < prefixCount; i += 1) {
      const f = pick(globalFlags);
      // Deliberately put non-interactive subcommand or machine flag names as VALUE operands!
      argv.push(f, pick([...nonInteractiveSubs, '--json', 'normal-val']));
    }
    const injectedSub = rand() < 0.35 ? pick(nonInteractiveSubs) : (rand() < 0.5 ? 'resume' : 'my prompt');
    if (rand() < 0.7) argv.push(injectedSub);
    const hasInjectedMachine = rand() < 0.35;
    if (hasInjectedMachine) {
      const mf = pick(machineFlags);
      argv.push(mf);
      if (mf === '-o' || mf === '--output-last-message' || mf === '--output-schema') argv.push('file.json');
    }
    if (rand() < 0.4) {
      argv.push('--', 'exec', '--json', '-prompt');
    }

    const rawSeat = {
      label: pick(dirtyLabels),
      accountId: `acc_${world}`,
      pinned: rand() < 0.5,
      autoRotate: rand() < 0.33 ? null : rand() < 0.5,
      isOwner: rand() < 0.33 ? null : rand() < 0.5,
      ownerLogin: pick(owners),
    };
    const seatBefore = structuredClone(rawSeat);
    const argvBefore = structuredClone(argv);
    const isTty = rand() < 0.75;
    const noticeRes = resolveCodexSeatNotice({ codexArgs: argv, isInteractiveTty: isTty, seat: rawSeat });

    // Immutability
    assert.deepEqual(rawSeat, seatBefore);
    assert.deepEqual(argv, argvBefore);

    // Consistency
    assert.equal(noticeRes.shouldPrint, noticeRes.notice !== null);
    if (noticeRes.notice !== null) {
      assert.equal(hasControlChar(noticeRes.notice), false, `control char leaked in world ${world}: ${JSON.stringify(noticeRes.notice)}`);
      assert.equal(noticeRes.notice.includes('\u001b'), false);
    }

    // 2. Fuzz summarizeCodexRuntimeStatus with mixed live/stale leases, secrets, and accounts
    const accountPool = [
      { account_id: 'acc_own', label: 'cx-own', provider: 'codex', is_owner: true, owner_login: 'pool-owner-serhan' },
      { account_id: 'acc_shr', label: 'cx-shr', provider: 'codex', is_owner: false, owner_login: 'pool-owner-alice' },
      { account_id: 'acc_claude_noise', label: 'cx-own', provider: 'claude', is_owner: false, owner_login: 'wrong-provider' },
    ];
    const cachedActiveCodex = { account_id: 'acc_cached_only', label: 'cached-cx', is_owner: true, owner_login: 'cached-owner' };

    const count = Math.floor(rand() * 7);
    const rawLeases = [];
    for (let i = 0; i < count; i += 1) {
      const liveChoice = pick([0, -1, 1.5, Number.NaN, 1, 2, 5]);
      const accId = pick(['acc_own', 'acc_shr', 'acc_cached_only', 'acc_unmatched', null]);
      const pinned = rand() < 0.5;
      rawLeases.push({
        mode: pinned ? 'pinned' : 'shared',
        pinned,
        lease_id: rand() < 0.8 ? `lse_${world}_${i}` : null,
        account_id: accId,
        label: pick(dirtyLabels),
        is_owner: rand() < 0.4 ? null : rand() < 0.5,
        owner_login: pick(owners),
        auto_rotate: rand() < 0.3 ? null : !pinned,
        expires_at: rand() < 0.5 ? '2026-12-01T00:00:00Z' : null,
        live_sessions: liveChoice,
        // Adversarial secret fields that must NEVER pass through:
        grant_token: 'pddg_secret_must_strip',
        access_token: 'sk-secret-must-strip',
        codex_gateway_token: 'pddg_gw_must_strip',
      });
    }

    const inputSnapshot = structuredClone({ runtimeLeases: rawLeases, accounts: accountPool, cachedActiveCodex });
    const summary = summarizeCodexRuntimeStatus({ runtimeLeases: rawLeases, accounts: accountPool, cachedActiveCodex });
    assert.deepEqual({ runtimeLeases: rawLeases, accounts: accountPool, cachedActiveCodex }, inputSnapshot, 'must not mutate inputs');

    const rt = summary.codex_runtime;
    const sumSessions = rt.leases.reduce((acc, item) => acc + item.live_sessions, 0);

    // Conservation & activation invariants
    assert.equal(rt.live_sessions, sumSessions);
    assert.equal(rt.active, rt.leases.length > 0);
    assert.equal(rt.active, rt.live_sessions > 0);
    assert.equal(summary.lines.length, rt.leases.length);

    if (!rt.active) {
      assert.equal(rt.label, null);
      assert.equal(rt.account_id, null);
      assert.equal(rt.access_type, null);
      assert.equal(rt.owner_login, null);
      assert.equal(rt.auto_rotate, null);
      assert.equal(rt.pinned, null);
      assert.equal(rt.expires_at, null);
      assert.deepEqual(summary.lines, []);
    } else {
      assert.equal(rt.label, rt.leases[0].label);
      assert.equal(rt.account_id, rt.leases[0].account_id);
      assert.equal(rt.access_type, rt.leases[0].access_type);
      assert.equal(rt.owner_login, rt.leases[0].owner_login);
      assert.equal(rt.auto_rotate, rt.leases[0].auto_rotate);
      assert.equal(rt.pinned, rt.leases[0].pinned);
      assert.equal(rt.expires_at, rt.leases[0].expires_at);
    }

    // Strict field whitelist, zero secret leakage, zero cross-seat contamination, single-line safety
    const serialized = JSON.stringify(summary);
    assert.equal(serialized.includes('pddg_'), false, 'secret grant must never appear in status output');
    assert.equal(serialized.includes('sk-secret'), false, 'access token must never appear in status output');
    assert.equal(serialized.includes('wrong-provider'), false, 'claude account must never contaminate codex runtime enrichment');

    for (let idx = 0; idx < rt.leases.length; idx += 1) {
      const lease = rt.leases[idx];
      assert.deepEqual(Object.keys(lease).sort(), EXPECTED_LEASE_KEYS);
      assert.ok(Number.isInteger(lease.live_sessions) && lease.live_sessions >= 1);
      assert.equal(hasControlChar(summary.lines[idx]), false);
      if (lease.account_id === 'acc_unmatched') {
        assert.notEqual(lease.owner_login, 'cached-owner', 'cachedActiveCodex must never contaminate unmatched account_id');
        assert.notEqual(lease.owner_login, 'pool-owner-serhan', 'conflicting account_id must never inherit cx-own owner_login via label');
        assert.notEqual(lease.owner_login, 'pool-owner-alice', 'conflicting account_id must never inherit cx-shr owner_login via label');
      }
      if (idx > 0 && rt.leases[idx - 1].mode === 'pinned') {
        assert.equal(lease.mode, 'pinned', 'shared leases must always sort before pinned leases');
      }
    }

    // Permutation invariance: reversing rawLeases produces identical deterministic output
    const reversedSummary = summarizeCodexRuntimeStatus({
      runtimeLeases: [...rawLeases].reverse(),
      accounts: accountPool,
      cachedActiveCodex,
    });
    assert.deepEqual(reversedSummary, summary);
  }
});
