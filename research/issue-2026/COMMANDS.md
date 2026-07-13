# Command transcript

Accepted artifact directories are `candidate-f680c761-controlled` and `baseline-263b4925-controlled`. Earlier `candidate-f680c761` and `candidate-f680c761-final` directories were exploratory runner-development attempts and are excluded from conclusions.

## Pinned worktrees

```sh
git worktree add --detach /private/tmp/pdd-2026-candidate f680c761462160ecdaec7b550be26ea529024801
git worktree add --detach /private/tmp/pdd-2026-baseline 263b4925f1a53b3f1cfe8a15274d2a18af842c17
```

## OS network-isolated observations

The macOS Seatbelt profile SHA-256 is `5c358b8d847211333e7ba22df82d84f796b5f30a41a2682209a949d783adbd08`.

```sh
sandbox-exec -f network-deny.sb /opt/anaconda3/bin/python run_comparison.py \
  --checkout /private/tmp/pdd-2026-candidate \
  --output candidate-f680c761-controlled

sandbox-exec -f network-deny.sb /opt/anaconda3/bin/python run_comparison.py \
  --planning-only \
  --checkout /private/tmp/pdd-2026-baseline \
  --output baseline-263b4925-controlled
```

Both runner summaries record failed external TCP (`1.1.1.1:443`) and loopback TCP (`127.0.0.1:9`) probes with `PermissionError(1, 'Operation not permitted')`.

## Scrubbed hermetic tests

```sh
sandbox-exec -f /absolute/path/to/network-deny.sb \
  /usr/bin/env -i \
  PATH=/opt/anaconda3/bin:/usr/bin:/bin:/usr/sbin:/sbin \
  HOME=/absolute/path/to/test-home \
  TMPDIR=/absolute/path/to/test-tmp \
  LANG=C TERM=dumb NO_COLOR=1 \
  PDD_AUTO_UPDATE=false PDD_SUPPRESS_SETUP_REMINDER=1 \
  LITELLM_CACHE_DISABLE=1 \
  /opt/anaconda3/bin/python -m pytest -q \
  tests/test_agentic_sync_mocked_e2e.py \
  tests/test_issue_1979_sync_exit_code.py \
  --junitxml=/absolute/path/to/hermetic-candidate-f680c761.xml
```

Result: 14 passed in 65.10 seconds. The JUnit XML is committed under `artifacts/`.

Focused #1980 unit validation:

```sh
python -m pytest -q tests/test_agentic_sync.py \
  -k 'issue_named or scope_reconcil or named_modules or branch_diff'
```

Result: 6 passed, 269 deselected.

## Artifact integrity

```sh
python -m pytest -q tests/test_issue_2026_comparison_artifacts.py
python -m py_compile research/issue-2026/run_comparison.py \
  tests/test_issue_2026_comparison_artifacts.py
git diff --check
```

Result: 4 passed; compile and whitespace checks succeeded.
