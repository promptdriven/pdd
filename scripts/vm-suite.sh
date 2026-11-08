#!/usr/bin/env bash
# Run on pdd-vm: scripts/vm-suite.sh <full commit SHA>. Logs stay outside the repo.
# The suite waits for its turn in vm-suite-lock.sh next to this script. See its header.
set -euo pipefail
if [[ $# != 1 || ! $1 =~ ^[0-9a-fA-F]{40}$ ]]; then
  echo 'Usage: scripts/vm-suite.sh <full commit SHA>' >&2
  exit 2
fi
requested=${1,,}
lock_runner="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/vm-suite-lock.sh"
if [[ ! -x $lock_runner ]]; then
  echo "vm-suite: lock runner not found or not executable: $lock_runner" >&2
  exit 1
fi
"$lock_runner" --check
run_dir=$(mktemp -d "${TMPDIR:-/tmp}/pdd-vm-suite.XXXXXX")
echo "VM suite logs: $run_dir"
trap 'rm -rf "$run_dir/checkout" "$run_dir/home" "$run_dir/state"' EXIT
git init --quiet "$run_dir/checkout"
cd "$run_dir/checkout"
git remote add origin https://github.com/promptdriven/pdd.git
git fetch --quiet --no-tags --depth=1 origin "$requested"
git checkout --quiet --detach FETCH_HEAD
tested=$(git rev-parse --verify HEAD)
test "$tested" = "$requested"
test -z "$(git status --porcelain)"
npm ci --ignore-scripts --no-audit --no-fund
mkdir "$run_dir/home" "$run_dir/state"
printf -v suite 'env HOME=%q PDD_STATE_DIR=%q POCKET_BROWSER_BIN=/usr/bin/google-chrome node --test --test-reporter=tap --test-concurrency=4 test/*.test.mjs' "$run_dir/home" "$run_dir/state"
suite_result=0
SUITE="$suite" "$lock_runner" > "$run_dir/suite.log" 2>&1 || suite_result=$?

# Only Node's complete final top-level TAP footer can supply published counts.
node --input-type=module - "$run_dir/suite.log" > "$run_dir/counts" <<'NODE'
import { readFileSync } from 'node:fs';
const output = readFileSync(process.argv[2], 'utf8').replace(/\r/g, '');
const footer = output.slice(output.lastIndexOf('\n# tests ') + 1);
const match = footer.match(/^# tests (\d+)\n# suites \d+\n# pass (\d+)\n# fail (\d+)\n# cancelled (\d+)\n# skipped (\d+)\n# todo (\d+)\n# duration_ms [\d.]+(?:\n|$)/);
const counts = match?.slice(1).map(Number);
if (!counts || !counts.every(Number.isSafeInteger) || counts[0] < 1 || counts[0] !== counts.slice(1).reduce((a, b) => a + b, 0)) {
  console.error('No complete final TAP totals; no vm-suite status posted.');
  process.exit(1);
}
console.log(counts.join(' '));
NODE
read -r total passed failed cancelled skipped todo < "$run_dir/counts"
state=failure
if [[ $suite_result == 0 && $failed == 0 && $cancelled == 0 ]]; then
  state=success
fi
# HOME and authentication remain the caller's, not the isolated suite's.
gh api --method POST "repos/promptdriven/pdd/statuses/$tested" \
  -f context=vm-suite -f state="$state" \
  -f description="$passed/$total, $failed failed" > "$run_dir/status.json"
test "$state" = success
