#!/usr/bin/env bash
# Generated from prompts/cli/test-suite-queue.prompt.md.
# Shared full-suite queue: machine-sized check slots, first come first served.
# Usage: cd <clone> && <pdd checkout>/scripts/vm-suite-lock.sh > <log> 2>&1
# SUITE is the command to run. Without SUITE, it runs the plain suite: npm test with Chrome.
# PDD_VM_SUITE_LOCK is the lock file that the jobs on the VM share. It must be an absolute path
# in a folder that exists. Default: ~/.local/state/pdd/vm-suite/fullsuite.lock (made if missing).
# Validation logs use PDD_STATE_DIR when nonempty; otherwise PDD_SUITE_QUEUE.state,
# or LOCK.queue.state beside the resolved lock. Logs survive child HOME/state cleanup.
# By default, an external lock/queue keeps validation state outside HOME.
# --check: check the lock folder only, then exit.
if [ -n "${PDD_VM_SUITE_LOCK:-}" ]; then
  L=$PDD_VM_SUITE_LOCK
else
  L=$HOME/.local/state/pdd/vm-suite/fullsuite.lock
  mkdir -p "$(dirname "$L")" || exit 1
fi
case $L in /*) ;; *) echo "vm-suite-lock: PDD_VM_SUITE_LOCK is not an absolute path: $L" >&2; exit 1 ;; esac
if [ ! -d "$(dirname "$L")" ] || [ ! -w "$(dirname "$L")" ]; then
  echo "vm-suite-lock: lock folder not found or not writable: $(dirname "$L")" >&2
  exit 1
fi
export PDD_STATE_DIR="${PDD_STATE_DIR:-${PDD_SUITE_QUEUE:-$L.queue}.state}"
umask 022
# The packaged queue is shared with pdd workflow suite, across repositories and profiles.
exec node "$(cd "$(dirname "${BASH_SOURCE[0]}")/../src" && pwd)/test-suite-entry.mjs" "${1:-}"
