#!/usr/bin/env bash
# Queue for full suites on pdd-vm: at most 3 run at a time, first come first served.
# Usage: cd <clone> && <pdd checkout>/scripts/vm-suite-lock.sh > <log> 2>&1
# SUITE is the command to run. Without SUITE, it runs the plain suite: npm test with Chrome.
# PDD_VM_SUITE_LOCK is the lock file that the jobs on the VM share. It must be an absolute path
# in a folder that exists. Default: ~/.local/state/pdd/vm-suite/fullsuite.lock (made if missing).
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
if [ "${1:-}" = --check ]; then exit 0; fi
echo "queued $(TZ=America/Los_Angeles date +%H:%M:%S) in $(pwd)"
exec 8>"$L.turn" && flock 8 || exit 1   # the queue: only the oldest waiter looks for a slot
while true; do
  for s in "$L.3" "$L.2" "$L"; do exec 9>"$s"; if flock -n 9; then break 2; fi; exec 9>&-; done
  sleep 5
done
flock -u 8; exec 8>&-                 # let the next waiter in
umask 022
echo "started $(TZ=America/Los_Angeles date +%H:%M:%S) in $(pwd)" | tee -a "$L.history"
if [ -n "${SUITE:-}" ]; then bash -c "$SUITE" < /dev/null; else POCKET_BROWSER_BIN=/usr/bin/google-chrome npm test < /dev/null; fi
rc=$?
echo "finished $(TZ=America/Los_Angeles date +%H:%M:%S) exit $rc in $(pwd)" | tee -a "$L.history"
exit $rc
