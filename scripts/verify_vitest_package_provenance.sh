#!/usr/bin/env bash
# Verify the PR-only Package Vitest provenance before any repository command.

set -euo pipefail
umask 077

fail() {
  printf 'Package Vitest provenance rejected: predicate=%s\n' "$1" >&2
  exit 1
}

check_equal() {
  local predicate="$1"
  local expected="$2"
  local actual="$3"
  [[ "$actual" == "$expected" ]] || fail "$predicate"
}

check_nonempty() {
  local predicate="$1"
  local actual="$2"
  [[ -n "$actual" ]] || fail "$predicate"
}

check_equal "trigger-event" "pull_request" "${PDD_TRIGGER_EVENT_NAME:-}"
check_nonempty "trigger-pr-head" "${PDD_TRIGGER_PR_HEAD_SHA:-}"
check_nonempty "reviewed-head" "${PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA:-}"
check_equal \
  "trigger-head-reviewed-head" "$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA" \
  "$PDD_TRIGGER_PR_HEAD_SHA"
checked_out_head="$(git rev-parse HEAD)" || fail "checkout-head-read"
check_equal "checkout-head-trigger-head" "$PDD_TRIGGER_PR_HEAD_SHA" \
  "$checked_out_head"
check_equal "checkout-head-reviewed-head" "$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA" \
  "$checked_out_head"

for required in \
  PDD_REVIEWED_FAILURE_BASELINE_SHA PDD_REVIEWED_PROTECTED_BASE_SHA \
  PDD_REVIEWED_PRODUCER_SHA256 PDD_REVIEWED_VERIFIER_SHA256 \
  PDD_REVIEWED_PACKAGE_VERIFIER_SHA256 \
  PDD_REVIEWED_PACKAGE_PROVENANCE_SHA256 \
  PDD_REVIEW_EVIDENCE_B64 PDD_REVIEW_EVIDENCE_SHA256 \
  PDD_PINNED_RUNNER_IMAGE PDD_PINNED_RUNNER_PROVISIONER \
  PDD_PINNED_PYTHON_VERSION PDD_PINNED_NODE_VERSION \
  PDD_PINNED_VITEST_PACKAGE_SHA256 PDD_PINNED_VITEST_LOCK_SHA256
do
  check_nonempty "protected-input-${required,,}" "${!required:-}"
done

git merge-base --is-ancestor \
  "$PDD_REVIEWED_FAILURE_BASELINE_SHA" "$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA" \
  >/dev/null 2>&1 || fail "failure-baseline-ancestry"
git merge-base --is-ancestor \
  "$PDD_REVIEWED_PROTECTED_BASE_SHA" "$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA" \
  >/dev/null 2>&1 || fail "protected-base-ancestry"

actual_producer_sha256="$(sha256sum pdd/sync_core/runner.py | awk '{print $1}')" \
  || fail "producer-sha256-read"
actual_verifier_sha256="$(
  sha256sum scripts/verify_vitest_termination_evidence.py | awk '{print $1}'
)" || fail "verifier-sha256-read"
actual_package_verifier_sha256="$(
  sha256sum scripts/verify_vitest_package_attestation.py | awk '{print $1}'
)" || fail "package-verifier-sha256-read"
actual_package_provenance_sha256="$(
  sha256sum scripts/verify_vitest_package_provenance.sh | awk '{print $1}'
)" || fail "package-provenance-sha256-read"
check_equal "producer-sha256" "$PDD_REVIEWED_PRODUCER_SHA256" \
  "$actual_producer_sha256"
check_equal "verifier-sha256" "$PDD_REVIEWED_VERIFIER_SHA256" \
  "$actual_verifier_sha256"
check_equal "package-verifier-sha256" \
  "$PDD_REVIEWED_PACKAGE_VERIFIER_SHA256" \
  "$actual_package_verifier_sha256"
check_equal "package-provenance-sha256" \
  "$PDD_REVIEWED_PACKAGE_PROVENANCE_SHA256" \
  "$actual_package_provenance_sha256"

review_directory="$(mktemp -d "$RUNNER_TEMP/pdd-vitest-wheel-review.XXXXXX")" \
  || fail "review-directory-create"
chmod 700 "$review_directory" || fail "review-directory-mode"
review_evidence="$review_directory/vitest-diagnostic-review-v1.json"
set +e
printf '%s' "$PDD_REVIEW_EVIDENCE_B64" \
  | base64 --decode >"$review_evidence" 2>"$review_directory/decode-output"
review_decode_status="$?"
set -e
[[ "$review_decode_status" -eq 0 ]] || fail "review-evidence-decode"
chmod 600 "$review_evidence" || fail "review-evidence-mode"
actual_review_sha256="$(sha256sum "$review_evidence" | awk '{print $1}')" \
  || fail "review-evidence-sha256-read"
check_equal "review-evidence-sha256" "$PDD_REVIEW_EVIDENCE_SHA256" \
  "$actual_review_sha256"

check_equal "runner-image-os" "ubuntu24" "${ImageOS:-}"
check_nonempty "runner-image-version" "${ImageVersion:-}"
actual_runner_image="ubuntu-24.04/${ImageVersion}"
provisioner_capture="$review_directory/hosted-compute-agent-version"
set +e
/opt/hca/hosted-compute-agent --version >"$provisioner_capture" 2>&1
provisioner_status="$?"
set -e
[[ "$provisioner_status" -eq 0 ]] || fail "runner-provisioner-command"
parser_capture="$review_directory/provisioner-versions"
set +e
sed -n 's/^version=\([0-9]\{8\}\.[0-9]\{3\}\)$/\1/p' \
  "$provisioner_capture" >"$parser_capture" 2>&1
parser_status="$?"
set -e
[[ "$parser_status" -eq 0 ]] || fail "runner-provisioner-version-parse"
mapfile -t provisioner_versions <"$parser_capture"
[[ "${#provisioner_versions[@]}" -eq 1 ]] \
  || fail "runner-provisioner-version-count"
expected_provisioner="$review_directory/expected-provisioner-version"
printf 'version=%s\n' "${provisioner_versions[0]}" >"$expected_provisioner"
cmp -s -- "$provisioner_capture" "$expected_provisioner" \
  || fail "runner-provisioner-output-shape"
actual_provisioner="${provisioner_versions[0]}"

actual_python="$(python --version 2>&1)" || fail "python-version-command"
actual_node="$(node --version 2>&1)" || fail "node-version-command"
actual_package_sha256="$(
  sha256sum .github/toolchains/vitest/package.json | awk '{print $1}'
)" || fail "vitest-package-sha256-read"
actual_lock_sha256="$(
  sha256sum .github/toolchains/vitest/package-lock.json | awk '{print $1}'
)" || fail "vitest-lock-sha256-read"
check_equal "runner-image" "$PDD_PINNED_RUNNER_IMAGE" "$actual_runner_image"
check_equal "runner-provisioner" "$PDD_PINNED_RUNNER_PROVISIONER" \
  "$actual_provisioner"
check_equal "python-version" "Python $PDD_PINNED_PYTHON_VERSION" \
  "$actual_python"
check_equal "node-version" "v$PDD_PINNED_NODE_VERSION" "$actual_node"
check_equal "vitest-package-sha256" "$PDD_PINNED_VITEST_PACKAGE_SHA256" \
  "$actual_package_sha256"
check_equal "vitest-lock-sha256" "$PDD_PINNED_VITEST_LOCK_SHA256" \
  "$actual_lock_sha256"

review_verifier_capture="$review_directory/review-verifier-output"
set +e
python scripts/verify_vitest_termination_evidence.py \
  --review-only \
  --review-evidence "$review_evidence" \
  --review-evidence-sha256 "$PDD_REVIEW_EVIDENCE_SHA256" \
  --repository "$GITHUB_WORKSPACE" \
  --failure-baseline-sha "$PDD_REVIEWED_FAILURE_BASELINE_SHA" \
  --protected-base-sha "$PDD_REVIEWED_PROTECTED_BASE_SHA" \
  --diagnostic-head-sha "$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA" \
  --producer-sha256 "$actual_producer_sha256" \
  --verifier-sha256 "$actual_verifier_sha256" \
  --package-verifier-sha256 "$actual_package_verifier_sha256" \
  --package-provenance-sha256 "$actual_package_provenance_sha256" \
  --runner-image "$actual_runner_image" \
  --runner-provisioner "$actual_provisioner" \
  --python "${actual_python#Python }" \
  --node "${actual_node#v}" \
  --vitest-package-sha256 "$actual_package_sha256" \
  --vitest-lock-sha256 "$actual_lock_sha256" \
  --test-node 'tests/test_sync_core_runner_vitest.py::test_real_vitest_runs_copied_entrypoint_without_candidate_result_access' \
  >"$review_verifier_capture" 2>&1
review_verifier_status="$?"
set -e
[[ "$review_verifier_status" -eq 0 ]] || fail "review-verifier"

{
  echo "PDD_WHEEL_REVIEW_EVIDENCE_PATH=$review_evidence"
  echo "PDD_WHEEL_MEASURED_RUNNER_IMAGE=$actual_runner_image"
  echo "PDD_WHEEL_MEASURED_RUNNER_PROVISIONER=$actual_provisioner"
  echo "PDD_WHEEL_MEASURED_PYTHON_VERSION=${actual_python#Python }"
  echo "PDD_WHEEL_MEASURED_NODE_VERSION=${actual_node#v}"
  echo "PDD_WHEEL_MEASURED_VITEST_PACKAGE_SHA256=$actual_package_sha256"
  echo "PDD_WHEEL_MEASURED_VITEST_LOCK_SHA256=$actual_lock_sha256"
} >>"$GITHUB_ENV" || fail "github-environment-write"
