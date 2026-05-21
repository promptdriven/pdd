#!/usr/bin/env bash
# Shared artifact helpers for strict A/B pipeline (sourced, not executed alone).

artifact_init_dirs() {
    local base="${1:-reports}"
    mkdir -p \
        "$base/artifacts" \
        "$base/artifacts/src" \
        "$base/artifacts/tests" \
        "$base/diffs"
}

artifact_save() {
    local src="$1"
    local rel_dst="$2"
    local base="${3:-reports}"
    if [[ ! -f "$src" ]]; then
        echo "artifact_save: missing source file: $src" >&2
        return 1
    fi
    local dst="$base/artifacts/$rel_dst"
    mkdir -p "$(dirname "$dst")"
    cp -f "$src" "$dst"
    echo "  saved artifact: $base/artifacts/$rel_dst"
}

artifact_diff() {
    local left="$1"
    local right="$2"
    local rel_name="$3"
    local label_left="${4:-$(basename "$left")}"
    local label_right="${5:-$(basename "$right")}"
    local base="${6:-reports}"
    if [[ ! -f "$left" || ! -f "$right" ]]; then
        echo "artifact_diff: missing input ($left or $right)" >&2
        return 1
    fi
    local dst="$base/diffs/$rel_name"
    mkdir -p "$(dirname "$dst")"
    diff -u \
        --label "$label_left" \
        --label "$label_right" \
        "$left" "$right" >"$dst" || true
    local hunks
    hunks="$(grep -c '^@@' "$dst" 2>/dev/null || echo 0)"
    echo "  wrote diff: $base/diffs/$rel_name ($hunks hunk(s))"
}
