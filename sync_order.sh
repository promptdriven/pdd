#!/bin/bash
#
# PDD Sync Order Script
# Generated: 2026-01-23T13:46:23.030205
# Total Modules: 3
#

set -e  # Exit immediately if a command exits with a non-zero status

cd /Users/caijiamin/Desktop/PDD_PRIVATE/my-new-worktree/.pdd/worktrees/change-issue-367

echo "[1/3] Syncing agentic_architecture_orchestrator..."
pdd sync agentic_architecture_orchestrator

echo "[2/3] Syncing agentic_architecture..."
pdd sync agentic_architecture

echo "[3/3] Syncing generate..."
pdd sync generate
