#!/bin/bash
#
# PDD Sync Order Script
# Generated: 2026-01-20T22:55:53.222757
# Total Modules: 4
#

set -e  # Exit immediately if a command exits with a non-zero status

cd /Users/gregtanaka/Documents/pdd_cloud/pdd/.pdd/worktrees/change-issue-332

echo "[1/4] Syncing cli..."
pdd sync cli

echo "[2/4] Syncing executor..."
pdd sync executor

echo "[3/4] Syncing agentic_test_orchestrator..."
pdd sync agentic_test_orchestrator

echo "[4/4] Syncing agentic_test..."
pdd sync agentic_test
