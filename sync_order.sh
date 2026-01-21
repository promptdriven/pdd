#!/bin/bash
#
# PDD Sync Order Script
# Generated: 2026-01-20T21:24:16.608201
# Total Modules: 4
#

set -e  # Exit immediately if a command exits with a non-zero status

cd /Users/gregtanaka/Documents/pdd_cloud/pdd/.pdd/worktrees/change-issue-343

echo "[1/4] Syncing agentic_change_step7_architecture..."
pdd sync agentic_change_step7_architecture

echo "[2/4] Syncing agentic_change_step6_devunits..."
pdd sync agentic_change_step6_devunits

echo "[3/4] Syncing agentic_change_step9_implement..."
pdd sync agentic_change_step9_implement

echo "[4/4] Syncing agentic_change_step8_analyze..."
pdd sync agentic_change_step8_analyze
