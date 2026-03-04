#!/bin/bash
#
# PDD Sync Order Script
# Generated: 2026-02-23T00:59:06.879331
# Total Modules: 3
#

set -e  # Exit immediately if a command exits with a non-zero status

echo "[1/3] Syncing extract_command..."
pdd sync extract_command

echo "[2/3] Syncing llm_extractor..."
pdd sync llm_extractor

echo "[3/3] Syncing content_selector..."
pdd sync content_selector
