#!/bin/bash
# PDD Workflow with Infisical secrets
# Usage: ./scripts/pdd_with_infisical.sh <component_name> [additional_args]

set -e

# Get the directory of this script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Source the environment setup
source "$SCRIPT_DIR/setup_env_from_infisical.sh"

# Check if component name is provided
if [ $# -eq 0 ]; then
    echo "Usage: $0 <component_name> [additional_args]"
    echo "Example: $0 utils"
    echo "Example: $0 utils --clean --no-log"
    exit 1
fi

COMPONENT_NAME="$1"
shift  # Remove component name from arguments

# Change to project root
cd "$PROJECT_ROOT"

echo "🚀 Running PDD workflow for component: $COMPONENT_NAME"
echo "📁 Working directory: $(pwd)"
echo "🔐 Environment loaded from Infisical"

# Run the PDD workflow script with all remaining arguments
python3 Scripts/PDD_workflow.py "$COMPONENT_NAME" "$@"