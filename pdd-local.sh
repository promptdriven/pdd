#!/bin/bash
# Wrapper script to run local development version of PDD

# Get the directory this script is in
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PYTHONPATH="$PYTHONPATH:$SCRIPT_DIR"


# Dynamically find the pdd conda environment Python
if command -v conda &> /dev/null; then
    # Get the path to the pdd environment's Python
    PDD_PYTHON=$(conda run -n pdd which python 2>/dev/null)
    if [ -z "$PDD_PYTHON" ]; then
        # If conda run fails, try to find it in conda info
        CONDA_PREFIX=$(conda info --envs | grep "^pdd " | awk '{print $2}')
        if [ -n "$CONDA_PREFIX" ]; then
            PDD_PYTHON="$CONDA_PREFIX/bin/python"
        fi
    fi
else
    PDD_PYTHON=""
fi

if [ -n "$PDD_PYTHON" ] && [ -f "$PDD_PYTHON" ]; then
    exec "$PDD_PYTHON" -c "from pdd.cli import cli; cli()" "$@"
else
    # Fallback to previous behavior
    if command -v python3 &> /dev/null; then
        exec python3 -c "from pdd.cli import cli; cli()" "$@"
    elif command -v python &> /dev/null; then
        exec python -c "from pdd.cli import cli; cli()" "$@"
    else
        echo "Error: Neither python3 nor python found in PATH" >&2
        exit 127
    fi
fi