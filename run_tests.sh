#!/bin/bash

# Set the PDD_PATH environment variable
# Set the PDD_PATH environment variable to the script's directory if not already set
export PDD_PATH="${PDD_PATH:-$(cd "$(dirname "$0")" && pwd)}"

# Activate conda environment
source /opt/anaconda3/etc/profile.d/conda.sh
conda activate pdd

# Run tests
python -m pytest "$@" 