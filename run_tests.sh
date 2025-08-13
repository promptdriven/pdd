#!/bin/bash

# Set the PDD_PATH environment variable
export PDD_PATH=/Users/gregtanaka/Documents/pdd

# Activate conda environment
source /opt/anaconda3/etc/profile.d/conda.sh
conda activate pdd

# Run tests
python -m pytest "$@" 