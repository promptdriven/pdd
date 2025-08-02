#!/usr/bin/env python3
import os
import shutil
import zipfile
import sys

# Define paths
wheel_path = "/Users/gregtanaka/Documents/pdd_cloud/pdd/dist/pdd_cli-0.0.44-py3-none-any.whl"
extract_path = "/Users/gregtanaka/Documents/pdd_cloud/pdd/dist/extracted"

# Check if wheel file exists
if not os.path.exists(wheel_path):
    print(f"Error: Wheel file not found at {wheel_path}")
    sys.exit(1)

# Remove existing extracted directory
if os.path.exists(extract_path):
    print(f"Removing existing directory: {extract_path}")
    shutil.rmtree(extract_path)

# Create new extracted directory
print(f"Creating directory: {extract_path}")
os.makedirs(extract_path)

# Extract the wheel file
print(f"Extracting {wheel_path} to {extract_path}")
with zipfile.ZipFile(wheel_path, 'r') as zip_ref:
    zip_ref.extractall(extract_path)

print("Extraction complete!")

# List extracted contents
print("\nExtracted contents:")
for root, dirs, files in os.walk(extract_path):
    level = root.replace(extract_path, '').count(os.sep)
    indent = ' ' * 2 * level
    print(f"{indent}{os.path.basename(root)}/")
    subindent = ' ' * 2 * (level + 1)
    for file in files[:10]:  # Show first 10 files
        print(f"{subindent}{file}")
    if len(files) > 10:
        print(f"{subindent}... and {len(files) - 10} more files")