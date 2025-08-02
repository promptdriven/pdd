#!/usr/bin/env python3
import os
import shutil
import zipfile
import sys
import glob

# Define paths
dist_dir = "/Users/gregtanaka/Documents/pdd_cloud/pdd/dist"
extract_path = "/Users/gregtanaka/Documents/pdd_cloud/pdd/dist/extracted"

# Find wheel file
wheel_files = glob.glob(os.path.join(dist_dir, "pdd_cli-*.whl"))
if not wheel_files:
    print(f"Error: No wheel files found in {dist_dir}")
    sys.exit(1)

# Use the most recent wheel file if multiple exist
wheel_path = max(wheel_files, key=os.path.getctime)
print(f"Using wheel file: {wheel_path}")

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