#!/usr/bin/env python
"""
Post-process wheel files to preprocess LLM prompts.

This script extracts a wheel file, preprocesses all *_LLM.prompt files
(except example_generator_LLM.prompt and generate_test_LLM.prompt),
and repackages the wheel with the preprocessed versions.
"""
import sys
import zipfile
import tempfile
import shutil
import subprocess
from pathlib import Path


def preprocess_wheel(wheel_path):
    """
    Preprocess LLM prompts in a wheel file.
    
    Args:
        wheel_path: Path to the wheel file to process
    """
    wheel_path = Path(wheel_path)
    
    if not wheel_path.exists():
        print(f"Error: Wheel file not found: {wheel_path}")
        sys.exit(1)
    
    print(f"Processing wheel: {wheel_path}")
    
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)
        
        # Extract wheel
        print("Extracting wheel...")
        with zipfile.ZipFile(wheel_path, 'r') as wheel:
            wheel.extractall(temp_path)
        
        # Find and preprocess LLM prompts
        prompts_dir = temp_path / 'pdd' / 'prompts'
        if not prompts_dir.exists():
            print(f"Error: prompts directory not found in wheel")
            sys.exit(1)
            
        exclude = {'example_generator_LLM.prompt', 'generate_test_LLM.prompt', 'auto_include_LLM.prompt'}
        
        llm_prompts = list(prompts_dir.glob('*_LLM.prompt'))
        print(f"Found {len(llm_prompts)} LLM prompt files")
        
        for prompt_file in llm_prompts:
            if prompt_file.name not in exclude:
                print(f"  Preprocessing {prompt_file.name}...")
                temp_output = prompt_file.with_suffix('.tmp')
                
                # Build preprocess command
                cmd = ['pdd', '--force', 'preprocess', '--output', str(temp_output)]
                
                # Add special flags for auto_include_LLM.prompt
                if prompt_file.name == 'auto_include_LLM.prompt':
                    cmd.extend(['--double', '--exclude', "['input_prompt','available_include']"])

                # Add special flags for agentic_update_LLM.prompt
                # The prompting guide contains code examples with curly braces that
                # would break Python's str.format() without escaping
                if prompt_file.name == 'agentic_update_LLM.prompt':
                    cmd.extend([
                        '--double',
                        '--exclude', 'prompt_path',
                        '--exclude', 'code_path',
                        '--exclude', 'test_paths'
                    ])

                cmd.append(str(prompt_file))
                
                # Run pdd preprocess
                result = subprocess.run(cmd, capture_output=True, text=True, stdin=subprocess.DEVNULL)
                
                if result.returncode == 0:
                    # Replace original with preprocessed version
                    temp_output.replace(prompt_file)
                    print("    ✓ Successfully preprocessed")
                else:
                    print(f"    ✗ Failed to preprocess {prompt_file.name}")
                    print(f"      Error: {result.stderr}")
                    # Continue with other files even if one fails
            else:
                print(f"  Skipping {prompt_file.name} (excluded from preprocessing)")
        
        # Repackage wheel
        print("Repackaging wheel...")
        new_wheel = wheel_path.with_suffix('.new')
        
        with zipfile.ZipFile(new_wheel, 'w', zipfile.ZIP_DEFLATED) as new_zip:
            # Walk through all files in the temp directory
            for file_path in temp_path.rglob('*'):
                if file_path.is_file():
                    arcname = file_path.relative_to(temp_path)
                    new_zip.write(file_path, arcname)
        
        # Replace original wheel with new one
        new_wheel.replace(wheel_path)
        print(f"✓ Successfully processed wheel: {wheel_path}")


def main():
    """Main entry point."""
    if len(sys.argv) != 2:
        print("Usage: preprocess_wheel.py <wheel_file>")
        print("       preprocess_wheel.py dist/*.whl")
        sys.exit(1)
    
    # Handle glob pattern if shell doesn't expand it
    wheel_pattern = sys.argv[1]
    wheel_files = list(Path('.').glob(wheel_pattern))
    
    if not wheel_files:
        print(f"Error: No wheel files found matching pattern: {wheel_pattern}")
        sys.exit(1)
    
    if len(wheel_files) > 1:
        print(f"Error: Multiple wheel files found: {wheel_files}")
        print("Please specify a single wheel file")
        sys.exit(1)
    
    preprocess_wheel(wheel_files[0])


if __name__ == '__main__':
    main()