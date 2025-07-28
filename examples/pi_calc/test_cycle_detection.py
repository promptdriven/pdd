#!/usr/bin/env python3
"""Test script to verify cycle detection in pdd sync."""

import subprocess
import sys
import os
import time

def test_sync_with_syntax_error():
    """Test that pdd sync detects and breaks crash-verify cycles."""
    
    # First, copy the broken example to the actual example location
    import shutil
    shutil.copy('examples/pi_calc_example_broken.py', 'examples/pi_calc_example.py')
    
    print("Testing pdd sync with syntax errors...")
    print("-" * 50)
    
    # Run pdd sync with a timeout
    start_time = time.time()
    try:
        result = subprocess.run(
            ['pdd', '--force', 'sync', 'pi_calc'],
            capture_output=True,
            text=True,
            timeout=180  # 3 minute timeout
        )
        
        elapsed = time.time() - start_time
        print(f"Command completed in {elapsed:.1f} seconds")
        print(f"Exit code: {result.returncode}")
        
        # Check output for cycle detection message
        if "Detected crash-verify cycle" in result.stdout or "Detected crash-verify cycle" in result.stderr:
            print("✅ SUCCESS: Cycle detection worked!")
            print("\nRelevant output:")
            for line in result.stdout.split('\n'):
                if 'cycle' in line.lower() or 'crash' in line or 'verify' in line:
                    print(f"  {line}")
        else:
            print("❌ FAILED: No cycle detection message found")
            print("\nFull stdout:")
            print(result.stdout[-1000:])  # Last 1000 chars
            print("\nFull stderr:")
            print(result.stderr[-1000:])  # Last 1000 chars
            
    except subprocess.TimeoutExpired:
        print(f"❌ FAILED: Command timed out after 180 seconds")
        print("This suggests the cycle detection is not working")
        
    finally:
        # Restore the working example
        shutil.copy('examples/pi_calc_example.py.bak', 'examples/pi_calc_example.py')

if __name__ == "__main__":
    # First backup the working example
    import shutil
    shutil.copy('examples/pi_calc_example.py', 'examples/pi_calc_example.py.bak')
    
    try:
        test_sync_with_syntax_error()
    finally:
        # Ensure we restore the working example
        if os.path.exists('examples/pi_calc_example.py.bak'):
            shutil.copy('examples/pi_calc_example.py.bak', 'examples/pi_calc_example.py')
            os.remove('examples/pi_calc_example.py.bak')