"""
Subprocess runner module for PDD CLI commands.

This module provides functionality to execute PDD CLI commands as external subprocesses,
with proper handling of timeouts, output capture, and error management.
"""

import asyncio
import dataclasses
import logging
import shutil
import subprocess
import os
from typing import List, Optional

try:
    from .api_key_check import ensure_api_keys
except ImportError:
    # If the module doesn't exist yet, define a simple version of the function
    def ensure_api_keys() -> bool:
        return True

logger = logging.getLogger(__name__)

@dataclasses.dataclass
class PddResult:
    """Represents the result of a PDD CLI command execution."""
    success: bool
    stdout: str
    stderr: str
    exit_code: int

async def run_pdd_command(cmd_list: List[str], timeout: int = 900) -> PddResult:
    """
    Executes a PDD CLI command as an asynchronous subprocess.

    Args:
        cmd_list: A list representing the command and its arguments (e.g., ['pdd', 'generate', ...]).
        timeout: Maximum execution time in seconds.

    Returns:
        A PddResult object containing the execution outcome.

    Raises:
        FileNotFoundError: If the 'pdd' executable cannot be found.
    """
    if not cmd_list:
        logger.error("Empty command list provided")
        return PddResult(
            success=False,
            stdout="",
            stderr="Empty command list provided",
            exit_code=-2
        )
    
    # Simplified environment logging
    logger.info(f"Using PATH: {os.environ.get('PATH', 'Not Set')[:100]}...")
    logger.info(f"Using PYTHONPATH: {os.environ.get('PYTHONPATH', 'Not Set')}")
    if 'OPENAI_API_KEY' in os.environ:
        logger.info("OPENAI_API_KEY is set")
    if 'ANTHROPIC_API_KEY' in os.environ:
        logger.info("ANTHROPIC_API_KEY is set")
    
    # Find pdd executable
    try:
        pdd_executable = shutil.which('pdd')
        if not pdd_executable:
            logger.error("PDD CLI executable not found in PATH")
            return PddResult(
                success=False,
                stdout="",
                stderr="PDD CLI executable ('pdd') not found in PATH. Please install it with: pip install pdd-cli",
                exit_code=127
            )
    except Exception as e:
        logger.exception(f"Error finding pdd executable: {str(e)}")
        return PddResult(
            success=False,
            stdout="",
            stderr=f"Error finding pdd executable: {str(e)}",
            exit_code=1
        )

    # Replace 'pdd' with the full path
    cmd_list[0] = pdd_executable
    command_str = ' '.join(cmd_list)  # For logging purposes
    logger.info("Running PDD command: %s", command_str)
    logger.info("Using PDD executable at: %s", pdd_executable)
    logger.info("Command timeout set to %d seconds", timeout)

    process: Optional[asyncio.subprocess.Process] = None
    
    try:
        # Start the process
        logger.info("Starting subprocess...")
        process = await asyncio.create_subprocess_exec(
            *cmd_list,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            env=os.environ.copy()
        )
        
        # Wait for the process to complete
        logger.info("Waiting for process to complete...")
        try:
            stdout_bytes, stderr_bytes = await asyncio.wait_for(
                process.communicate(), timeout=timeout
            )
            
            # Decode the output
            stdout = stdout_bytes.decode('utf-8', errors='replace')
            stderr = stderr_bytes.decode('utf-8', errors='replace')
            exit_code = process.returncode
            
            # Log completion
            logger.info(f"Process completed with exit code: {exit_code}")
            
            # Return result
            if exit_code == 0:
                return PddResult(success=True, stdout=stdout, stderr=stderr, exit_code=exit_code)
            else:
                return PddResult(success=False, stdout=stdout, stderr=stderr, exit_code=exit_code)
                
        except asyncio.TimeoutError:
            logger.error(f"Process timed out after {timeout} seconds")
            
            # Try to kill the process
            if process and process.returncode is None:
                try:
                    process.kill()
                except Exception as e:
                    logger.error(f"Error killing process: {str(e)}")
            
            return PddResult(
                success=False,
                stdout="",
                stderr=f"Command timed out after {timeout} seconds",
                exit_code=-1
            )
            
    except Exception as e:
        logger.exception(f"Error running command: {str(e)}")
        return PddResult(
            success=False,
            stdout="",
            stderr=f"Error running command: {str(e)}",
            exit_code=-1
        )

async def _handle_timeout(process: asyncio.subprocess.Process, timeout: int) -> PddResult:
    """Helper function to handle process timeout and cleanup."""
    if process is None:
        return PddResult(
            success=False,
            stdout="",
            stderr=f"Command timed out after {timeout} seconds but process reference was lost.",
            exit_code=-1
        )
        
    try:
        # Try graceful termination first
        if process.returncode is None:
            process.terminate()
            try:
                await asyncio.wait_for(process.wait(), timeout=5)
            except asyncio.TimeoutError:
                logger.warning("Failed to terminate timed-out process gracefully, attempting kill")
                try:
                    process.kill()
                    await process.wait()
                except ProcessLookupError:
                    pass  # Process already gone
                except Exception as kill_err:
                    logger.error("Error killing process: %s", kill_err)
    except ProcessLookupError:
        pass  # Process already gone
    except Exception as cleanup_err:
        logger.error("Error during process cleanup: %s", cleanup_err)

    return PddResult(
        success=False,
        stdout="",
        stderr=f"Command timed out after {timeout} seconds.",
        exit_code=-1  # Distinct code for timeout
    )