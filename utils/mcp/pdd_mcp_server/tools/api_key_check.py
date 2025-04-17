"""
Module to check and set API keys for local mode.
"""

import os
import logging
from typing import Dict, Optional

logger = logging.getLogger(__name__)

def get_api_keys() -> Dict[str, Optional[str]]:
    """
    Get current API keys from environment variables.
    
    Returns:
        Dictionary of API key environment variables and their values.
    """
    return {
        "OPENAI_API_KEY": os.environ.get("OPENAI_API_KEY"),
        "ANTHROPIC_API_KEY": os.environ.get("ANTHROPIC_API_KEY")
    }

def has_api_keys() -> bool:
    """
    Check if any of the required API keys are set.
    
    Returns:
        True if at least one API key is set, False otherwise.
    """
    api_keys = get_api_keys()
    return any(api_keys.values())

def set_dummy_api_keys() -> None:
    """
    Set dummy API keys for testing if none are set.
    This will only set them if they're not already set.
    """
    keys_to_set = {
        "OPENAI_API_KEY": "sk-dummy-api-key-for-testing",
        "ANTHROPIC_API_KEY": "dummy-anthropic-api-key-for-testing"
    }
    
    for key, value in keys_to_set.items():
        if key not in os.environ or not os.environ[key]:
            os.environ[key] = value
            logger.warning(f"Set dummy {key} for testing purposes")

def ensure_api_keys() -> bool:
    """
    Ensure that API keys are set for local mode.
    
    Returns:
        True if API keys were already set or have been set,
        False if something went wrong.
    """
    if has_api_keys():
        logger.info("API keys are already set")
        return True
    
    try:
        set_dummy_api_keys()
        logger.info("Dummy API keys have been set for testing")
        return True
    except Exception as e:
        logger.error(f"Failed to set API keys: {e}")
        return False 