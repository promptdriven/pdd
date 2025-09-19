# edit_file_tool/claude_api.py

"""
This module encapsulates all interactions with the Anthropic Claude API.

It provides a high-level async interface for sending prompts and receiving
responses, abstracting away the underlying HTTP and SDK details. It handles
model selection, tool registration, prompt caching, and cost tracking.
"""

import asyncio
import logging
import os
import re
from typing import Any, Dict, List, Optional, Set, Tuple, TypedDict

import anthropic
from anthropic.types import Message
from dotenv import load_dotenv

from edit_file_tool.think_tool import ThinkTool
from edit_file_tool.utils import APIError, get_logger, retry

# ==============================================================================
# 1. Module Setup and Configuration
# ==============================================================================

log = get_logger(__name__)

# Load .env file if it exists. `override=False` prevents overwriting existing env vars.
load_dotenv(override=False)

# --- Type Definitions ---

class CostInfo(TypedDict):
    """A TypedDict for structuring cost information for an API call."""
    model: str
    input_tokens: int
    output_tokens: int
    cache_creation_tokens: int
    cache_read_tokens: int
    total_cost: float


# --- Model and Tool Configuration ---

DEFAULT_MODEL = "claude-3-5-sonnet-20240620"

# Model pricing per million tokens (USD), based on prompt requirements.
# Cache read rate is 10% of the standard input rate.
_MODEL_PRICES = {
    "claude-3-opus-20240229": {"input": 15.00, "output": 75.00},
    "claude-3-sonnet-20240229": {"input": 3.00, "output": 15.00},
    # "claude-3-haiku-20240307" is intentionally omitted to test fallback pricing
    "claude-3-5-sonnet-20240620": {"input": 3.00, "output": 15.00},
    # Hypothetical future models from README/docs
    "claude-3-7-sonnet-20250219": {"input": 3.00, "output": 15.00},
}

MODEL_PRICES: Dict[str, Dict[str, float]] = {}
for model, prices in _MODEL_PRICES.items():
    input_price = prices["input"]
    MODEL_PRICES[model] = {
        "input": input_price,
        "output": prices["output"],
        "cache_read": input_price * 0.10,
    }

# Base schema for the text_editor tool. Different versions only change the name.
_TEXT_EDITOR_TOOL_SCHEMA_BASE = {
    "description": "A tool for editing text files. It can view, replace, insert, create, and undo edits.",
    "input_schema": {
        "type": "object",
        "properties": {
            "command": {
                "type": "string",
                "enum": ["view", "str_replace", "insert", "create", "undo_edit"],
                "description": "The edit operation to perform."
            },
            "path": {
                "type": "string",
                "description": "The path to the file to edit."
            },
            "old_str": {
                "type": "string",
                "description": "The string to be replaced (for str_replace)."
            },
            "new_str": {
                "type": "string",
                "description": "The new string to insert or replace with."
            },
            "insert_line": {
                "type": "integer",
                "description": "The 0-indexed line number for insertions."
            },
        },
        "required": ["command", "path"]
    }
}

# Define the specific tool versions
TEXT_EDITOR_TOOL_DEFINITIONS = {
    "text_editor_20250728": {
        "name": "text_editor_20250728",
        **_TEXT_EDITOR_TOOL_SCHEMA_BASE
    },
    "text_editor_20250124": {
        "name": "text_editor_20250124",
        **_TEXT_EDITOR_TOOL_SCHEMA_BASE
    },
    "text_editor_20241022": {
        "name": "text_editor_20241022",
        **_TEXT_EDITOR_TOOL_SCHEMA_BASE
    },
}

# Map models to their supported text editor tool definition.
# This structure is required for backward compatibility with core.py.
MODEL_TO_TEXT_EDITOR_TOOL: Dict[str, Dict[str, Any]] = {
    "claude-3-opus-20240229": TEXT_EDITOR_TOOL_DEFINITIONS["text_editor_20250728"],
    "claude-3-sonnet-20240229": TEXT_EDITOR_TOOL_DEFINITIONS["text_editor_20250728"],
    "claude-3-haiku-20240307": TEXT_EDITOR_TOOL_DEFINITIONS["text_editor_20241022"],
    "claude-3-5-sonnet-20240620": TEXT_EDITOR_TOOL_DEFINITIONS["text_editor_20250124"],
    "claude-3-7-sonnet-20250219": TEXT_EDITOR_TOOL_DEFINITIONS["text_editor_20250124"],
}

SUPPORTED_MODELS: Set[str] = set(MODEL_TO_TEXT_EDITOR_TOOL.keys())


# ==============================================================================
# 2. API Client Initialization
# ==============================================================================

def _initialize_client() -> anthropic.AsyncAnthropic:
    """
    Initializes and returns the asynchronous Anthropic API client.

    Reads the API key from the ANTHROPIC_API_KEY environment variable.

    Returns:
        An instance of anthropic.AsyncAnthropic.

    Raises:
        ValueError: If the ANTHROPIC_API_KEY environment variable is not set.
    """
    api_key = os.getenv("ANTHROPIC_API_KEY")
    if not api_key:
        raise ValueError(
            "The ANTHROPIC_API_KEY environment variable is not set. "
            "Please set it to your Anthropic API key."
        )
    return anthropic.AsyncAnthropic(api_key=api_key)

# Initialize client at module level for reuse.
try:
    client = _initialize_client()
except ValueError as e:
    log.error(f"Failed to initialize Anthropic client: {e}")
    client = None


# ==============================================================================
# 3. Helper Functions
# ==============================================================================

def _calculate_cost(model: str, usage: anthropic.types.Usage) -> CostInfo:
    """
    Calculates the cost of an API call based on token usage and model pricing.

    Args:
        model: The name of the model used.
        usage: The usage object from the Anthropic API response.

    Returns:
        A CostInfo dictionary with a detailed cost breakdown.
    """
    prices = MODEL_PRICES.get(model)
    if not prices:
        log.warning(
            f"Model '{model}' not in pricing list. Falling back to '{DEFAULT_MODEL}' pricing."
        )
        prices = MODEL_PRICES[DEFAULT_MODEL]


    # Extract token counts, defaulting to 0 if not present or None.
    input_tokens = usage.input_tokens or 0
    output_tokens = usage.output_tokens or 0
    cache_creation_tokens = getattr(usage, 'cache_creation_input_tokens', 0) or 0
    cache_read_tokens = getattr(usage, 'cache_read_input_tokens', 0) or 0

    # Per Anthropic docs, `input_tokens` is the base count.
    # Cache tokens are separate and should not be subtracted from `input_tokens`.
    # Cost for cache creation is the same as standard input.
    # Cost for cache read is at a discounted rate.
    
    standard_input_cost = (input_tokens / 1_000_000) * prices["input"]
    cache_creation_cost = (cache_creation_tokens / 1_000_000) * prices["input"]
    cache_read_cost = (cache_read_tokens / 1_000_000) * prices["cache_read"]
    output_cost = (output_tokens / 1_000_000) * prices["output"]

    total_cost = standard_input_cost + cache_creation_cost + cache_read_cost + output_cost

    return {
        "model": model,
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "cache_creation_tokens": cache_creation_tokens,
        "cache_read_tokens": cache_read_tokens,
        "total_cost": total_cost,
    }

def _prepare_cached_messages(messages: List[Dict[str, Any]]) -> Optional[List[Dict[str, Any]]]:
    """
    Splits the initial user message into a cacheable part (file content)
    and a non-cacheable part (instructions) for prompt caching.

    Args:
        messages: The original list of messages.

    Returns:
        A new list of messages optimized for caching, or None if parsing fails.
    """
    if not messages or messages[0].get("role") != "user":
        return None

    initial_prompt = messages[0].get("content", "")
    if not isinstance(initial_prompt, str):
        return None

    # This regex is designed to parse the specific prompt structure from core.py
    match = re.search(r"(File content:\n```\n.*?\n```)", initial_prompt, re.DOTALL)
    if not match:
        return None

    file_content_block = match.group(1)
    instruction_block = initial_prompt.replace(file_content_block, "").strip()

    cached_messages = [
        {
            "role": "user",
            "content": [
                {"type": "text", "text": file_content_block, "cache_control": {"type": "ephemeral"}}
            ]
        },
        {
            "role": "user",
            "content": [{"type": "text", "text": instruction_block}]
        }
    ]
    # Append any subsequent messages from a multi-turn conversation
    cached_messages.extend(messages[1:])
    return cached_messages


# ==============================================================================
# 4. Main API Function
# ==============================================================================

@retry(max_attempts=3, backoff_factor=1.5, exceptions=(anthropic.RateLimitError, anthropic.APIConnectionError))
async def call_claude_api(
    messages: List[Dict[str, Any]],
    model: str,
    system_prompt: Optional[str] = None,
    use_cache: bool = False,
    max_tokens: int = 4096,
    temperature: float = 0.1,
) -> Tuple[Message, CostInfo]:
    """
    Calls the Anthropic Claude API with the given parameters.

    This function handles tool selection, prompt caching, retries, and cost
    calculation, providing a robust interface for other modules.

    Args:
        messages: A list of message dictionaries for the conversation.
        model: The model identifier string.
        system_prompt: An optional system prompt.
        use_cache: If True, attempts to use prompt caching for the request.
        max_tokens: The maximum number of tokens to generate.
        temperature: The sampling temperature for generation.

    Returns:
        A tuple containing the API response Message object and a CostInfo dict.

    Raises:
        APIError: If a non-retryable API error occurs.
        ValueError: If the model is not supported or the client is not initialized.
    """
    if client is None:
        raise ValueError("Anthropic client is not initialized. Check ANTHROPIC_API_KEY.")

    if model not in SUPPORTED_MODELS:
        raise ValueError(f"Model '{model}' is not supported. Supported models: {', '.join(SUPPORTED_MODELS)}")

    # Assemble the tools for the API call
    text_editor_tool = MODEL_TO_TEXT_EDITOR_TOOL.get(model, MODEL_TO_TEXT_EDITOR_TOOL[DEFAULT_MODEL])
    think_tool = ThinkTool.get_definition()
    tools = [text_editor_tool, think_tool]

    # Prepare messages for caching if requested
    api_messages = messages
    if use_cache:
        cached_messages = _prepare_cached_messages(messages)
        if cached_messages:
            log.info("Using cache-optimized message structure.")
            api_messages = cached_messages
        else:
            log.warning("Cache requested, but failed to parse initial prompt for caching. Proceeding without cache.")

    try:
        log.info(f"Calling Claude API with model: {model}")
        response = await client.messages.create(
            model=model,
            messages=api_messages,
            system=system_prompt,
            tools=tools,
            max_tokens=max_tokens,
            temperature=temperature,
        )
        log.info(f"API call successful. Stop reason: {response.stop_reason}")

        cost_info = _calculate_cost(model, response.usage)
        log.info(
            f"Cost for this call: ${cost_info['total_cost']:.4f} "
            f"(In: {cost_info['input_tokens']}, Out: {cost_info['output_tokens']}, "
            f"Cache Write: {cost_info['cache_creation_tokens']}, Cache Read: {cost_info['cache_read_tokens']})"
        )

        return response, cost_info

    except (anthropic.RateLimitError, anthropic.APIConnectionError) as e:
        # Re-raise retryable errors to be handled by the @retry decorator
        raise e
    except anthropic.APIError as e:
        # Wrap other, non-retryable API errors in our custom exception
        log.error(f"Anthropic API error: {e}", exc_info=True)
        raise APIError(f"API call failed: {e.message}", context={"status_code": e.status_code}) from e
    except Exception as e:
        # Wrap any other unexpected errors
        log.critical(f"An unexpected error occurred in call_claude_api: {e}", exc_info=True)
        raise APIError(f"An unexpected error occurred: {e}") from e
