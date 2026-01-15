"""
Stateless utility module to invoke Claude API via litellm with Extended Thinking support.
Returns Anthropic-formatted responses and calculated USD costs.
"""

import os
import json
import logging
from typing import List, Dict, Tuple, Any, Optional

import litellm
from litellm import BadRequestError

from edit_file_tool.cost_tracker_utility import calculate_cost

# Setup logging
logger = logging.getLogger(__name__)

# Models that support extended thinking (Claude 3.7+ and future v4)
THINKING_SUPPORTED_MODELS = ["claude-3-7", "claude-sonnet-4", "claude-opus-4"]
# Haiku models specifically do NOT support extended thinking
HAIKU_MODELS = ["haiku"]

async def invoke_with_thinking(
    messages: List[Dict[str, Any]],
    tools: List[Dict[str, Any]],
    model: str
) -> Tuple[Dict[str, Any], float]:
    """
    Invoke Claude API with thinking enabled for supported models.
    
    Args:
        messages: List of messages in OpenAI format.
        tools: List of tool definitions.
        model: Model identifier (e.g., 'anthropic/claude-3-7-sonnet-20250219').
        
    Returns:
        Tuple of (anthropic_formatted_response, cost_in_usd)
    """
    
    # 1. Determine if thinking should be enabled
    use_thinking = any(m in model.lower() for m in THINKING_SUPPORTED_MODELS) and \
                   not any(h in model.lower() for h in HAIKU_MODELS)
    
    # 2. Prepare completion parameters
    completion_kwargs = {
        "model": model,
        "messages": messages,
        "tools": tools,
        "max_tokens": 4096,
    }

    # 3. Handle Provider-Specific Configuration
    if model.startswith("vertex_ai/"):
        logger.debug(f"Using Vertex AI provider path for model: {model}")
        # Load credentials from environment
        creds_path = os.environ.get("VERTEX_CREDENTIALS")
        if creds_path and os.path.exists(creds_path):
            with open(creds_path, 'r') as f:
                completion_kwargs["vertex_credentials"] = f.read()
        
        completion_kwargs["vertex_ai_project"] = os.environ.get("VERTEX_PROJECT")
        completion_kwargs["vertex_ai_location"] = os.environ.get("VERTEX_LOCATION")
    else:
        logger.debug(f"Using Anthropic provider path for model: {model}")
        # litellm auto-detects ANTHROPIC_API_KEY

    # 4. Execute with Thinking Fallback
    try:
        if use_thinking:
            logger.debug(f"Invoking {model} with thinking budget=1024")
            # Note: litellm translates 'thinking' param for Anthropic/Vertex
            response = await litellm.acompletion(
                **completion_kwargs,
                thinking={"type": "enabled", "budget_tokens": 1024}
            )
        else:
            response = await litellm.acompletion(**completion_kwargs)
            
    except BadRequestError as e:
        if use_thinking:
            logger.warning(f"Thinking failed for {model}, retrying without thinking: {str(e)}")
            response = await litellm.acompletion(**completion_kwargs)
        else:
            raise e

    # 5. Extract Usage and Calculate Cost
    usage = response.get("usage", {})
    # Handle field name fallbacks between OpenAI/Anthropic formats in litellm
    input_tokens = usage.get("prompt_tokens", 0)
    output_tokens = usage.get("completion_tokens", 0)
    cache_write = usage.get("cache_creation_input_tokens", 0)
    cache_read = usage.get("cache_read_input_tokens", 0)

    cost_usd = calculate_cost(
        model=model.split("/")[-1], # Pass base model name to tracker
        input_tokens=input_tokens,
        output_tokens=output_tokens,
        cache_write_tokens=cache_write,
        cache_read_tokens=cache_read
    )

    # 6. Convert to Anthropic Format for core.py
    anthropic_response = _convert_to_anthropic_format(response)
    
    return anthropic_response, cost_usd

def _convert_to_anthropic_format(litellm_response: Any) -> Dict[str, Any]:
    """
    Converts litellm ModelResponse (OpenAI-like) to Anthropic-style dictionary.
    """
    message = litellm_response.choices[0].message
    content_blocks = []

    # 1. Handle Thinking Blocks (Anthropic specific)
    # litellm populates thinking_blocks for Claude 3.7+
    thinking_blocks = getattr(message, "thinking_blocks", None)
    if thinking_blocks:
        for block in thinking_blocks:
            content_blocks.append({
                "type": "thinking",
                "thinking": block.get("thinking", ""),
                "signature": block.get("signature")
            })

    # 2. Handle Text Content
    if message.content:
        content_blocks.append({
            "type": "text",
            "text": message.content
        })

    # 3. Handle Tool Calls
    if hasattr(message, "tool_calls") and message.tool_calls:
        for tool_call in message.tool_calls:
            # Convert OpenAI tool_call to Anthropic tool_use
            try:
                tool_input = json.loads(tool_call.function.arguments)
            except (json.JSONDecodeError, TypeError):
                tool_input = tool_call.function.arguments

            content_blocks.append({
                "type": "tool_use",
                "id": tool_call.id,
                "name": tool_call.function.name,
                "input": tool_input
            })

    # 4. Construct final dict
    usage = litellm_response.get("usage", {})
    return {
        "role": "assistant",
        "content": content_blocks,
        "usage": {
            "input_tokens": usage.get("prompt_tokens", 0),
            "output_tokens": usage.get("completion_tokens", 0),
            "cache_creation_input_tokens": usage.get("cache_creation_input_tokens", 0),
            "cache_read_input_tokens": usage.get("cache_read_input_tokens", 0)
        }
    }