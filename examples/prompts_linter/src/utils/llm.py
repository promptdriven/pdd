import os
import json
import logging
import re
from typing import Optional, Dict, Any, Tuple

import litellm
from pydantic import ValidationError

# Import internal models
# Assumes src is in the python path
from src.utils.models import LLMResponse

# Configure Logger
logger = logging.getLogger(__name__)

# --- Constants ---

DEFAULT_MODELS = {
    "openai": "gpt-4o-mini",
    "google": "gemini-2.0-flash-exp",
    "anthropic": "claude-3-haiku-20240307",
}

# System Prompt: Defines the Persona and the Output Schema
SYSTEM_PROMPT = """
You are an expert PDD (Prompt Driven Development) Linter. Your task is to analyze prompt files for adherence to PDD best practices and return a strict JSON response.

### Analysis Criteria
Analyze the user's prompt for the following PDD principles:
1. **Anatomy**: Does it have clear sections for Requirements, Dependencies, Instructions, and Deliverable/Input-Output?
2. **Determinism**: Are there non-deterministic tags like <web>, <shell>, <exec>, or <run>? These reduce reliability.
3. **Modularity**: Does the prompt define multiple files? PDD requires one prompt per file/module.
4. **Context Engineering**: Are there raw code dumps? Code should be referenced via <include> tags, not pasted directly.
5. **Requirements Clarity**: Are requirements specific and testable, or vague?
6. **Attention Hierarchy**: Is critical info at the start/end (primacy/recency effect)?
7. **Atomic Instructions**: Are steps broken down atomically?
8. **Error Handling**: Does the prompt specify how to handle edge cases or failures?

### Output Schema
You must output ONLY valid JSON matching this structure:
{
  "guide_alignment_summary": "A brief summary of how well the prompt aligns with PDD principles.",
  "top_fixes": [
    {
      "title": "Short title of the fix",
      "rationale": "Why this fix is needed based on PDD",
      "priority": "High" | "Medium" | "Low"
    }
  ],
  "suggestions": [
    {
      "rule_id": "Optional rule ID if applicable",
      "title": "Specific suggestion title",
      "rationale": "Explanation",
      "before": "The specific text or pattern in the prompt causing the issue",
      "after": "The suggested replacement or improvement",
      "priority": "High" | "Medium" | "Low"
    }
  ]
}

Do not include markdown formatting (like ```json) in your response if possible, but if you do, ensure the content inside is valid JSON.
"""

# --- Helper Functions ---

def get_provider_and_model(user_model: Optional[str] = None) -> Tuple[Optional[str], Optional[str]]:
    """
    Determines the LLM provider and model to use.
    
    Priority:
    1. User override (user_model)
    2. OpenAI (if OPENAI_API_KEY present)
    3. Anthropic (if ANTHROPIC_API_KEY present)
    4. Google (if GOOGLE_API_KEY present)
    
    Returns:
        Tuple[str, str]: (provider_name, model_name)
        Tuple[None, None]: If no keys are found.
    """
    # Check for any available API key
    has_openai = os.getenv("OPENAI_API_KEY") is not None
    has_anthropic = os.getenv("ANTHROPIC_API_KEY") is not None
    has_google = os.getenv("GOOGLE_API_KEY") is not None
    
    # Requirement: If no keys are present, signal unavailable (None, None)
    if not (has_openai or has_anthropic or has_google):
        return None, None

    # 1. User Override
    if user_model:
        return "custom", user_model

    # 2. OpenAI
    if has_openai:
        return "openai", DEFAULT_MODELS["openai"]

    # 3. Anthropic
    if has_anthropic:
        return "anthropic", DEFAULT_MODELS["anthropic"]

    # 4. Google
    if has_google:
        return "google", DEFAULT_MODELS["google"]

    return None, None

def _clean_json_string(content: str) -> str:
    """
    Robustly extracts JSON from a string that might contain Markdown or extra text.
    """
    content = content.strip()
    
    # Remove markdown code blocks if present
    if content.startswith("```"):
        # Remove first line (```json or ```)
        content = re.sub(r"^```[a-zA-Z]*\n", "", content)
        # Remove last line (```)
        content = re.sub(r"\n```$", "", content)
    
    # If content still looks like it has wrapper text, find the outer braces
    if not content.startswith("{") or not content.endswith("}"):
        start_idx = content.find("{")
        end_idx = content.rfind("}")
        
        if start_idx != -1 and end_idx != -1 and end_idx > start_idx:
            content = content[start_idx : end_idx + 1]
            
    return content.strip()

# --- Main Analysis Function ---

def analyze_prompt(prompt_text: str, config: Optional[Dict[str, Any]] = None) -> Optional[LLMResponse]:
    """
    Analyzes a prompt using an LLM to detect PDD violations and suggest improvements.
    
    This function is designed to be "safe" - it will never raise an exception.
    If any part of the process fails (auth, network, parsing), it logs the error
    and returns None, allowing the caller to fall back to heuristics.

    Args:
        prompt_text: The raw content of the prompt file.
        config: Optional dictionary for overrides (timeout, model, max_retries).

    Returns:
        Optional[LLMResponse]: A structured object containing the analysis, or None on failure.
    """
    if config is None:
        config = {}

    # 1. Configuration Extraction
    user_model = config.get("model")
    timeout = config.get("timeout", 20)  # Default 20s
    max_retries = config.get("max_retries", 2) # Default 2 retries

    # 2. Provider/Model Resolution
    provider, model = get_provider_and_model(user_model)
    
    if not provider or not model:
        logger.warning("LLM Analysis skipped: No API keys detected (OPENAI, ANTHROPIC, GOOGLE).")
        return None

    logger.info(f"Starting LLM analysis using model: {model}")

    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": f"Analyze this prompt:\n\n{prompt_text}"}
    ]

    # 3. Prepare Litellm Arguments
    kwargs = {
        "model": model,
        "messages": messages,
        "temperature": 0.1, # Low temperature for deterministic JSON
        "max_tokens": 2000, # High budget to prevent JSON truncation
        "timeout": timeout,
        "num_retries": max_retries,
    }

    # Only use json_object mode for GPT models to avoid errors with other providers
    if "gpt" in model.lower():
        kwargs["response_format"] = {"type": "json_object"}

    # 4. Execution with Safety Net
    try:
        response = litellm.completion(**kwargs)
        
        raw_content = response.choices[0].message.content
        
        if not raw_content:
            logger.warning("LLM returned empty content.")
            return None

        # 5. Clean and Parse JSON
        cleaned_content = _clean_json_string(raw_content)
        
        try:
            data = json.loads(cleaned_content)
        except json.JSONDecodeError as e:
            logger.warning(f"LLM failed to return valid JSON. Error: {e}")
            logger.debug(f"Raw content received: {raw_content[:500]}...") # Log snippet for debug
            return None

        # 6. Validate against Schema
        try:
            validated_response = LLMResponse(**data)
            return validated_response
        except ValidationError as e:
            logger.warning(f"LLM response did not match expected schema: {e}")
            return None

    # 7. Exception Handling
    except litellm.exceptions.AuthenticationError:
        logger.warning(f"Authentication failed for model {model}. Check your API key.")
        return None
    except litellm.exceptions.Timeout:
        logger.warning(f"LLM request timed out after {timeout} seconds.")
        return None
    except litellm.exceptions.RateLimitError:
        logger.warning("LLM rate limit exceeded.")
        return None
    except Exception as e:
        logger.warning(f"Unexpected error during LLM analysis: {str(e)}")
        return None