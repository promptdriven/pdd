"""
REST API endpoints for prompt analysis and preprocessing.

Provides endpoints for preprocessing prompts and calculating token metrics
without executing commands.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Optional

from fastapi import APIRouter, Depends, HTTPException
from pydantic import BaseModel, Field

try:
    from rich.console import Console
    console = Console()
except ImportError:
    class Console:
        def print(self, *args, **kwargs):
            import builtins
            builtins.print(*args)
    console = Console()

from ..security import PathValidator, SecurityError
from ..token_counter import get_token_metrics


# Request/Response Models

class CostEstimateResponse(BaseModel):
    """Cost estimation result."""
    input_cost: float = Field(..., description="Estimated input cost in USD")
    model: str = Field(..., description="Model used for estimation")
    tokens: int = Field(..., description="Number of tokens")
    cost_per_million: float = Field(..., description="Cost per million tokens")
    currency: str = Field("USD", description="Currency code")


class TokenMetricsResponse(BaseModel):
    """Token metrics result."""
    token_count: int = Field(..., description="Number of tokens")
    context_limit: int = Field(..., description="Model context limit")
    context_usage_percent: float = Field(..., description="Percentage of context used")
    cost_estimate: Optional[CostEstimateResponse] = Field(None, description="Cost estimate if pricing available")


class PromptAnalyzeRequest(BaseModel):
    """Request to analyze a prompt file."""
    path: str = Field(..., description="Path to prompt file (relative to project root)")
    model: str = Field("claude-sonnet-4-20250514", description="Model to use for token estimation")
    preprocess: bool = Field(True, description="Whether to preprocess the prompt")
    content: Optional[str] = Field(None, description="Optional content to analyze instead of reading from file")


class PromptAnalyzeResponse(BaseModel):
    """Response from prompt analysis."""
    raw_content: str = Field(..., description="Original prompt content")
    processed_content: Optional[str] = Field(None, description="Preprocessed content (if requested)")
    raw_metrics: TokenMetricsResponse = Field(..., description="Token metrics for raw content")
    processed_metrics: Optional[TokenMetricsResponse] = Field(None, description="Token metrics for processed content")
    preprocessing_succeeded: bool = Field(True, description="Whether preprocessing succeeded")
    preprocessing_error: Optional[str] = Field(None, description="Preprocessing error if any")


class SyncStatusResponse(BaseModel):
    """Response from sync status check."""
    status: str = Field(..., description="Sync status: in_sync, prompt_changed, code_changed, conflict, never_synced")
    last_sync_timestamp: Optional[str] = Field(None, description="ISO timestamp of last sync")
    last_sync_command: Optional[str] = Field(None, description="Last sync command executed")
    prompt_modified: bool = Field(False, description="Whether prompt was modified since last sync")
    code_modified: bool = Field(False, description="Whether code was modified since last sync")
    fingerprint_exists: bool = Field(False, description="Whether a fingerprint exists")
    prompt_exists: bool = Field(False, description="Whether the prompt file exists")
    code_exists: bool = Field(False, description="Whether the code file exists")


class ModelInfo(BaseModel):
    """Information about an available LLM model."""
    model: str = Field(..., description="Full model identifier (e.g., gpt-5.1-codex-mini)")
    provider: str = Field(..., description="Model provider (e.g., OpenAI, Anthropic)")
    input_cost: float = Field(..., description="Input cost per million tokens (USD)")
    output_cost: float = Field(..., description="Output cost per million tokens (USD)")
    elo: int = Field(..., description="Coding arena ELO rating")
    context_limit: int = Field(..., description="Maximum context window size in tokens")
    max_thinking_tokens: int = Field(0, description="Maximum thinking/reasoning tokens (0 if not supported)")
    reasoning_type: str = Field("none", description="Reasoning type: none, effort, or budget")
    structured_output: bool = Field(True, description="Whether the model supports structured output")


class ModelsResponse(BaseModel):
    """Response containing available models."""
    models: list[ModelInfo] = Field(..., description="List of available models")
    default_model: str = Field(..., description="Default model name")


class MatchCheckRequest(BaseModel):
    """Request to check prompt-code match."""
    prompt_content: str = Field(..., description="Prompt/requirements content")
    code_content: str = Field(..., description="Code content to evaluate")
    strength: float = Field(0.5, description="Model strength (0-1)")


class MatchCheckResult(BaseModel):
    """Result from LLM match evaluation."""
    match_score: int = Field(..., description="Match score (0-100)")
    summary: str = Field(..., description="Summary of match analysis")
    missing: list[str] = Field(default_factory=list, description="Missing requirements")
    extra: list[str] = Field(default_factory=list, description="Extra code not in prompt")
    suggestions: list[str] = Field(default_factory=list, description="Improvement suggestions")


class MatchCheckResponse(BaseModel):
    """Response from match check endpoint."""
    result: MatchCheckResult = Field(..., description="Match evaluation result")
    cost: float = Field(..., description="LLM invocation cost in USD")
    model: str = Field(..., description="Model used for evaluation")


# Router setup
router = APIRouter(prefix="/api/v1/prompts", tags=["prompts"])

# Dependency injection placeholder
_path_validator: Optional[PathValidator] = None


def get_path_validator() -> PathValidator:
    """Dependency to get the PathValidator instance."""
    if _path_validator is None:
        raise RuntimeError("PathValidator not configured")
    return _path_validator


def set_path_validator(validator: PathValidator) -> None:
    """Configure the PathValidator instance."""
    global _path_validator
    _path_validator = validator


@router.post("/analyze", response_model=PromptAnalyzeResponse)
async def analyze_prompt(
    request: PromptAnalyzeRequest,
    validator: PathValidator = Depends(get_path_validator),
):
    """
    Analyze a prompt file: preprocess it and calculate token metrics.

    Returns both raw and processed content with their respective token counts,
    context usage percentages, and cost estimates.

    This endpoint does NOT execute any commands - it's purely for preview
    and cost estimation before running expensive operations.
    """
    try:
        abs_path = validator.validate(request.path)

        # Use provided content if available, otherwise read from file
        if request.content is not None:
            raw_content = request.content
            # Check content size (limit to 500KB)
            if len(raw_content.encode('utf-8')) > 500 * 1024:
                raise HTTPException(
                    status_code=400,
                    detail=f"Content too large for analysis (max 500KB)"
                )
        else:
            # Read from file
            if not abs_path.exists():
                raise HTTPException(status_code=404, detail=f"File not found: {request.path}")

            if abs_path.is_dir():
                raise HTTPException(status_code=400, detail=f"Cannot analyze directory: {request.path}")

            # Check file size (limit to 500KB for preprocessing)
            file_size = abs_path.stat().st_size
            if file_size > 500 * 1024:
                raise HTTPException(
                    status_code=400,
                    detail=f"File too large for analysis: {file_size} bytes (max 500KB)"
                )

            # Read raw content
            try:
                raw_content = abs_path.read_text(encoding='utf-8')
            except UnicodeDecodeError:
                raise HTTPException(status_code=400, detail="File is not a valid text file")

        # Calculate raw metrics
        pricing_csv = validator.project_root / ".pdd" / "llm_model.csv"
        raw_metrics = get_token_metrics(
            raw_content,
            model=request.model,
            pricing_csv=pricing_csv if pricing_csv.exists() else None
        )

        # Preprocess if requested
        processed_content = None
        processed_metrics = None
        preprocessing_succeeded = True
        preprocessing_error = None

        if request.preprocess:
            try:
                # Import here to avoid circular imports
                from pdd.preprocess import preprocess

                # Change to project root for relative includes to work
                original_cwd = os.getcwd()
                try:
                    os.chdir(validator.project_root)
                    processed_content = preprocess(
                        raw_content,
                        recursive=True,
                        double_curly_brackets=True
                    )
                finally:
                    os.chdir(original_cwd)

                processed_metrics_obj = get_token_metrics(
                    processed_content,
                    model=request.model,
                    pricing_csv=pricing_csv if pricing_csv.exists() else None
                )
                processed_metrics = TokenMetricsResponse(
                    token_count=processed_metrics_obj.token_count,
                    context_limit=processed_metrics_obj.context_limit,
                    context_usage_percent=processed_metrics_obj.context_usage_percent,
                    cost_estimate=CostEstimateResponse(**processed_metrics_obj.cost_estimate.to_dict())
                        if processed_metrics_obj.cost_estimate else None
                )
            except Exception as e:
                preprocessing_succeeded = False
                preprocessing_error = str(e)
                console.print(f"[yellow]Preprocessing warning: {e}[/yellow]")

        # Convert raw metrics to response model
        raw_metrics_response = TokenMetricsResponse(
            token_count=raw_metrics.token_count,
            context_limit=raw_metrics.context_limit,
            context_usage_percent=raw_metrics.context_usage_percent,
            cost_estimate=CostEstimateResponse(**raw_metrics.cost_estimate.to_dict())
                if raw_metrics.cost_estimate else None
        )

        return PromptAnalyzeResponse(
            raw_content=raw_content,
            processed_content=processed_content,
            raw_metrics=raw_metrics_response,
            processed_metrics=processed_metrics,
            preprocessing_succeeded=preprocessing_succeeded,
            preprocessing_error=preprocessing_error,
        )

    except SecurityError as e:
        raise HTTPException(status_code=403, detail=e.message)


@router.get("/sync-status", response_model=SyncStatusResponse)
async def get_sync_status(
    basename: str,
    language: str,
    validator: PathValidator = Depends(get_path_validator),
):
    """
    Get the sync status for a prompt/code pair.

    Compares current file hashes with the stored fingerprint to determine
    if the prompt and code are in sync, or if either has been modified.

    Query parameters:
        basename: The basename of the module (e.g., "calculator", "core/utils")
        language: The programming language (e.g., "python", "typescript")

    Returns:
        SyncStatusResponse with status and modification details
    """
    try:
        # Import sync utilities - these handle all the fingerprint logic
        from pdd.sync_determine_operation import (
            read_fingerprint,
            get_pdd_file_paths,
            calculate_sha256,
        )

        # Change to project root for proper path resolution
        original_cwd = os.getcwd()
        try:
            os.chdir(validator.project_root)

            # Get file paths for this module
            paths = get_pdd_file_paths(basename, language)

            # Check if files exist
            prompt_exists = paths['prompt'].exists()
            code_exists = paths['code'].exists()

            # Read fingerprint (stored hash state)
            fingerprint = read_fingerprint(basename, language)

            if not fingerprint:
                # No fingerprint - never synced
                return SyncStatusResponse(
                    status="never_synced",
                    fingerprint_exists=False,
                    prompt_exists=prompt_exists,
                    code_exists=code_exists,
                )

            # Calculate current hashes
            current_prompt_hash = calculate_sha256(paths['prompt']) if prompt_exists else None
            current_code_hash = calculate_sha256(paths['code']) if code_exists else None

            # Compare with fingerprint
            prompt_modified = (
                current_prompt_hash is not None and
                fingerprint.prompt_hash is not None and
                current_prompt_hash != fingerprint.prompt_hash
            )
            code_modified = (
                current_code_hash is not None and
                fingerprint.code_hash is not None and
                current_code_hash != fingerprint.code_hash
            )

            # Determine status
            if prompt_modified and code_modified:
                status = "conflict"
            elif prompt_modified:
                status = "prompt_changed"
            elif code_modified:
                status = "code_changed"
            else:
                status = "in_sync"

            return SyncStatusResponse(
                status=status,
                last_sync_timestamp=fingerprint.timestamp,
                last_sync_command=fingerprint.command,
                prompt_modified=prompt_modified,
                code_modified=code_modified,
                fingerprint_exists=True,
                prompt_exists=prompt_exists,
                code_exists=code_exists,
            )

        finally:
            os.chdir(original_cwd)

    except SecurityError as e:
        raise HTTPException(status_code=403, detail=e.message)
    except Exception as e:
        console.print(f"[red]Error getting sync status: {e}[/red]")
        raise HTTPException(status_code=500, detail=f"Error getting sync status: {str(e)}")


@router.get("/models", response_model=ModelsResponse)
async def get_available_models():
    """
    Get a list of available LLM models with their capabilities.

    Returns model information including:
    - Context limits
    - Thinking/reasoning token capacity
    - Pricing (input/output cost per million tokens)
    - ELO ratings
    """
    try:
        # Import here to avoid circular imports
        from pdd.llm_invoke import _load_model_data, LLM_MODEL_CSV_PATH, DEFAULT_BASE_MODEL
        from ..token_counter import MODEL_CONTEXT_LIMITS

        # Load model data from CSV
        model_df = _load_model_data(LLM_MODEL_CSV_PATH)

        # Helper to determine context limit for a model
        def get_context_limit(model_name: str) -> int:
            """Get context limit based on model name."""
            model_lower = model_name.lower()
            for prefix, limit in MODEL_CONTEXT_LIMITS.items():
                if prefix in model_lower:
                    return limit
            return MODEL_CONTEXT_LIMITS.get("default", 128000)

        # Convert DataFrame to list of ModelInfo
        models = []
        for _, row in model_df.iterrows():
            model_name = str(row.get('model', ''))
            if not model_name:
                continue

            models.append(ModelInfo(
                model=model_name,
                provider=str(row.get('provider', 'Unknown')),
                input_cost=float(row.get('input', 0)),
                output_cost=float(row.get('output', 0)),
                elo=int(row.get('coding_arena_elo', 0)),
                context_limit=get_context_limit(model_name),
                max_thinking_tokens=int(row.get('max_reasoning_tokens', 0)),
                reasoning_type=str(row.get('reasoning_type', 'none')),
                structured_output=bool(row.get('structured_output', True)),
            ))

        # Sort by ELO descending (best models first)
        models.sort(key=lambda m: m.elo, reverse=True)

        return ModelsResponse(
            models=models,
            default_model=DEFAULT_BASE_MODEL,
        )

    except Exception as e:
        console.print(f"[red]Error getting available models: {e}[/red]")
        raise HTTPException(status_code=500, detail=f"Error getting available models: {str(e)}")


@router.post("/check-match", response_model=MatchCheckResponse)
async def check_match(request: MatchCheckRequest):
    """
    Check how well code implements the requirements in a prompt using LLM judge.

    Uses llm_invoke to evaluate the match between prompt requirements and code,
    returning a score, summary, missing requirements, and suggestions.
    """
    try:
        from pdd.llm_invoke import llm_invoke

        judge_prompt = """You are a code review expert. Analyze how well the following code implements the requirements in the prompt.

PROMPT/REQUIREMENTS:
{prompt}

CODE:
{code}

Evaluate the code against the prompt requirements and respond with a JSON object containing:
- match_score: integer from 0-100 indicating how well the code matches the prompt
- summary: 1-2 sentence summary of your analysis
- missing: array of requirements from the prompt that are NOT implemented in the code
- extra: array of code features that are NOT specified in the prompt
- suggestions: array of improvement suggestions"""

        result = llm_invoke(
            prompt=judge_prompt,
            input_json={"prompt": request.prompt_content, "code": request.code_content},
            strength=request.strength,
            temperature=0.1,
            output_schema={
                "type": "object",
                "properties": {
                    "match_score": {"type": "integer", "minimum": 0, "maximum": 100},
                    "summary": {"type": "string"},
                    "missing": {"type": "array", "items": {"type": "string"}},
                    "extra": {"type": "array", "items": {"type": "string"}},
                    "suggestions": {"type": "array", "items": {"type": "string"}}
                },
                "required": ["match_score", "summary"]
            }
        )

        # Parse result - it might be a string or dict depending on model
        llm_result = result.get('result', {})
        if isinstance(llm_result, str):
            import json
            llm_result = json.loads(llm_result)

        return MatchCheckResponse(
            result=MatchCheckResult(
                match_score=llm_result.get('match_score', 0),
                summary=llm_result.get('summary', ''),
                missing=llm_result.get('missing', []),
                extra=llm_result.get('extra', []),
                suggestions=llm_result.get('suggestions', []),
            ),
            cost=result.get('cost', 0.0),
            model=result.get('model_name', 'unknown'),
        )

    except Exception as e:
        console.print(f"[red]Error checking match: {e}[/red]")
        raise HTTPException(status_code=500, detail=f"Error checking match: {str(e)}")
