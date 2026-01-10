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
