import sys
import os
import logging
from typing import Dict, Any, Optional

from fastapi import FastAPI, HTTPException, status
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, Field

# --- Path Setup ---
# Add the project root to sys.path to allow imports from 'src'
# File location: src/backend/api.py -> Root is two levels up
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# --- Imports ---
try:
    from src.utils.models import Report
    from src.utils.pipeline import lint_text, LintConfig
except ImportError as e:
    # Fallback for development environments where src might not be in path yet
    logging.error(f"Failed to import core modules: {e}")
    sys.exit(1)

# --- Configuration ---
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger("api")

# --- Data Models ---

class LintRequest(BaseModel):
    """
    DTO for the linting request.
    """
    content: str = Field(..., description="The prompt text to be linted.")
    config: Optional[Dict[str, Any]] = Field(
        default_factory=dict,
        description="Optional configuration overrides for the linter (e.g., use_llm, weights)."
    )

# --- App Initialization ---

app = FastAPI(
    title="PDD Prompt Linter API",
    description="Backend API for the PDD (Prompt Driven Development) Linter tool.",
    version="1.0.0"
)

# --- Middleware ---

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # Allow all origins for development flexibility
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# --- Endpoints ---

@app.get("/health", status_code=status.HTTP_200_OK)
async def health_check():
    """
    Simple health check endpoint to verify the service is running.
    """
    return {"status": "ok"}

@app.post("/lint", response_model=Report, status_code=status.HTTP_200_OK)
async def lint_endpoint(request: LintRequest):
    """
    Accepts a prompt and configuration, runs the linting pipeline, and returns a Report.
    """
    logger.info("Received lint request.")
    
    try:
        # 1. Prepare Configuration
        # Convert dict to LintConfig object (request.config defaults to {} if not provided)
        config = LintConfig(**request.config)

        # 2. Delegate to Pipeline
        # Note: lint_text is synchronous (CPU/Network bound).
        report = lint_text(text=request.content, config=config)
        
        logger.info(f"Linting complete. Score: {report.score}")
        return report

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Internal server error during linting: {e}", exc_info=True)
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail=f"An error occurred while processing the prompt: {str(e)}"
        )

# --- Execution ---

if __name__ == "__main__":
    # Run the app using uvicorn when executed directly
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)