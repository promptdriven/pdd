import uvicorn
from fastapi import FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse
from pydantic import BaseModel, Field
from typing import Dict, Optional, Any

# Internal imports based on the provided package structure
from src.backend.core.lint_engine import LintEngine
from src.backend.models.findings import LintReport
import src.backend.rules.pdd_rules  # noqa: F401

# --- Request Models ---

class LintRequest(BaseModel):
    """
    Schema for the incoming linting request.
    """
    prompt_text: str = Field(
        ..., 
        description="The raw prompt text to be analyzed.",
        example="Write a python script to scrape google."
    )
    options: Optional[Dict[str, Any]] = Field(
        default_factory=dict,
        description="Optional configuration flags for the linter (e.g., specific rule sets)."
    )

# --- Application Setup ---

app = FastAPI(
    title="PDD Prompt Linter",
    description="API for analyzing LLM prompts against PDD (Prompt Driven Development) best practices.",
    version="1.0"
)

# --- Middleware Configuration ---

# Configure CORS to allow requests from the Streamlit UI (or any origin for MVP)
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # Allow all origins for MVP development
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# --- Core Engine Initialization ---

# Initialize the LintEngine. 
# We instantiate it at the module level so rules are loaded once.
# Assuming LintEngine loads default PDD rules in its __init__.
lint_engine = LintEngine()

# --- Exception Handlers ---

@app.exception_handler(Exception)
async def global_exception_handler(request: Request, exc: Exception):
    """
    Global exception handler to ensure the API returns 500 JSON responses
    instead of crashing or leaking stack traces in production.
    """
    return JSONResponse(
        status_code=500,
        content={"detail": "Internal Server Error", "message": str(exc)},
    )

# --- Endpoints ---

@app.get("/", tags=["System"])
async def root():
    """
    Root endpoint providing API status and documentation link.
    """
    return {
        "message": "Welcome to the PDD Prompt Linter API",
        "docs_url": "/docs",
        "status": "running"
    }

@app.get("/health", tags=["System"])
async def health_check():
    """
    Simple health check endpoint for deployment probes.
    """
    return {"status": "ok"}

@app.post("/lint", response_model=LintReport, tags=["Linter"])
async def lint_prompt(request: LintRequest):
    """
    Analyzes the provided prompt text and returns a structured report of findings.
    
    - **prompt_text**: The string to analyze.
    - **options**: Optional dictionary for configuration.
    """
    try:
        # The engine handles the logic of applying rules and generating the LintReport
        report = lint_engine.lint(request.prompt_text)
        return report
    except Exception as e:
        # While the global handler catches most things, specific logic errors 
        # during linting might need context here.
        raise HTTPException(status_code=500, detail=f"Error processing prompt: {str(e)}")

# --- Execution Entry Point ---

if __name__ == "__main__":
    # Run the application using uvicorn when executed directly
    uvicorn.run("src.backend.app.main:app", host="0.0.0.0", port=8000, reload=True)