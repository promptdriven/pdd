"""Example usage of pdd.server.routes.config for server configuration endpoints.

This module provides REST API endpoints for server configuration information,
allowing the frontend to discover the cloud URL the server is using.
"""
from __future__ import annotations

from fastapi import APIRouter
from pydantic import BaseModel


# Router setup with prefix and tags
router = APIRouter(prefix="/api/v1/config", tags=["config"])


class CloudUrlResponse(BaseModel):
    """Response model for cloud URL endpoint."""

    cloud_url: str
    environment: str


@router.get("/cloud-url", response_model=CloudUrlResponse)
async def get_cloud_url() -> CloudUrlResponse:
    """
    Get the cloud functions URL that the server is configured to use.

    This ensures the frontend uses the same cloud URL as the CLI,
    preventing environment mismatches (staging vs production).

    Returns:
        CloudUrlResponse with cloud_url and environment
    """
    ...


# Example usage:
#
# # Register the router in the main app:
# from fastapi import FastAPI
# from pdd.server.routes.config import router as config_router
#
# app = FastAPI()
# app.include_router(config_router)
#
# # Frontend can then fetch configuration:
# # GET /api/v1/config/cloud-url
# # Response: {"cloud_url": "https://us-central1-pdd-prod.cloudfunctions.net", "environment": "production"}
