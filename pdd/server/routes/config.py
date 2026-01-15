"""Configuration routes for PDD Server.

Provides endpoints for server configuration and environment information.
"""
from __future__ import annotations

from fastapi import APIRouter
from pydantic import BaseModel

from pdd.core.cloud import CloudConfig


router = APIRouter(prefix="/api/v1/config", tags=["config"])


class CloudUrlResponse(BaseModel):
    """Response model for cloud URL."""

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
    import os

    cloud_url = CloudConfig.get_base_url()
    environment = os.environ.get("PDD_ENV", "production")

    return CloudUrlResponse(
        cloud_url=cloud_url,
        environment=environment
    )
