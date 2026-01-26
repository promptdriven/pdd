"""Example usage of pdd.server.routes.session for remote session status endpoints.

This module provides REST API endpoints to query the current server's
remote session registration status with PDD Cloud.
"""
from __future__ import annotations

from datetime import datetime, timezone
from typing import Optional

from fastapi import APIRouter
from pydantic import BaseModel


# Router setup with prefix and tags
router = APIRouter(prefix="/api/v1/session", tags=["session"])


class RemoteSessionInfo(BaseModel):
    """Response model for session info endpoint."""

    session_id: Optional[str] = None
    cloud_url: Optional[str] = None
    registered: bool = False
    registered_at: Optional[datetime] = None


@router.get("/info", response_model=RemoteSessionInfo)
async def get_session_info() -> RemoteSessionInfo:
    """
    Get the current remote session registration status.

    Returns information about whether this server instance is registered
    with PDD Cloud for remote access.

    Returns:
        RemoteSessionInfo with registration status and cloud URL if registered
    """
    ...


# Example usage:
#
# from pdd.remote_session import get_active_session_manager
#
# # Get active session manager (if any)
# manager = get_active_session_manager()
# if manager and manager.session_id:
#     return RemoteSessionInfo(
#         session_id=manager.session_id,
#         cloud_url=manager.cloud_url,
#         registered=True,
#         registered_at=datetime.now(timezone.utc),
#     )
# else:
#     return RemoteSessionInfo(registered=False)
