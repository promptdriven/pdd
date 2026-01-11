from __future__ import annotations

from . import auth
from . import files
from . import commands
from . import prompts
from .auth import router as auth_router
from .files import router as files_router
from .commands import router as commands_router
from .websocket import router as websocket_router
from .prompts import router as prompts_router

__all__ = [
    "auth",
    "files",
    "commands",
    "prompts",
    "auth_router",
    "files_router",
    "commands_router",
    "websocket_router",
    "prompts_router",
]