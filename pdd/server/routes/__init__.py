from __future__ import annotations

from . import architecture
from . import auth
from . import config
from . import files
from . import commands
from . import prompts
from .architecture import router as architecture_router
from .auth import router as auth_router
from .config import router as config_router
from .files import router as files_router
from .commands import router as commands_router
from .websocket import router as websocket_router
from .prompts import router as prompts_router

__all__ = [
    "architecture",
    "auth",
    "config",
    "files",
    "commands",
    "prompts",
    "architecture_router",
    "auth_router",
    "config_router",
    "files_router",
    "commands_router",
    "websocket_router",
    "prompts_router",
]