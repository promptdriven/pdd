"""Small filesystem durability primitives shared by canonical state writers."""

import os
from pathlib import Path


def fsync_directory(path: Path) -> None:
    """Flush a directory entry update after atomic replacement."""
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
