"""Root conftest.py — ensures the local pdd source takes precedence over any
installed package copies so tests exercise the development version."""
import sys
from pathlib import Path

# Prepend the project root so ``import pdd`` resolves to the checked-out
# source tree rather than the system/venv site-packages installation.
_PROJECT_ROOT = str(Path(__file__).resolve().parent)
if _PROJECT_ROOT not in sys.path:
    sys.path.insert(0, _PROJECT_ROOT)
