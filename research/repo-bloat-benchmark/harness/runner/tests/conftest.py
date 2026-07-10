"""Make `harness.*` importable when pytest runs from any directory."""

import sys
from pathlib import Path

_BENCH_ROOT = Path(__file__).resolve().parents[3]
if str(_BENCH_ROOT) not in sys.path:
    sys.path.insert(0, str(_BENCH_ROOT))
