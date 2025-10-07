import os
import importlib
import types

def test_logging_levels_toggle(monkeypatch):
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "verbose")
    # reload to pick up env at import time
    if "pdd.agentic_logging" in list(importlib.sys.modules.keys()):
        importlib.sys.modules.pop("pdd.agentic_logging", None)
    mod = importlib.import_module("pdd.agentic_logging")
    assert mod.IS_VERBOSE is True
    assert mod.IS_QUIET is False

    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")
    importlib.reload(mod)
    assert mod.IS_QUIET is True
    assert mod.IS_VERBOSE is False

def test_env_defaults(monkeypatch):
    for k in ("PDD_AGENTIC_COST_PER_CALL", "PDD_AGENTIC_TIMEOUT", "PDD_AGENTIC_VERIFY_TIMEOUT", "PDD_AGENTIC_MAX_LOG_LINES"):
        monkeypatch.delenv(k, raising=False)
    if "pdd.agentic_logging" in list(importlib.sys.modules.keys()):
        importlib.sys.modules.pop("pdd.agentic_logging", None)
    mod = importlib.import_module("pdd.agentic_logging")
    assert isinstance(mod.AGENT_COST_PER_CALL, float)
    assert isinstance(mod.AGENT_CALL_TIMEOUT, int)
    assert isinstance(mod.VERIFY_TIMEOUT, int)
    assert isinstance(mod.MAX_LOG_LINES, int)
