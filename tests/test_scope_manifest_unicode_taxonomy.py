"""Regression test: a non-UTF-8 scope manifest must map to scope:MANIFEST_UNREADABLE.

Bug summary
-----------
``pdd.commands.analysis._load_scope_manifest`` classifies read failures via an
exception taxonomy. ``UnicodeError`` is a subclass of ``ValueError``, so the
``except ValueError: raise`` clause shadowed the later
``except (OSError, UnicodeError)`` handler. As a result, a manifest file whose
bytes are not valid UTF-8 raised a raw ``UnicodeDecodeError`` (leaking the
``'utf-8' codec can't decode`` message) instead of the intended
``ValueError("scope:MANIFEST_UNREADABLE")`` the taxonomy promises for
unreadable manifests.

This test exercises observable behavior (the exception raised for a real file
on disk). It fails on the buggy ordering and passes once the
``except (OSError, UnicodeError)`` handler precedes ``except ValueError``.
"""
from __future__ import annotations

from pathlib import Path

import pytest


def test_non_utf8_manifest_maps_to_unreadable(tmp_path: Path) -> None:
    from pdd.commands.analysis import _load_scope_manifest

    manifest = tmp_path / "scope_manifest.json"
    # Bytes that are not valid UTF-8, so json.load's read() raises
    # UnicodeDecodeError (a ValueError subclass) before any JSON parsing.
    manifest.write_bytes(b'\xff\xfe{"schema_version": "pdd.detect.stories.scope.v1"}')

    with pytest.raises(ValueError) as excinfo:
        _load_scope_manifest(manifest)

    assert "scope:MANIFEST_UNREADABLE" in str(excinfo.value)
