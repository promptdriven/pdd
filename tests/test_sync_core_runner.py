"""Tests for pass-only trusted runner normalization and self-certification guards."""

import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

import pytest
import pdd.sync_core.runner as runner_module

from pdd.sync_core import (
    AttestationSigner,
    AttestationIssue,
    EvidenceOutcome,
    RunnerConfig,
    RunBinding,
    UnitId,
    VerificationObligation,
    VerificationProfile,
    run_profile,
)
from pdd.sync_core.runner import (
    _config_loads_plugin,
    _has_dynamic_pytest_plugins,
    _local_module_paths,
    pytest_validator_config_digest,
    runner_identity_digest,
)


UNIT = UnitId("repository-1", PurePosixPath("prompts/widget_python.prompt"), "python")


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()


def _repository(tmp_path: Path, test_content: str) -> tuple[Path, str]:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/test_widget.py").write_text(test_content)
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "tests")
    return root, _git(root, "rev-parse", "HEAD")


def _profile(
    root: Path,
    ref: str,
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
) -> VerificationProfile:
    paths = (PurePosixPath("tests/test_widget.py"),)
    obligation = VerificationObligation(
        "pytest",
        "test",
        "pytest",
        pytest_validator_config_digest(root, ref, paths),
        ("REQ-1",),
        paths,
        code_under_test_paths=code_under_test_paths,
    )
    return VerificationProfile(UNIT, (obligation,), ("REQ-1",), "profile-v1")


def _run(
    root: Path,
    base: str,
    head: str,
    code_under_test_paths: tuple[PurePosixPath, ...] = (),
):
    if sys.platform == "darwin":
        pytest.skip("protected validators fail closed without Linux namespaces")
    return run_profile(
        root,
        _profile(root, base, code_under_test_paths),
        RunBinding("snapshot-v1", base, head),
        AttestationIssue(
            AttestationSigner("trusted-ci", b"v" * 32),
            "attestation-1",
            "nonce-1",
            datetime(2026, 7, 10, 12, 0, tzinfo=timezone.utc),
        ),
        config=RunnerConfig(timeout_seconds=20),
    )


def test_passing_collected_test_is_pass(tmp_path) -> None:
    root, commit = _repository(tmp_path, "def test_widget(): assert True\n")
    envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is EvidenceOutcome.PASS
    assert envelope.results[0].outcome is EvidenceOutcome.PASS


def test_zero_tests_is_not_collected(tmp_path) -> None:
    root, commit = _repository(tmp_path, "value = 1\n")
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is EvidenceOutcome.NOT_COLLECTED


def test_skipped_test_cannot_satisfy_obligation(tmp_path) -> None:
    root, commit = _repository(
        tmp_path,
        "import pytest\n@pytest.mark.skip(reason='not ready')\ndef test_widget(): pass\n",
    )
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is EvidenceOutcome.SKIP


def test_candidate_modified_test_cannot_self_certify(tmp_path) -> None:
    root, base = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "tests/test_widget.py").write_text("def test_widget(): assert 1 == 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "weaken test")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, base, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


def test_worktree_modified_test_cannot_self_certify(tmp_path) -> None:
    root, head = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "tests/test_widget.py").write_text("def test_widget(): assert 1 == 1\n")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED


def test_candidate_modified_conftest_cannot_self_certify(tmp_path) -> None:
    root, base = _repository(tmp_path, "def test_widget(value): assert value == 1\n")
    (root / "tests/conftest.py").write_text(
        "import pytest\n@pytest.fixture\ndef value(): return 1\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate fixture")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, base, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "config digest" in executions[0].detail


def test_untracked_conftest_cannot_influence_checked_sha(tmp_path) -> None:
    root, head = _repository(tmp_path, "def test_widget(): assert False\n")
    (root / "conftest.py").write_text(
        "def pytest_collection_modifyitems(items):\n"
        "    for item in items: item.obj = lambda: None\n"
    )
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED
    assert "conftest.py" in executions[0].detail


def test_candidate_modified_imported_test_helper_cannot_self_certify(tmp_path) -> None:
    root, base = _repository(
        tmp_path,
        "from tests.helper import expected\ndef test_widget(): assert expected() == 1\n",
    )
    (root / "tests/__init__.py").write_text("")
    (root / "tests/helper.py").write_text("def expected():\n    return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate helper")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, base, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED
    assert "tests/helper.py" in executions[0].detail


def test_candidate_modified_product_code_can_be_certified_by_protected_tests(tmp_path) -> None:
    root, base = _repository(
        tmp_path,
        "import product\n\ndef test_widget(): assert product.expected() >= 1\n",
    )
    (root / "product.py").write_text("def expected(): return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "base product")
    base = _git(root, "rev-parse", "HEAD")
    (root / "product.py").write_text("def expected(): return 2\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate product")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(
        root, base, head, (PurePosixPath("product.py"),)
    )
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_dirty_declared_product_code_cannot_receive_committed_head_evidence(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path, "import product\ndef test_widget(): assert product.expected() == 1\n"
    )
    (root / "product.py").write_text("def expected(): return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "product")
    head = _git(root, "rev-parse", "HEAD")
    (root / "product.py").write_text("def expected(): return 2\n")
    _envelope, executions = _run(
        root, head, head, (PurePosixPath("product.py"),)
    )
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED
    assert "dirty" in executions[0].detail


def test_declared_product_reflection_is_not_an_unbound_test_loader(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path, "import product\ndef test_widget(): assert product.expected() == 1\n"
    )
    (root / "product.py").write_text(
        "def expected():\n    return getattr(type('X', (), {'value': 1}), 'value')\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "reflective product")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(
        root, head, head, (PurePosixPath("product.py"),)
    )
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_candidate_modified_helper_outside_tests_is_protected(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path,
        "from support.fixtures import expected\n"
        "def test_widget(): assert expected() == 1\n",
    )
    (root / "support").mkdir()
    (root / "support/__init__.py").write_text("")
    (root / "support/fixtures.py").write_text("def expected(): return 2\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "base helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "support/fixtures.py").write_text("def expected(): return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate helper")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, base, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED
    assert "support/fixtures.py" in executions[0].detail


def test_candidate_modified_package_initializer_is_protected(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path,
        "from support.fixtures import expected\n"
        "def test_widget(): assert expected() == 1\n",
    )
    (root / "support").mkdir()
    (root / "support/__init__.py").write_text("FLAG = 1\n")
    (root / "support/fixtures.py").write_text("def expected(): return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "base helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "support/__init__.py").write_text("FLAG = 2\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate initializer")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, base, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED
    assert "support/__init__.py" in executions[0].detail


def test_collection_time_protected_test_rewrite_fails_closed(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path,
        "import product\ndef test_widget(): assert False\n",
    )
    (root / "product.py").write_text(
        "from pathlib import Path\n"
        "Path('tests/test_widget.py').write_text("
        "'import product\\ndef test_widget(): assert True\\n')\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate product")
    head = _git(root, "rev-parse", "HEAD")
    original = (root / "tests/test_widget.py").read_bytes()
    _envelope, executions = _run(
        root, head, head, (PurePosixPath("product.py"),)
    )
    assert executions[0].outcome is not EvidenceOutcome.PASS
    assert "protected" in executions[0].detail
    assert (root / "tests/test_widget.py").read_bytes() == original


def test_external_literal_pytest_plugin_fails_closed(tmp_path) -> None:
    root, _initial = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "conftest.py").write_text('pytest_plugins = "pytest_mock"\n')
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "external plugin")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "external pytest_plugins" in executions[0].detail


def test_nested_external_pytest_plugin_fails_closed(tmp_path) -> None:
    root, _base = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "tests/plugin.py").write_text('pytest_plugins = "pytest_mock"\n')
    (root / "conftest.py").write_text('pytest_plugins = "tests.plugin"\n')
    _git(root, "add", "conftest.py", "tests/plugin.py")
    _git(root, "commit", "-q", "-m", "nested external plugin")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "external pytest_plugins" in executions[0].detail


def test_product_pytest_plugins_declaration_is_not_traversed_as_support(tmp_path) -> None:
    root, _base = _repository(
        tmp_path, "import product\ndef test_widget(): assert product.VALUE == 1\n"
    )
    (root / "product.py").write_text(
        'VALUE = 1\npytest_plugins = "vendor.runtime"\n'
    )
    _git(root, "add", "product.py", "tests/test_widget.py")
    _git(root, "commit", "-q", "-m", "declared product")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(
        root, head, head, (PurePosixPath("product.py"),)
    )
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_dynamic_repo_local_import_fails_closed(tmp_path) -> None:
    root, _base = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "tests/test_widget.py").write_text(
        "import importlib\n"
        "helper = importlib.import_module('support.helper')\n"
        "def test_widget(): assert helper.expected() == 1\n"
    )
    (root / "support").mkdir()
    (root / "support/helper.py").write_text("def expected(): return 1\n")
    _git(root, "add", "tests/test_widget.py", "support/helper.py")
    _git(root, "commit", "-q", "-m", "dynamic helper")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR


def test_aliased_dynamic_repo_local_import_fails_closed(tmp_path) -> None:
    root, _base = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "tests/test_widget.py").write_text(
        "from importlib import import_module as load\n"
        "helper = load('support.helper')\n"
        "def test_widget(): assert helper.expected() == 1\n"
    )
    (root / "support").mkdir()
    (root / "support/helper.py").write_text("def expected(): return 1\n")
    _git(root, "add", "tests/test_widget.py", "support/helper.py")
    _git(root, "commit", "-q", "-m", "aliased dynamic helper")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR


def test_string_pytest_plugins_are_bound_as_protected_support(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path,
        "def test_widget(value): assert value in {1, 2}\n",
    )
    (root / "tests/__init__.py").write_text("")
    (root / "tests/plugin.py").write_text(
        "import pytest\n@pytest.fixture\ndef value(): return 1\n"
    )
    (root / "conftest.py").write_text('pytest_plugins = "tests.plugin"\n')
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "base string plugin")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/plugin.py").write_text(
        "import pytest\n@pytest.fixture\ndef value(): return 2\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate plugin change")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, base, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED
    assert "tests/plugin.py" in executions[0].detail


def test_dynamic_pytest_plugins_fail_closed(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path,
        "def test_widget(value): assert value == 1\n",
    )
    (root / "tests/__init__.py").write_text("")
    (root / "tests/plugin.py").write_text(
        "import pytest\n@pytest.fixture\ndef value(): return 1\n"
    )
    (root / "conftest.py").write_text("pytest_plugins = tuple(['tests.plugin'])\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "dynamic plugin declaration")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "dynamic pytest_plugins" in executions[0].detail


@pytest.mark.parametrize(
    "declaration",
    [
        "pytest_plugins = []\npytest_plugins.append('tests.plugin')\n",
        "pytest_plugins = set()\npytest_plugins.update({'tests.plugin'})\n",
        "pytest_plugins = []\nglobals()['pytest_plugins'] = ['tests.plugin']\n",
        "pytest_plugins = []\nsetattr(sys.modules[__name__], 'pytest_plugins', ['tests.plugin'])\n",
        "pytest_plugins = []\nalias = pytest_plugins\nalias.append('tests.plugin')\n",
        "setattr(sys.modules[__name__], 'pytest_plugins', ['tests.plugin'])\n",
    ],
)
def test_mutated_pytest_plugins_fail_closed(tmp_path, declaration) -> None:
    root, _initial = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "tests/__init__.py").write_text("")
    (root / "tests/plugin.py").write_text("VALUE = 1\n")
    (root / "conftest.py").write_text("import sys\n" + declaration)
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "mutated plugin declaration")
    head = _git(root, "rev-parse", "HEAD")
    assert _has_dynamic_pytest_plugins(
        root, head, (PurePosixPath("tests/test_widget.py"),)
    )


def test_unrelated_getattr_in_protected_conftest_is_allowed(tmp_path) -> None:
    root, _initial = _repository(tmp_path, "def test_widget(value): assert value == 1\n")
    (root / "conftest.py").write_text(
        "import pytest\n"
        "VALUE = getattr(type('Config', (), {'value': 1}), 'value')\n"
        "@pytest.fixture\ndef value(): return VALUE\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "ordinary reflection")
    head = _git(root, "rev-parse", "HEAD")
    assert not _has_dynamic_pytest_plugins(
        root, head, (PurePosixPath("tests/test_widget.py"),)
    )


def test_repository_conftest_ordinary_getattr_passes_plugin_preflight(
    monkeypatch,
) -> None:
    root = Path(__file__).resolve().parents[1]
    source = (root / "tests/conftest.py").read_bytes()
    monkeypatch.setattr("pdd.sync_core.runner.read_git_blob", lambda *_args: None)
    _paths, dynamic = _local_module_paths(
        root, "HEAD", PurePosixPath("tests/conftest.py"), source
    )
    assert not dynamic


def test_candidate_modified_importfrom_alias_helper_cannot_self_certify(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path,
        "from tests import helper\ndef test_widget(): assert helper.expected() == 1\n",
    )
    (root / "tests/__init__.py").write_text("")
    (root / "tests/helper.py").write_text("def expected(): return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "base helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.py").write_text("def expected():\n    return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate helper")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, base, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED
    assert "tests/helper.py" in executions[0].detail


def test_candidate_modified_relative_importfrom_helper_cannot_self_certify(tmp_path) -> None:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "runner@example.com")
    _git(root, "config", "user.name", "Runner Test")
    (root / "tests").mkdir()
    (root / "tests/__init__.py").write_text("")
    (root / "tests/test_widget.py").write_text(
        "from . import helper\ndef test_widget(): assert helper.expected() == 1\n"
    )
    (root / "tests/helper.py").write_text("def expected(): return 2\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "base helper")
    base = _git(root, "rev-parse", "HEAD")
    (root / "tests/helper.py").write_text("def expected(): return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate helper")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, base, head)
    assert executions[0].outcome is EvidenceOutcome.QUARANTINED
    assert "tests/helper.py" in executions[0].detail


def test_validator_subprocess_cannot_read_signing_secret(tmp_path, monkeypatch) -> None:
    content = (
        "import os\n"
        "def test_widget():\n"
        "    assert os.environ.get('PDD_ATTESTATION_SIGNING_KEY') is None\n"
    )
    root, head = _repository(tmp_path, content)
    monkeypatch.setenv("PDD_ATTESTATION_SIGNING_KEY", "candidate-must-not-read")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_pytest_execution_uses_private_home_and_userprofile(tmp_path, monkeypatch) -> None:
    protected_home = tmp_path / "protected-home"
    protected_home.mkdir()
    (protected_home / "secret.txt").write_text("protected-secret")
    monkeypatch.setenv("HOME", str(protected_home))
    monkeypatch.setenv("USERPROFILE", str(protected_home))
    content = (
        "import os\nfrom pathlib import Path\n"
        "def test_widget():\n"
        "    home = Path(os.environ['HOME'])\n"
        "    profile = Path(os.environ['USERPROFILE'])\n"
        "    assert home == profile\n"
        "    assert not (home / 'secret.txt').exists()\n"
    )
    root, head = _repository(tmp_path, content)
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_pytest_collection_uses_private_home_and_userprofile(tmp_path, monkeypatch) -> None:
    protected_home = tmp_path / "protected-home"
    protected_home.mkdir()
    (protected_home / "secret.txt").write_text("protected-secret")
    monkeypatch.setenv("HOME", str(protected_home))
    monkeypatch.setenv("USERPROFILE", str(protected_home))
    root, head = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "conftest.py").write_text(
        "import os\nfrom pathlib import Path\n"
        "def pytest_collection_modifyitems(items):\n"
        "    home = Path(os.environ['HOME'])\n"
        "    profile = Path(os.environ['USERPROFILE'])\n"
        "    assert home == profile\n"
        "    assert not (home / 'secret.txt').exists()\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "collection hook")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_validator_subprocess_cannot_read_signer_capabilities(tmp_path, monkeypatch) -> None:
    content = (
        "import os\n"
        "def test_widget():\n"
        "    assert os.environ.get('PDD_ATTESTATION_SIGNER_COMMAND') is None\n"
        "    assert os.environ.get('PDD_CERTIFICATE_ISSUER') is None\n"
        "    assert os.environ.get('PDD_RELEASED_CHECKER_COMMAND') is None\n"
    )
    root, head = _repository(tmp_path, content)
    monkeypatch.setenv("PDD_ATTESTATION_SIGNER_COMMAND", "protected-attestation")
    monkeypatch.setenv("PDD_CERTIFICATE_ISSUER", "protected-issuer")
    monkeypatch.setenv("PDD_RELEASED_CHECKER_COMMAND", "protected-checker")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_ambient_pytest_options_and_plugins_are_disabled(tmp_path, monkeypatch) -> None:
    content = (
        "import os\n"
        "def test_widget():\n"
        "    assert os.environ.get('PYTEST_ADDOPTS') is None\n"
        "    assert os.environ['PYTEST_DISABLE_PLUGIN_AUTOLOAD'] == '1'\n"
    )
    root, head = _repository(tmp_path, content)
    monkeypatch.setenv("PYTEST_ADDOPTS", "--collect-only")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS


def test_collection_probe_is_checker_owned_not_candidate_shadow(tmp_path) -> None:
    root, head = _repository(tmp_path, "def test_widget(): assert True\n")
    candidate_probe = root / "pdd/sync_core/pytest_probe.py"
    candidate_probe.parent.mkdir(parents=True)
    (root / "pdd/__init__.py").write_text("", encoding="utf-8")
    (root / "pdd/sync_core/__init__.py").write_text("", encoding="utf-8")
    candidate_probe.write_text(
        "from pathlib import Path\n"
        "def pytest_collection_modifyitems(items):\n"
        "    Path('candidate-probe-loaded').write_text('shadowed')\n"
        "    items[:] = []\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate probe shadow")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS
    assert not (root / "candidate-probe-loaded").exists()


def test_collection_probe_fixed_name_is_not_candidate_shadowable(tmp_path) -> None:
    root, head = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "pdd_checker_pytest_probe.py").write_text(
        "import json, os\n"
        "from pathlib import Path\n"
        "def pytest_collection_modifyitems(items):\n"
        "    Path('candidate-fixed-probe-loaded').write_text('shadowed')\n"
        "    output = os.environ.get('PDD_TRUSTED_COLLECTION_OUTPUT')\n"
        "    if output:\n"
        "        Path(output).write_text(json.dumps([item.nodeid for item in items]))\n",
        encoding="utf-8",
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "candidate fixed probe shadow")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS
    assert not (root / "candidate-fixed-probe-loaded").exists()


def test_deselected_declared_test_cannot_pass(tmp_path) -> None:
    content = "def test_keep(): assert True\ndef test_drop(): assert True\n"
    root, head = _repository(tmp_path, content)
    (root / "conftest.py").write_text(
        "def pytest_collection_modifyitems(items):\n"
        "    items[:] = [item for item in items if item.name == 'test_keep']\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected collection policy")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.NOT_COLLECTED


def test_removed_parametrized_case_cannot_pass(tmp_path) -> None:
    content = (
        "import pytest\n"
        "@pytest.mark.parametrize('value', [1, 2])\n"
        "def test_widget(value): assert value in {1, 2}\n"
    )
    root, head = _repository(tmp_path, content)
    (root / "conftest.py").write_text(
        "def pytest_collection_modifyitems(items):\n"
        "    items[:] = [item for item in items if '[2]' not in item.nodeid]\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "protected collection hook")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is not EvidenceOutcome.PASS


def test_config_loaded_local_plugin_fails_closed(tmp_path) -> None:
    root, head = _repository(tmp_path, "def test_widget(): assert False\n")
    (root / "local_plugin.py").write_text(
        "def pytest_collection_modifyitems(items):\n"
        "    for item in items: item.obj = lambda: None\n"
    )
    (root / "pytest.ini").write_text("[pytest]\naddopts = -p local_plugin\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "configured local plugin")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "plugins are not bound" in executions[0].detail


def test_non_strict_xpass_cannot_pass(tmp_path) -> None:
    content = (
        "import pytest\n"
        "@pytest.mark.xfail(reason='known')\n"
        "def test_widget(): assert True\n"
    )
    root, head = _repository(tmp_path, content)
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.XFAIL


def test_reflective_dynamic_repo_local_import_fails_closed(tmp_path) -> None:
    root, _base = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "tests/test_widget.py").write_text(
        "import importlib\n"
        "helper = getattr(importlib, 'import_module')('support.helper')\n"
        "def test_widget(): assert helper.expected() == 1\n"
    )
    (root / "support").mkdir()
    (root / "support/helper.py").write_text("def expected(): return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "reflective dynamic helper")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR


def test_file_loader_repo_local_import_fails_closed(tmp_path) -> None:
    root, _base = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "tests/test_widget.py").write_text(
        "from importlib.machinery import SourceFileLoader\n"
        "helper = SourceFileLoader('helper', 'support/helper.py').load_module()\n"
        "def test_widget(): assert helper.expected() == 1\n"
    )
    (root / "support").mkdir()
    (root / "support/helper.py").write_text("def expected(): return 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "file loader helper")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR


def test_compact_config_loaded_local_plugin_fails_closed(tmp_path) -> None:
    root, _head = _repository(tmp_path, "def test_widget(): assert False\n")
    (root / "local_plugin.py").write_text(
        "def pytest_collection_modifyitems(items):\n"
        "    for item in items: item.obj = lambda: None\n"
    )
    (root / "pytest.ini").write_text("[pytest]\naddopts = -plocal_plugin\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "compact configured local plugin")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.ERROR
    assert "plugins are not bound" in executions[0].detail


def test_self_restoring_protected_test_rewrite_cannot_pass(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path, "import product\ndef test_widget(): assert False\n"
    )
    (root / "product.py").write_text(
        "import atexit\nfrom pathlib import Path\n"
        "p = Path('tests/test_widget.py')\noriginal = p.read_text()\n"
        "p.write_text('import product\\ndef test_widget(): assert True\\n')\n"
        "atexit.register(p.write_text, original)\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "self restoring rewrite")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head, (PurePosixPath("product.py"),))
    assert executions[0].outcome is not EvidenceOutcome.PASS


def test_surviving_validator_descendant_cannot_pass(tmp_path) -> None:
    pid_file = tmp_path / "descendant.pid"
    content = (
        "import subprocess, sys\nfrom pathlib import Path\n"
        "def test_widget():\n"
        "    child = subprocess.Popen([sys.executable, '-c', "
        "'import time; time.sleep(30)'])\n"
        f"    Path({str(pid_file)!r}).write_text(str(child.pid))\n"
        "    assert True\n"
    )
    root, head = _repository(tmp_path, content)
    try:
        _envelope, executions = _run(root, head, head)
        assert executions[0].outcome is not EvidenceOutcome.PASS
    finally:
        if pid_file.exists():
            try:
                os.kill(int(pid_file.read_text()), 9)
            except ProcessLookupError:
                pass


def test_managed_subprocess_fails_closed_without_supported_os_sandbox(
    tmp_path, monkeypatch
) -> None:
    from pdd.sync_core.runner import _managed_subprocess

    monkeypatch.setattr("pdd.sync_core.runner.sys.platform", "freebsd14")
    result, surviving = _managed_subprocess(
        [sys.executable, "-c", "print('must not execute')"],
        cwd=tmp_path,
        timeout=5,
        env={},
        writable_roots=(tmp_path,),
    )
    assert result.returncode != 0
    assert "unsupported sandbox platform" in result.stderr
    assert "must not execute" not in result.stdout
    assert surviving is False


@pytest.mark.parametrize(
    "source",
    [
        "pytest_plugins = []\npytest_plugins += ['vendor.runtime']\n",
        "pytest_plugins = []\n(alias := pytest_plugins).append('vendor.runtime')\n",
        "pytest_plugins = ['tests.local']\ndel pytest_plugins[0]\n",
        "pytest_plugins = ['tests.local']\npytest_plugins[0] = 'vendor.runtime'\n",
        "pytest_plugins = []\nalias = pytest_plugins\nalias.value = 'vendor.runtime'\n",
    ],
)
def test_effective_pytest_plugin_mutations_fail_closed(source: str) -> None:
    _resolved, dynamic = _local_module_paths(
        Path("."), "HEAD", PurePosixPath("tests/conftest.py"), source.encode()
    )
    assert dynamic is True


def test_runner_identity_binds_code_under_test_role_policy(tmp_path: Path) -> None:
    root, commit = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "product.py").write_text("VALUE = 1\n", encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "product")
    commit = _git(root, "rev-parse", "HEAD")
    support = _profile(root, commit)
    product = _profile(root, commit, (PurePosixPath("product.py"),))
    assert runner_identity_digest(support, root=root, ref=commit) != (
        runner_identity_digest(product, root=root, ref=commit)
    )


def test_candidate_leader_exit_cannot_forge_junit_pass(tmp_path: Path) -> None:
    content = (
        "import os, sys\n"
        "for arg in sys.argv:\n"
        "    if arg.startswith('--junitxml='):\n"
        "        open(arg.split('=', 1)[1], 'w').write("
        "'<testsuite tests=\"1\" failures=\"0\" errors=\"0\" skipped=\"0\"/>')\n"
        "os._exit(0)\n"
        "def test_widget(): assert False\n"
    )
    root, commit = _repository(tmp_path, content)
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is not EvidenceOutcome.PASS


def test_candidate_leader_exit_cannot_forge_collection_pass(tmp_path: Path) -> None:
    content = (
        "import os\n"
        "output = os.environ.get('PDD_TRUSTED_COLLECTION_OUTPUT')\n"
        "if output:\n"
        "    open(output, 'w').write('[\"tests/test_widget.py::test_widget\"]')\n"
        "    os._exit(0)\n"
        "def test_widget(): assert False\n"
    )
    root, commit = _repository(tmp_path, content)
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is not EvidenceOutcome.PASS


def test_candidate_controller_globals_cannot_forge_execution_pass(tmp_path: Path) -> None:
    content = (
        "import os, sys\n"
        "main = sys.modules['__main__']\n"
        "for arg in getattr(main, '_ARGS', ()):\n"
        "    if arg.startswith('--junitxml='):\n"
        "        open(arg.split('=', 1)[1], 'w').write("
        "'<testsuite tests=\"1\" failures=\"0\" errors=\"0\" skipped=\"0\"/>')\n"
        "        os._exit(0)\n"
        "def test_widget(): assert False\n"
    )
    root, commit = _repository(tmp_path, content)
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is not EvidenceOutcome.PASS


def test_candidate_controller_globals_cannot_forge_collection_pass(tmp_path: Path) -> None:
    content = (
        "import os, sys\n"
        "main = sys.modules['__main__']\n"
        "module = getattr(main, '_MODULE', None)\n"
        "output = getattr(module, '_OUTPUT_PATH', None)\n"
        "if output:\n"
        "    open(output, 'w').write('[\"tests/test_widget.py::test_widget\"]')\n"
        "    os._exit(0)\n"
        "def test_widget(): assert False\n"
    )
    root, commit = _repository(tmp_path, content)
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is not EvidenceOutcome.PASS


def test_candidate_cannot_forge_worker_outputs_discovered_from_script_path(
    tmp_path: Path,
) -> None:
    content = (
        "import os, sys\nfrom pathlib import Path\n"
        "directory = Path(sys.argv[0]).resolve().parent\n"
        "if Path(sys.argv[0]).name == 'collection_worker.py':\n"
        "    next(directory.glob('collection-*.json')).write_text("
        "'[\"tests/test_widget.py::test_widget\"]')\n"
        "    os._exit(0)\n"
        "if Path(sys.argv[0]).name == 'execution_worker.py':\n"
        "    next(directory.glob('execution-*.xml')).write_text("
        "'<testsuite tests=\"1\" failures=\"0\" errors=\"0\" skipped=\"0\"/>')\n"
        "    os._exit(0)\n"
        "def test_widget(): assert False\n"
    )
    root, commit = _repository(tmp_path, content)
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is not EvidenceOutcome.PASS


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux protected runner",
)
def test_candidate_reading_worker_source_cannot_forge_collection_or_execution(
    tmp_path: Path,
) -> None:
    """A worker script is candidate-readable, so it cannot name an authority."""
    content = (
        "import os, re, sys\nfrom pathlib import Path\n"
        "source = Path(sys.argv[0]).read_text(encoding='utf-8')\n"
        "for name in re.findall(r'/[^\\\" ]*/results-[0-9a-f]+/"
        "(?:collection|execution)-[0-9a-f]+\\.(?:json|xml)', source):\n"
        "    payload = ('[\\\"tests/test_widget.py::test_widget\\\"]' if name.endswith('.json') "
        "else '<testsuite tests=\\\"1\\\" failures=\\\"0\\\" errors=\\\"0\\\" skipped=\\\"0\\\"/>')\n"
        "    Path(name).write_text(payload, encoding='utf-8')\n"
        "if Path(sys.argv[0]).name in {'collection_worker.py', 'execution_worker.py'}:\n"
        "    os._exit(80)\n"
        "def test_widget(): assert False\n"
    )
    root, commit = _repository(tmp_path, content)
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is not EvidenceOutcome.PASS


@pytest.mark.skipif(
    not sys.platform.startswith("linux") or not shutil.which("bwrap"),
    reason="requires Linux protected runner",
)
def test_candidate_cannot_recursively_forge_any_result_channel(tmp_path: Path) -> None:
    content = (
        "import os, sys\nfrom pathlib import Path\n"
        "trusted = Path(sys.argv[0]).resolve().parent\n"
        "for path in trusted.rglob('*'):\n"
        "    if path.is_file() and (path.suffix in {'.json', '.xml'} or "
        "path.name in {'node-ids.json', 'junit.xml'}):\n"
        "        try:\n"
        "            payload = ('[\"tests/test_widget.py::test_widget\"]' if "
        "path.suffix == '.json' else "
        "'<testsuite tests=\"1\" failures=\"0\" errors=\"0\" skipped=\"0\"/>')\n"
        "            path.write_text(payload)\n"
        "        except OSError:\n"
        "            pass\n"
        "if Path(sys.argv[0]).name in {'collection_worker.py', 'execution_worker.py'}:\n"
        "    os._exit(0)\n"
        "def test_widget(): assert False\n"
    )
    root, commit = _repository(tmp_path, content)
    _envelope, executions = _run(root, commit, commit)
    assert executions[0].outcome is not EvidenceOutcome.PASS


def test_runner_identity_fails_closed_for_dynamic_product_loader(tmp_path: Path) -> None:
    root, _commit = _repository(
        tmp_path, "import product\ndef test_widget(): assert product.value == 1\n"
    )
    (root / "product.py").write_text(
        "import importlib\nvalue = importlib.import_module('helper').value\n"
    )
    (root / "helper.py").write_text("value = 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "dynamic product closure")
    commit = _git(root, "rev-parse", "HEAD")
    profile = _profile(root, commit, (PurePosixPath("product.py"),))
    with pytest.raises(ValueError, match="dynamic product dependency"):
        runner_identity_digest(profile, root=root, ref=commit)


@pytest.mark.parametrize(
    "product",
    [
        "loader = __builtins__['__import__']\nvalue = loader('helper').value\n",
        "loader = getattr(__builtins__, '__getitem__')('__import__')\n"
        "value = loader('helper').value\n",
    ],
)
def test_runner_identity_fails_closed_for_aliased_reflective_loader(
    tmp_path: Path, product: str
) -> None:
    root, _commit = _repository(
        tmp_path, "import product\ndef test_widget(): assert product.value == 1\n"
    )
    (root / "product.py").write_text(product)
    (root / "helper.py").write_text("value = 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "aliased product loader")
    before = _git(root, "rev-parse", "HEAD")
    profile = _profile(root, before, (PurePosixPath("product.py"),))
    before_digest = runner_identity_digest(profile, root=root, ref=before)
    (root / "helper.py").write_text("value = 2\n")
    _git(root, "add", "helper.py")
    _git(root, "commit", "-q", "-m", "change hidden helper")
    after = _git(root, "rev-parse", "HEAD")
    assert runner_identity_digest(profile, root=root, ref=after) != before_digest


def test_runner_identity_binds_measured_runtime_and_checker(
    tmp_path: Path, monkeypatch
) -> None:
    root, commit = _repository(tmp_path, "def test_widget(): assert True\n")
    profile = _profile(root, commit)
    first = runner_identity_digest(profile, root=root, ref=commit)
    monkeypatch.setattr("pdd.sync_core.runner.platform.python_version", lambda: "99.1")
    assert runner_identity_digest(profile, root=root, ref=commit) != first
    monkeypatch.undo()
    monkeypatch.setattr("pdd.sync_core.runner._checker_artifact_digest", lambda: "0" * 64)
    assert runner_identity_digest(profile, root=root, ref=commit) != first


def test_runner_identity_binds_transitive_product_dependency(tmp_path: Path) -> None:
    root, _commit = _repository(
        tmp_path, "import product\ndef test_widget(): assert product.value == 1\n"
    )
    (root / "product.py").write_text("from helper import value\n")
    (root / "helper.py").write_text("value = 1\n")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "product closure")
    before = _git(root, "rev-parse", "HEAD")
    profile = _profile(root, before, (PurePosixPath("product.py"),))
    before_digest = runner_identity_digest(profile, root=root, ref=before)
    (root / "helper.py").write_text("value = 2\n")
    _git(root, "add", "helper.py")
    _git(root, "commit", "-q", "-m", "change indirect helper")
    after = _git(root, "rev-parse", "HEAD")
    assert runner_identity_digest(profile, root=root, ref=after) != before_digest


def test_runner_identity_binds_product_readable_repository_data(tmp_path: Path) -> None:
    root, _commit = _repository(
        tmp_path,
        "import product\ndef test_widget(): assert product.value == 1\n",
    )
    (root / "product.py").write_text(
        "import json\nvalue = json.loads(open('helper.json').read())['value']\n",
        encoding="utf-8",
    )
    (root / "helper.json").write_text('{"value": 1}\n', encoding="utf-8")
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "product data closure")
    before = _git(root, "rev-parse", "HEAD")
    profile = _profile(root, before, (PurePosixPath("product.py"),))
    first = runner_identity_digest(profile, root=root, ref=before)
    (root / "helper.json").write_text('{"value": 2}\n', encoding="utf-8")
    _git(root, "add", "helper.json")
    _git(root, "commit", "-q", "-m", "change product data")
    after = _git(root, "rev-parse", "HEAD")
    assert runner_identity_digest(profile, root=root, ref=after) != first


def test_released_runtime_digest_binds_installed_native_dependency(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    native = tmp_path / "site-packages" / "native_extension.so"
    native.parent.mkdir()
    native.write_bytes(b"native-v1")
    monkeypatch.setattr(
        runner_module,
        "_released_runtime_closure_paths",
        lambda: (("python-runtime/site-packages/native_extension.so", native),),
        raising=False,
    )
    first = runner_module._released_runtime_closure_digest()
    native.write_bytes(b"native-v2")
    assert runner_module._released_runtime_closure_digest() != first


def test_released_runtime_digest_binds_runtime_and_sandbox_bytes_prefix_portably(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    first_prefix = tmp_path / "prefix-a"
    second_prefix = tmp_path / "prefix-b"
    first_python = first_prefix / "bin/python"
    second_python = second_prefix / "bin/python"
    first_bwrap = first_prefix / "bin/bwrap"
    second_bwrap = second_prefix / "bin/bwrap"
    for path in (first_python, second_python, first_bwrap, second_bwrap):
        path.parent.mkdir(parents=True, exist_ok=True)
    first_python.write_bytes(b"python-runtime")
    second_python.write_bytes(b"python-runtime")
    first_bwrap.write_bytes(b"sandbox-runtime")
    second_bwrap.write_bytes(b"sandbox-runtime")
    paths = (("interpreter/python", first_python), ("sandbox/bwrap", first_bwrap))
    monkeypatch.setattr(
        runner_module, "_released_runtime_closure_paths", lambda: paths, raising=False
    )
    first = runner_module._released_runtime_closure_digest()
    monkeypatch.setattr(
        runner_module,
        "_released_runtime_closure_paths",
        lambda: (("interpreter/python", second_python), ("sandbox/bwrap", second_bwrap)),
    )
    assert runner_module._released_runtime_closure_digest() == first
    second_bwrap.write_bytes(b"changed sandbox runtime")
    assert runner_module._released_runtime_closure_digest() != first


def test_runner_identity_is_stable_across_interpreter_prefixes(
    tmp_path: Path, monkeypatch
) -> None:
    root, commit = _repository(tmp_path, "def test_widget(): assert True\n")
    profile = _profile(root, commit)
    monkeypatch.setattr("pdd.sync_core.runner.sys.executable", "/venv-a/bin/python")
    first = runner_identity_digest(profile, root=root, ref=commit)
    monkeypatch.setattr("pdd.sync_core.runner.sys.executable", "/venv-b/bin/python")
    assert runner_identity_digest(profile, root=root, ref=commit) == first


def test_runner_identity_binds_actual_supervisor_bytes(tmp_path: Path, monkeypatch) -> None:
    root, commit = _repository(tmp_path, "def test_widget(): assert True\n")
    profile = _profile(root, commit)
    first = runner_identity_digest(profile, root=root, ref=commit)
    source = Path(__file__).parents[1] / "pdd/sync_core/supervisor.py"
    changed = tmp_path / "supervisor.py"
    changed.write_bytes(source.read_bytes() + b"\n# changed checker semantics\n")
    monkeypatch.setattr("pdd.sync_core.supervisor.__file__", str(changed))
    assert runner_identity_digest(profile, root=root, ref=commit) != first


def test_runner_identity_binds_actual_pytest_bytes_and_ignores_prefix(
    tmp_path: Path, monkeypatch
) -> None:
    root, commit = _repository(tmp_path, "def test_widget(): assert True\n")
    profile = _profile(root, commit)
    pytest_source = Path(pytest.__file__).resolve()
    first_prefix = tmp_path / "venv-a"
    second_prefix = tmp_path / "venv-b"
    relative = Path("lib/python/site-packages/pytest/__init__.py")
    first_file = first_prefix / relative
    second_file = second_prefix / relative
    first_file.parent.mkdir(parents=True)
    second_file.parent.mkdir(parents=True)
    first_file.write_bytes(pytest_source.read_bytes())
    second_file.write_bytes(pytest_source.read_bytes())
    monkeypatch.setattr(pytest, "__file__", str(first_file))
    first = runner_identity_digest(profile, root=root, ref=commit)
    monkeypatch.setattr(pytest, "__file__", str(second_file))
    assert runner_identity_digest(profile, root=root, ref=commit) == first
    second_file.write_bytes(second_file.read_bytes() + b"\n# changed pytest semantics\n")
    assert runner_identity_digest(profile, root=root, ref=commit) != first


def test_pytest_plugin_guard_ignores_non_pytest_preview_prose(tmp_path: Path) -> None:
    root, _commit = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "setup.cfg").write_text(
        "[metadata]\ndescription = a -preview build\n", encoding="utf-8"
    )
    _git(root, "add", "setup.cfg")
    _git(root, "commit", "-q", "-m", "config prose")
    assert not _config_loads_plugin(root, _git(root, "rev-parse", "HEAD"))


@pytest.mark.parametrize("option", ["-p local_plugin", "-plocal_plugin", "-p=local_plugin"])
def test_pytest_plugin_guard_rejects_structured_pytest_addopts(
    tmp_path: Path, option: str
) -> None:
    root, _commit = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "setup.cfg").write_text(
        f"[tool:pytest]\naddopts = {option}\n", encoding="utf-8"
    )
    _git(root, "add", "setup.cfg")
    _git(root, "commit", "-q", "-m", "pytest plugin")
    assert _config_loads_plugin(root, _git(root, "rev-parse", "HEAD"))
