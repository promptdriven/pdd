"""Tests for pass-only trusted runner normalization and self-certification guards."""

import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

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
from pdd.sync_core.runner import pytest_validator_config_digest


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


def test_candidate_modified_helper_outside_tests_is_protected(tmp_path) -> None:
    root, _initial = _repository(
        tmp_path,
        "from support.fixtures import expected\n"
        "def test_widget(): assert expected() == 1\n",
    )
    (root / "support").mkdir()
    (root / "support/__init__.py").write_text("")
    (root / "support/fixtures.py").write_text("def expected(): return 1\n")
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
        "import os\nfrom pathlib import Path\n"
        "def test_widget():\n"
        "    Path('observed-secret').write_text("
        "os.environ.get('PDD_ATTESTATION_SIGNING_KEY', 'missing'))\n"
    )
    root, head = _repository(tmp_path, content)
    monkeypatch.setenv("PDD_ATTESTATION_SIGNING_KEY", "candidate-must-not-read")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS
    assert (root / "observed-secret").read_text() == "missing"


def test_pytest_execution_uses_private_home_and_userprofile(tmp_path, monkeypatch) -> None:
    protected_home = tmp_path / "protected-home"
    protected_home.mkdir()
    (protected_home / "secret.txt").write_text("protected-secret")
    monkeypatch.setenv("HOME", str(protected_home))
    monkeypatch.setenv("USERPROFILE", str(protected_home))
    content = (
        "import json, os\nfrom pathlib import Path\n"
        "def test_widget():\n"
        "    home = Path(os.environ['HOME'])\n"
        "    profile = Path(os.environ['USERPROFILE'])\n"
        "    Path('observed-execution-home.json').write_text(json.dumps({\n"
        "        'home': str(home),\n"
        "        'userprofile': str(profile),\n"
        "        'home_secret': (home / 'secret.txt').exists(),\n"
        "        'profile_secret': (profile / 'secret.txt').exists(),\n"
        "    }, sort_keys=True))\n"
    )
    root, head = _repository(tmp_path, content)
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS
    observed = json.loads((root / "observed-execution-home.json").read_text())
    assert observed["home"] != str(protected_home)
    assert observed["userprofile"] != str(protected_home)
    assert observed["home_secret"] is False
    assert observed["profile_secret"] is False


def test_pytest_collection_uses_private_home_and_userprofile(tmp_path, monkeypatch) -> None:
    protected_home = tmp_path / "protected-home"
    protected_home.mkdir()
    (protected_home / "secret.txt").write_text("protected-secret")
    monkeypatch.setenv("HOME", str(protected_home))
    monkeypatch.setenv("USERPROFILE", str(protected_home))
    root, head = _repository(tmp_path, "def test_widget(): assert True\n")
    (root / "conftest.py").write_text(
        "import json, os\nfrom pathlib import Path\n"
        "def pytest_collection_modifyitems(items):\n"
        "    home = Path(os.environ['HOME'])\n"
        "    profile = Path(os.environ['USERPROFILE'])\n"
        "    Path('observed-collection-home.json').write_text(json.dumps({\n"
        "        'home': str(home),\n"
        "        'userprofile': str(profile),\n"
        "        'home_secret': (home / 'secret.txt').exists(),\n"
        "        'profile_secret': (profile / 'secret.txt').exists(),\n"
        "    }, sort_keys=True))\n"
    )
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "collection hook")
    head = _git(root, "rev-parse", "HEAD")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS
    observed = json.loads((root / "observed-collection-home.json").read_text())
    assert observed["home"] != str(protected_home)
    assert observed["userprofile"] != str(protected_home)
    assert observed["home_secret"] is False
    assert observed["profile_secret"] is False


def test_validator_subprocess_cannot_read_signer_capabilities(tmp_path, monkeypatch) -> None:
    content = (
        "import json, os\nfrom pathlib import Path\n"
        "def test_widget():\n"
        "    Path('observed-capabilities.json').write_text(json.dumps({\n"
        "        'attestation_command': os.environ.get('PDD_ATTESTATION_SIGNER_COMMAND'),\n"
        "        'certificate_issuer': os.environ.get('PDD_CERTIFICATE_ISSUER'),\n"
        "        'released_checker': os.environ.get('PDD_RELEASED_CHECKER_COMMAND'),\n"
        "    }, sort_keys=True))\n"
    )
    root, head = _repository(tmp_path, content)
    monkeypatch.setenv("PDD_ATTESTATION_SIGNER_COMMAND", "protected-attestation")
    monkeypatch.setenv("PDD_CERTIFICATE_ISSUER", "protected-issuer")
    monkeypatch.setenv("PDD_RELEASED_CHECKER_COMMAND", "protected-checker")
    _envelope, executions = _run(root, head, head)
    assert executions[0].outcome is EvidenceOutcome.PASS
    assert json.loads((root / "observed-capabilities.json").read_text()) == {
        "attestation_command": None,
        "certificate_issuer": None,
        "released_checker": None,
    }


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
