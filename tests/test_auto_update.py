"""Unit tests for the auto_update module."""
import importlib
import os
from unittest.mock import patch, MagicMock
import pytest
from pdd.auto_update import auto_update, detect_installation_method, get_upgrade_command


@pytest.fixture(autouse=True)
def clean_auto_update_env():
    """Ensure auto_update tests run with clean environment (no CI mode skips)."""
    # Save original values
    orig_ci = os.environ.get("CI")
    orig_skip = os.environ.get("PDD_SKIP_UPDATE_CHECK")
    orig_no_interactive = os.environ.get("PDD_NO_INTERACTIVE")

    # Clear the environment variables that cause early exit
    if "CI" in os.environ:
        del os.environ["CI"]
    if "PDD_SKIP_UPDATE_CHECK" in os.environ:
        del os.environ["PDD_SKIP_UPDATE_CHECK"]
    if "PDD_NO_INTERACTIVE" in os.environ:
        del os.environ["PDD_NO_INTERACTIVE"]

    # Mock isatty to return True (simulating interactive terminal)
    with patch("pdd.auto_update.sys.stdin.isatty", return_value=True), \
         patch("pdd.auto_update.sys.stdout.isatty", return_value=True):
        yield

    # Restore original values
    if orig_ci is not None:
        os.environ["CI"] = orig_ci
    if orig_skip is not None:
        os.environ["PDD_SKIP_UPDATE_CHECK"] = orig_skip
    if orig_no_interactive is not None:
        os.environ["PDD_NO_INTERACTIVE"] = orig_no_interactive


@pytest.fixture(name="mock_importlib_metadata_version")
def mock_importlib_metadata_version_fixture():
    """Mock the importlib.metadata.version function."""
    with patch("pdd.auto_update.importlib.metadata.version") as mock_version:
        yield mock_version

@pytest.fixture(name="mock_requests_get")
def mock_requests_get_fixture():
    """Mock the requests.get function."""
    with patch("pdd.auto_update.requests.get") as mock_get:
        yield mock_get

@pytest.fixture(name="mock_subprocess_check_call")
def mock_subprocess_check_call_fixture():
    """Mock the subprocess.check_call function."""
    with patch("pdd.auto_update.subprocess.check_call") as mock_check_call:
        yield mock_check_call

@pytest.fixture(name="mock_subprocess_run")
def mock_subprocess_run_fixture():
    """Mock the subprocess.run function."""
    with patch("pdd.auto_update.subprocess.run") as mock_run:
        yield mock_run
        
@pytest.fixture(name="mock_shutil_which")
def mock_shutil_which_fixture():
    """Mock the shutil.which function."""
    with patch("pdd.auto_update.shutil.which") as mock_which:
        yield mock_which

@pytest.fixture(name="mock_input")
def mock_input_fixture():
    """Mock the input function."""
    with patch("builtins.input") as mock_input_func:
        yield mock_input_func

def test_auto_update_no_new_version(
    mock_importlib_metadata_version, mock_requests_get
):
    """Test when the current version is the same as the latest version."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.0.0"}}
    )

    with patch("builtins.print") as mock_print:
        auto_update()
        mock_print.assert_not_called()

def test_auto_update_new_version_decline_upgrade(
    mock_importlib_metadata_version, mock_requests_get, mock_input
):
    """Test when a new version is available but the user declines the upgrade."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.1.0"}}
    )
    mock_input.return_value = "n"

    with patch("builtins.print") as mock_print:
        auto_update()
        assert any("New version of pdd-cli available" in call[0][0]
                   for call in mock_print.call_args_list)
        assert any("Upgrade cancelled" in call[0][0]
                   for call in mock_print.call_args_list)

def test_auto_update_new_version_accept_upgrade_pip(
    mock_importlib_metadata_version,
    mock_requests_get,
    mock_input,
    mock_subprocess_run
):
    """Test when a new version is available, the user accepts the upgrade, and pip is used."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.1.0"}}
    )
    mock_input.return_value = "y"
    mock_subprocess_run.return_value = MagicMock(returncode=0, stderr="")
    
    # Mock a non-UV path
    with patch("pdd.auto_update.sys.executable", "/usr/bin/python"):
        with patch("builtins.print") as mock_print:
            auto_update()
            assert any("New version of pdd-cli available" in call[0][0]
                       for call in mock_print.call_args_list)
            assert any("Detected installation method: pip" in call[0][0]
                       for call in mock_print.call_args_list)
            assert any("Upgrading with command:" in call[0][0]
                       for call in mock_print.call_args_list)
            assert mock_subprocess_run.called
            assert any("Successfully upgraded" in call[0][0]
                       for call in mock_print.call_args_list)


def test_auto_update_new_version_accept_upgrade_uv(
    mock_importlib_metadata_version,
    mock_requests_get,
    mock_input,
    mock_subprocess_run,
    mock_shutil_which,
):
    """Test when a new version is available, the user accepts the upgrade, and uv is used."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.1.0"}}
    )
    mock_input.return_value = "y"
    mock_subprocess_run.return_value = MagicMock(returncode=0, stderr="")
    mock_shutil_which.return_value = "/usr/local/bin/uv"
    
    # Mock a UV path
    with patch(
        "pdd.auto_update.sys.executable",
        "/Users/user/.local/share/uv/tools/pdd-cli/bin/python"
    ):
        with patch("builtins.print") as mock_print:
            auto_update()
            assert any("New version of pdd-cli available" in call[0][0]
                       for call in mock_print.call_args_list)
            assert any("Detected installation method: uv" in call[0][0]
                       for call in mock_print.call_args_list)
            assert any("Upgrading with command:" in call[0][0]
                       for call in mock_print.call_args_list)
            assert mock_subprocess_run.called
            assert any("Successfully upgraded" in call[0][0]
                       for call in mock_print.call_args_list)

def test_auto_update_package_not_installed(mock_importlib_metadata_version):
    """Test when the package is not installed."""
    mock_importlib_metadata_version.side_effect = \
        importlib.metadata.PackageNotFoundError

    with patch("builtins.print") as mock_print:
        auto_update()
        assert any("Package pdd-cli is not installed" in call[0][0]
                   for call in mock_print.call_args_list)

def test_auto_update_fetch_latest_version_failure(
    mock_importlib_metadata_version, mock_requests_get
):
    """Test when fetching the latest version from PyPI fails."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.side_effect = Exception("Network error")

    with patch("builtins.print") as mock_print:
        auto_update()
        assert any("Failed to fetch latest version from PyPI" in call[0][0]
                   for call in mock_print.call_args_list)

def test_auto_update_invalid_version_format(
    mock_importlib_metadata_version, mock_requests_get
):
    """Test when the version format is invalid and falls back to string comparison."""
    mock_importlib_metadata_version.return_value = "1.0.0x"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.0.0x"}}
    )

    with patch("builtins.print") as mock_print:
        auto_update()
        mock_print.assert_not_called()

def test_auto_update_semver_comparison(
    mock_importlib_metadata_version, mock_requests_get
):
    """Test semantic versioning comparison."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.0.1"}}
    )

    with patch("builtins.print") as mock_print:
        auto_update()
        assert any("New version of pdd-cli available" in call[0][0]
                   for call in mock_print.call_args_list)


def test_detect_uv_installation():
    """Test detection of UV installation."""
    # Test UV tool paths
    assert detect_installation_method(
        "/Users/user/.local/share/uv/tools/pdd-cli/bin/python"
    ) == "uv"
    assert detect_installation_method(
        "/home/user/.local/share/uv/tools/pdd-cli/bin/python"
    ) == "uv"
    assert detect_installation_method(
        "/opt/uv/tools/pdd-cli/bin/python"
    ) == "uv"


def test_detect_pip_installation():
    """Test detection of pip installation."""
    # Test standard Python paths
    assert detect_installation_method("/usr/bin/python") == "pip"
    assert detect_installation_method("/usr/local/bin/python") == "pip"
    assert detect_installation_method("C:\\Python39\\python.exe") == "pip"
    assert detect_installation_method(
        "/home/user/.pyenv/versions/3.9.0/bin/python"
    ) == "pip"


def test_detect_uv_installation_windows():
    """Test detection of UV installation on Windows with backslash paths."""
    # Test Windows UV tool paths with backslashes
    assert detect_installation_method(
        r"C:\Users\pmbri\AppData\Roaming\uv\tools\pdd-cli\Scripts\python.exe"
    ) == "uv"
    assert detect_installation_method(
        r"C:\Users\user\.local\share\uv\tools\pdd-cli\Scripts\python.exe"
    ) == "uv"
    assert detect_installation_method(
        r"D:\uv\tools\pdd-cli\bin\python.exe"
    ) == "uv"
    # Test with forward slashes on Windows (some tools normalize paths)
    assert detect_installation_method(
        "C:/Users/user/AppData/Roaming/uv/tools/pdd-cli/Scripts/python.exe"
    ) == "uv"


def test_get_upgrade_command():
    """Test that the correct upgrade commands are generated."""
    # Test UV command generation
    uv_cmd, uv_shell = get_upgrade_command("pdd-cli", "uv")
    assert "tool" in uv_cmd
    assert "install" in uv_cmd
    assert "--force" in uv_cmd
    assert "pdd-cli" in uv_cmd
    assert isinstance(uv_shell, bool)
    
    # Test pip command generation
    pip_cmd, pip_shell = get_upgrade_command("pdd-cli", "pip")
    assert "-m" in pip_cmd
    assert "pip" in pip_cmd
    assert "install" in pip_cmd
    assert "--upgrade" in pip_cmd
    assert "pdd-cli" in pip_cmd
    assert isinstance(pip_shell, bool)

# ---------------------------------------------------------------------------
# Issue #2345: never check for or install updates in non-interactive contexts
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "env",
    [
        {"CI": "true"},
        {"CI": "1"},
        {"PDD_NO_INTERACTIVE": "1"},
        {"PDD_NO_INTERACTIVE": "true"},
        {"PDD_SKIP_UPDATE_CHECK": "1"},
        {"PDD_SKIP_UPDATE_CHECK": "true"},
    ],
)
def test_issue_2345_auto_update_skips_in_machine_mode(
    env, monkeypatch, mock_requests_get, mock_input, mock_subprocess_run
):
    """Issue #2345: CI and explicit no-interactive flags skip the update check entirely."""
    for key, value in env.items():
        monkeypatch.setenv(key, value)
    mock_input.return_value = "n"

    auto_update()

    mock_requests_get.assert_not_called()
    mock_input.assert_not_called()
    mock_subprocess_run.assert_not_called()


def test_issue_2345_auto_update_skips_when_stdout_not_tty(
    mock_requests_get, mock_input, mock_subprocess_run
):
    """Issue #2345: redirected stdout (e.g. piped into a log) is non-interactive."""
    mock_input.return_value = "n"
    with patch("pdd.auto_update.sys.stdout.isatty", return_value=False):
        auto_update()

    mock_requests_get.assert_not_called()
    mock_input.assert_not_called()
    mock_subprocess_run.assert_not_called()


def test_issue_2345_falsey_ci_does_not_disable_update_check(monkeypatch):
    """Issue #2345: CI=false in an interactive terminal keeps the update check."""
    from pdd.auto_update import is_update_check_disabled

    monkeypatch.setenv("CI", "false")
    with patch("pdd.auto_update.sys.stdout.isatty", return_value=True):
        assert is_update_check_disabled() is False


def test_issue_2345_uv_missing_from_path_never_uses_shell(mock_shutil_which):
    """Issue #2345: the upgrade command is always an explicit argv, never shell=True."""
    mock_shutil_which.return_value = None

    cmd, use_shell = get_upgrade_command("pdd-cli", "uv")

    assert use_shell is False
    assert cmd == ["uv", "tool", "install", "pdd-cli", "--force"]


def test_issue_2345_upgrade_subprocess_runs_without_shell(mock_shutil_which, mock_subprocess_run):
    """Issue #2345: the upgrade subprocess is invoked with shell=False."""
    from pdd.auto_update import _upgrade_package

    mock_shutil_which.return_value = None
    mock_subprocess_run.return_value = MagicMock(returncode=0)

    _upgrade_package("pdd-cli", "uv")

    assert mock_subprocess_run.call_args.kwargs["shell"] is False


def test_issue_2345_cli_does_not_announce_skipped_update_check(monkeypatch):
    """Issue #2345: the CLI must not print 'Checking for updates...' when the check is skipped."""
    from click.testing import CliRunner
    from pdd.core.cli import cli

    monkeypatch.delenv("PDD_AUTO_UPDATE", raising=False)
    monkeypatch.setenv("CI", "true")
    with patch("pdd.core.cli.auto_update"):
        result = CliRunner().invoke(cli, [])

    assert "Checking for updates" not in result.output
