"""Unit tests for the auto_update module."""
import importlib
from unittest.mock import patch, MagicMock
import pytest
from pdd.auto_update import auto_update, detect_installation_method, get_upgrade_command

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