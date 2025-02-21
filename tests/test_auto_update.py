# File: output/test_auto_update.py

import pytest
import importlib
from unittest.mock import patch, MagicMock
from pdd.auto_update import auto_update

@pytest.fixture
def mock_importlib_metadata_version():
    """Mock the importlib.metadata.version function."""
    with patch("pdd.auto_update.importlib.metadata.version") as mock_version:
        yield mock_version

@pytest.fixture
def mock_requests_get():
    """Mock the requests.get function."""
    with patch("pdd.auto_update.requests.get") as mock_get:
        yield mock_get

@pytest.fixture
def mock_subprocess_check_call():
    """Mock the subprocess.check_call function."""
    with patch("pdd.auto_update.subprocess.check_call") as mock_check_call:
        yield mock_check_call

@pytest.fixture
def mock_input():
    """Mock the input function."""
    with patch("builtins.input") as mock_input_func:
        yield mock_input_func

def test_auto_update_no_new_version(mock_importlib_metadata_version, mock_requests_get):
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
        assert any("New version of pdd-cli available" in call[0][0] for call in mock_print.call_args_list)
        assert any("Upgrade cancelled" in call[0][0] for call in mock_print.call_args_list)

def test_auto_update_new_version_accept_upgrade(
    mock_importlib_metadata_version, mock_requests_get, mock_input, mock_subprocess_check_call
):
    """Test when a new version is available and the user accepts the upgrade."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.1.0"}}
    )
    mock_input.return_value = "y"

    with patch("builtins.print") as mock_print:
        auto_update()
        assert any("New version of pdd-cli available" in call[0][0] for call in mock_print.call_args_list)
        assert any("Upgrading with command" in call[0][0] for call in mock_print.call_args_list)
        mock_subprocess_check_call.assert_called_once()

def test_auto_update_package_not_installed(mock_importlib_metadata_version):
    """Test when the package is not installed."""
    mock_importlib_metadata_version.side_effect = importlib.metadata.PackageNotFoundError

    with patch("builtins.print") as mock_print:
        auto_update()
        assert any("Package pdd-cli is not installed" in call[0][0] for call in mock_print.call_args_list)

def test_auto_update_fetch_latest_version_failure(mock_importlib_metadata_version, mock_requests_get):
    """Test when fetching the latest version from PyPI fails."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.side_effect = Exception("Network error")

    with patch("builtins.print") as mock_print:
        auto_update()
        assert any("Failed to fetch latest version from PyPI" in call[0][0] for call in mock_print.call_args_list)

def test_auto_update_invalid_version_format(mock_importlib_metadata_version, mock_requests_get):
    """Test when the version format is invalid and falls back to string comparison."""
    mock_importlib_metadata_version.return_value = "1.0.0x"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.0.0x"}}
    )

    with patch("builtins.print") as mock_print:
        auto_update()
        mock_print.assert_not_called()

def test_auto_update_semver_comparison(mock_importlib_metadata_version, mock_requests_get):
    """Test semantic versioning comparison."""
    mock_importlib_metadata_version.return_value = "1.0.0"
    mock_requests_get.return_value = MagicMock(
        status_code=200, json=lambda: {"info": {"version": "1.0.1"}}
    )

    with patch("builtins.print") as mock_print:
        auto_update()
        assert any("New version of pdd-cli available" in call[0][0] for call in mock_print.call_args_list)