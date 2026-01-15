"""This module provides a function to automatically update the package.

It can detect whether the current tool was installed via UV or pip, check
PyPI for a newer version, prompt the user, and perform an upgrade using the
appropriate installer with sensible fallbacks.
"""
import importlib.metadata
import os
import shutil
import subprocess
import sys
from typing import Optional, Tuple, List

import requests
import semver


def detect_installation_method(sys_executable: str) -> str:
    """Detect whether the package is installed via UV or pip.

    The detection is based on the path of the Python executable. The path is
    normalized so that both Unix ("/") and Windows ("\\") separators are
    handled uniformly. If typical UV tool installation markers are present in
    the normalized path, "uv" is returned; otherwise "pip" is returned.

    Args:
        sys_executable: Path to the Python executable (e.g. ``sys.executable``).

    Returns:
        "uv" if a UV-style installation path is detected, otherwise "pip".
    """
    # Normalize path separators to support both Unix (/) and Windows (\) paths
    normalized_path = sys_executable.replace("\\", "/")

    # Check if executable path contains UV paths
    if any(marker in normalized_path for marker in ["/uv/tools/", ".local/share/uv/"]):
        return "uv"
    return "pip"  # Default to pip for all other cases


def get_upgrade_command(package_name: str, installation_method: str) -> Tuple[List[str], bool]:
    """Build the appropriate upgrade command based on the installation method.

    For UV, this uses ``uv tool install --force``. For pip, this uses
    ``python -m pip install --upgrade`` with the current Python executable.

    Args:
        package_name: Name of the package to upgrade.
        installation_method: Either ``"uv"`` or ``"pip"``.

    Returns:
        A tuple ``(command_list, shell_mode)`` where ``command_list`` is the
        command and its arguments as a list of strings, and ``shell_mode`` is a
        boolean indicating whether ``subprocess.run`` should be invoked with
        ``shell=True``.
    """
    if installation_method == "uv":
        # For UV commands, we need the full path if available
        uv_path = shutil.which("uv")
        if uv_path:
            return [uv_path, "tool", "install", package_name, "--force"], False
        # If uv isn't in PATH, use shell=True
        return ["uv", "tool", "install", package_name, "--force"], True

    # Default pip method
    return [sys.executable, "-m", "pip", "install", "--upgrade", package_name], False


def _get_latest_version(package_name: str) -> Optional[str]:
    """Fetch the latest version of a package from PyPI.

    This queries the JSON API at ``https://pypi.org/pypi/<package_name>/json``
    with a timeout and extracts the ``info.version`` field.

    Any exception results in a user-friendly error message and ``None`` being
    returned.

    Args:
        package_name: The name of the package to query.

    Returns:
        The latest version string if it could be fetched, otherwise ``None``.
    """
    # pylint: disable=broad-except
    try:
        pypi_url = f"https://pypi.org/pypi/{package_name}/json"
        response = requests.get(pypi_url, timeout=10)
        response.raise_for_status()
        return response.json()["info"]["version"]
    except Exception as ex:  # noqa: BLE001
        print(f"Failed to fetch latest version from PyPI: {str(ex)}")
        return None


def _upgrade_package(package_name: str, installation_method: str) -> bool:
    """Upgrade a package using the specified installation method.

    This runs the command returned by :func:`get_upgrade_command`, captures
    stdout/stderr, and reports success or failure.

    Args:
        package_name: Name of the package to upgrade.
        installation_method: Either ``"uv"`` or ``"pip"``.

    Returns:
        ``True`` if the upgrade command succeeded (exit code 0), otherwise
        ``False``.
    """
    cmd, use_shell = get_upgrade_command(package_name, installation_method)
    cmd_str = " ".join(cmd)
    print(f"\nDetected installation method: {installation_method}")
    print(f"Upgrading with command: {cmd_str}")

    # pylint: disable=broad-except
    try:
        result = subprocess.run(  # noqa: PLW1510
            cmd,
            shell=use_shell,
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode == 0:
            print(f"\nSuccessfully upgraded {package_name}")
            return True
        print(f"\nUpgrade command failed: {result.stderr}")
        return False
    except Exception as ex:  # noqa: BLE001
        print(f"\nError during upgrade: {str(ex)}")
        return False


def _is_new_version_available(current_version: str, latest_version: str) -> bool:
    """Determine whether a newer version is available.

    Semantic versioning is used when possible via :mod:`semver`. If parsing
    fails for either version string, the function falls back to a simple
    inequality comparison of the raw strings.

    Args:
        current_version: The currently installed version string.
        latest_version: The latest available version string.

    Returns:
        ``True`` if ``latest_version`` is considered newer than
        ``current_version``, otherwise ``False``.
    """
    try:
        current_semver = semver.VersionInfo.parse(current_version)
        latest_semver = semver.VersionInfo.parse(latest_version)
        return latest_semver > current_semver
    except ValueError:
        return latest_version != current_version


def auto_update(package_name: str = "pdd-cli", latest_version: Optional[str] = None) -> None:
    """Check PyPI for a newer version of the package and offer to upgrade.

    This function:

    * Determines the currently installed version using :mod:`importlib.metadata`.
    * Optionally accepts a pre-fetched ``latest_version`` for testing; if not
      supplied it will query PyPI.
    * Compares versions using semantic versioning with a string comparison
      fallback.
    * Interactively prompts the user for confirmation before upgrading.
    * Performs the upgrade using UV or pip depending on installation method,
      with a pip fallback if a UV upgrade fails.

    Args:
        package_name: Name of the package to check (default: ``"pdd-cli"``).
        latest_version: Optionally, a known latest version to use instead of
            querying PyPI (primarily for testing).

    Returns:
        None. All feedback is provided via ``print`` statements.
    """
    # Skip update check in CI mode, headless mode, or when stdin is not a TTY
    if (os.environ.get('CI') == '1' or
        os.environ.get('PDD_SKIP_UPDATE_CHECK') == '1' or
        not sys.stdin.isatty()):
        return

    # pylint: disable=broad-except
    try:
        current_version = importlib.metadata.version(package_name)

        if latest_version is None:
            latest_version = _get_latest_version(package_name)
            if latest_version is None:
                return

        if not _is_new_version_available(current_version, latest_version):
            return

        print(
            f"\nNew version of {package_name} available: "
            f"{latest_version} (current: {current_version})",
        )

        while True:
            response = input("Would you like to upgrade? [y/N]: ").lower().strip()
            if response in ["y", "yes"]:
                installation_method = detect_installation_method(sys.executable)
                if _upgrade_package(package_name, installation_method):
                    break

                if installation_method == "uv":
                    print("\nAttempting fallback to pip...")
                    if _upgrade_package(package_name, "pip"):
                        break

                break
            if response in ["n", "no", ""]:
                print("\nUpgrade cancelled")
                break
            print("Please answer 'y' or 'n'")

    except importlib.metadata.PackageNotFoundError:
        print(f"Package {package_name} is not installed")
    except Exception as ex:  # noqa: BLE001
        print(f"Error checking for updates: {str(ex)}")


if __name__ == "__main__":
    auto_update()
