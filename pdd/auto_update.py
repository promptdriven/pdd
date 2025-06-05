"""This module provides a function to automatically update the package."""
import importlib.metadata
import shutil
import subprocess
import sys
from typing import Optional
import requests
import semver


def detect_installation_method(sys_executable):
    """
    Detect if package is installed via UV or pip.
    
    Args:
        sys_executable (str): Path to the Python executable
    
    Returns:
        str: "uv" if installed via UV, "pip" otherwise
    """
    # Check if executable path contains UV paths
    if any(marker in sys_executable for marker in ["/uv/tools/", ".local/share/uv/"]):
        return "uv"
    return "pip"  # Default to pip for all other cases


def get_upgrade_command(package_name, installation_method):
    """
    Return appropriate upgrade command based on installation method.
    
    Args:
        package_name (str): Name of the package to upgrade
        installation_method (str): "uv" or "pip"
    
    Returns:
        tuple: (command_list, shell_mode) where command_list is the command to run
               and shell_mode is a boolean indicating if shell=True should be used
    """
    if installation_method == "uv":
        # For UV commands, we need the full path if available
        uv_path = shutil.which("uv")
        if uv_path:
            return ([uv_path, "tool", "install", package_name, "--force"], False)
        # If uv isn't in PATH, use shell=True
        return (["uv", "tool", "install", package_name, "--force"], True)
    # Default pip method
    return ([sys.executable, "-m", "pip", "install", "--upgrade", package_name], False)


def _get_latest_version(package_name: str) -> Optional[str]:
    """Fetch the latest version of a package from PyPI."""
    # pylint: disable=broad-except
    try:
        pypi_url = f"https://pypi.org/pypi/{package_name}/json"
        response = requests.get(pypi_url, timeout=10)
        response.raise_for_status()
        return response.json()['info']['version']
    except Exception as ex:
        print(f"Failed to fetch latest version from PyPI: {str(ex)}")
        return None


def _upgrade_package(package_name: str, installation_method: str):
    """Upgrade a package using the specified installation method."""
    cmd, use_shell = get_upgrade_command(package_name, installation_method)
    cmd_str = " ".join(cmd)
    print(f"\nDetected installation method: {installation_method}")
    print(f"Upgrading with command: {cmd_str}")

    # pylint: disable=broad-except
    try:
        result = subprocess.run(
            cmd,
            shell=use_shell,
            capture_output=True,
            text=True,
            check=False
        )
        if result.returncode == 0:
            print(f"\nSuccessfully upgraded {package_name}")
            return True
        print(f"\nUpgrade command failed: {result.stderr}")
        return False
    except Exception as ex:
        print(f"\nError during upgrade: {str(ex)}")
        return False


def _is_new_version_available(current_version: str, latest_version: str) -> bool:
    """Check if a new version is available."""
    try:
        current_semver = semver.VersionInfo.parse(current_version)
        latest_semver = semver.VersionInfo.parse(latest_version)
        return latest_semver > current_semver
    except ValueError:
        return latest_version != current_version


def auto_update(package_name: str = "pdd-cli", latest_version: str = None) -> None:
    """
    Check if there's a new version of the package available and prompt for upgrade.
    Handles both UV and pip installations automatically.
    
    Args:
        latest_version (str): Known latest version (default: None)
        package_name (str): Name of the package to check (default: "pdd-cli")
    """
    # pylint: disable=broad-except
    try:
        current_version = importlib.metadata.version(package_name)

        if latest_version is None:
            latest_version = _get_latest_version(package_name)
            if latest_version is None:
                return

        if not _is_new_version_available(current_version, latest_version):
            return

        print(f"\nNew version of {package_name} available: "
              f"{latest_version} (current: {current_version})")
        
        while True:
            response = input("Would you like to upgrade? [y/N]: ").lower().strip()
            if response in ['y', 'yes']:
                installation_method = detect_installation_method(sys.executable)
                if _upgrade_package(package_name, installation_method):
                    break
                
                if installation_method == "uv":
                    print("\nAttempting fallback to pip...")
                    if _upgrade_package(package_name, "pip"):
                        break
                
                break
            if response in ['n', 'no', '']:
                print("\nUpgrade cancelled")
                break
            print("Please answer 'y' or 'n'")

    except importlib.metadata.PackageNotFoundError:
        print(f"Package {package_name} is not installed")
    except Exception as ex:
        print(f"Error checking for updates: {str(ex)}")


if __name__ == "__main__":
    auto_update()