import importlib.metadata
import requests
import semver
import subprocess
import sys
import shutil

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
        else:
            # If uv isn't in PATH, use shell=True
            return (["uv", "tool", "install", package_name, "--force"], True)
    else:
        # Default pip method
        return ([sys.executable, "-m", "pip", "install", "--upgrade", package_name], False)


def auto_update(package_name: str = "pdd-cli", latest_version: str = None) -> None:
    """
    Check if there's a new version of the package available and prompt for upgrade.
    Handles both UV and pip installations automatically.
    
    Args:
        latest_version (str): Known latest version (default: None)
        package_name (str): Name of the package to check (default: "pdd-cli")
    """
    try:
        # Get current installed version
        current_version = importlib.metadata.version(package_name)

        # If latest_version is not provided, fetch from PyPI
        if latest_version is None:
            try:
                pypi_url = f"https://pypi.org/pypi/{package_name}/json"
                response = requests.get(pypi_url)
                response.raise_for_status()
                latest_version = response.json()['info']['version']
            except Exception as e:
                print(f"Failed to fetch latest version from PyPI: {str(e)}")
                return

        # Compare versions using semantic versioning
        try:
            current_semver = semver.VersionInfo.parse(current_version)
            latest_semver = semver.VersionInfo.parse(latest_version)
        except ValueError:
            # If versions don't follow semantic versioning, fall back to string comparison
            if current_version == latest_version:
                return
        else:
            # If versions follow semantic versioning, compare properly
            if current_semver >= latest_semver:
                return

        # If we get here, there's a new version available
        print(f"\nNew version of {package_name} available: {latest_version} (current: {current_version})")
        
        # Ask for user confirmation
        while True:
            response = input("Would you like to upgrade? [y/N]: ").lower().strip()
            if response in ['y', 'yes']:
                # Detect installation method
                installation_method = detect_installation_method(sys.executable)
                cmd, use_shell = get_upgrade_command(package_name, installation_method)
                
                cmd_str = " ".join(cmd)
                print(f"\nDetected installation method: {installation_method}")
                print(f"Upgrading with command: {cmd_str}")
                
                try:
                    result = subprocess.run(cmd, shell=use_shell, capture_output=True, text=True)
                    
                    if result.returncode == 0:
                        print(f"\nSuccessfully upgraded {package_name} to version {latest_version}")
                    else:
                        print(f"\nUpgrade command failed: {result.stderr}")
                        
                        # If UV failed and we're not already in fallback mode, try pip as fallback
                        if installation_method == "uv":
                            print("\nAttempting fallback to pip...")
                            fallback_cmd, fallback_shell = get_upgrade_command(package_name, "pip")
                            fallback_str = " ".join(fallback_cmd)
                            print(f"Fallback command: {fallback_str}")
                            
                            try:
                                fallback_result = subprocess.run(fallback_cmd, shell=fallback_shell, capture_output=True, text=True)
                                if fallback_result.returncode == 0:
                                    print(f"\nSuccessfully upgraded {package_name} using fallback method")
                                else:
                                    print(f"\nFallback upgrade failed: {fallback_result.stderr}")
                            except Exception as fallback_err:
                                print(f"\nError during fallback upgrade: {str(fallback_err)}")
                except Exception as e:
                    print(f"\nError during upgrade: {str(e)}")
                break
            elif response in ['n', 'no', '']:
                print("\nUpgrade cancelled")
                break
            else:
                print("Please answer 'y' or 'n'")

    except importlib.metadata.PackageNotFoundError:
        print(f"Package {package_name} is not installed")
    except Exception as e:
        print(f"Error checking for updates: {str(e)}")


if __name__ == "__main__":
    auto_update()