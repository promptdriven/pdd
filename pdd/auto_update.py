import importlib.metadata
import requests
import semver
import subprocess
import sys

def auto_update(package_name: str = "pdd-cli", latest_version: str = None) -> None:
    """
    Check if there's a new version of the package available and prompt for upgrade.
    
    Args:
        latest_version (str): Known latest version (default: None)
        package_name (str): Name of the package to check (default: "pdd")
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
                # Construct pip command
                pip_command = f"{sys.executable} -m pip install --upgrade {package_name}"
                print(f"\nUpgrading with command: {pip_command}")
                
                try:
                    subprocess.check_call(pip_command.split())
                    print(f"\nSuccessfully upgraded {package_name} to version {latest_version}")
                except subprocess.CalledProcessError as e:
                    print(f"\nFailed to upgrade: {str(e)}")
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