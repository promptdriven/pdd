# Example usage of auto_update function
from pdd.auto_update import auto_update, is_update_check_disabled

def main():
    """
    Demonstrates different ways to use the auto_update function.

    The function will:
    1. Check the current installed version
    2. Compare it with the latest version (from PyPI or provided)
    3. If a newer version exists, prompt for upgrade
    4. If user confirms, perform the upgrade using pip

    No output if the package is up to date.
    """
    # True in CI, with PDD_NO_INTERACTIVE/PDD_SKIP_UPDATE_CHECK, or without a TTY;
    # auto_update() is then a silent no-op.
    if not is_update_check_disabled():
        print("Checking for updates...")

    # Basic usage - check for updates of 'pdd' package
    auto_update()

    # Check updates for a specific package
    auto_update(package_name="requests")

    # Check against a known version
    auto_update(package_name="pandas", latest_version="2.0.0")

if __name__ == "__main__":
    main()