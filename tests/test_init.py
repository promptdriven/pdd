"""
Test suite for pdd/__init__.py module.

Test Plan:

1.  **Cloud Defaults Setup Tests (`_setup_cloud_defaults`)**:
    *   Verify default Firebase API key is set when not already present.
    *   Verify default GitHub Client ID is set when not already present.
    *   Verify existing environment variables are NOT overridden.
    *   Verify defaults are NOT set when K_SERVICE is present (cloud environment).
    *   Verify defaults are NOT set when FUNCTIONS_EMULATOR is present (emulator).
    *   Verify the default values match expected public keys.

"""

import os
import importlib
import pytest
from unittest.mock import patch


# Store the expected default values (must match pdd/__init__.py)
EXPECTED_FIREBASE_KEY = "AIzaSyC0w2jwRR82ZFgQs_YXJoEBqnnTH71X6BE"
EXPECTED_GITHUB_CLIENT_ID = "Ov23liJ4eSm0y5W1L20u"


@pytest.fixture
def clean_env():
    """Fixture to ensure environment is clean before and after tests."""
    # Store original values
    original_env = os.environ.copy()

    # Clear relevant keys
    keys_to_clear = [
        "NEXT_PUBLIC_FIREBASE_API_KEY",
        "GITHUB_CLIENT_ID",
        "K_SERVICE",
        "FUNCTIONS_EMULATOR",
    ]
    for key in keys_to_clear:
        if key in os.environ:
            del os.environ[key]

    yield

    # Restore original values
    os.environ.clear()
    os.environ.update(original_env)


class TestSetupCloudDefaults:
    """Tests for the _setup_cloud_defaults function."""

    def test_sets_firebase_key_when_not_present(self, clean_env):
        """Test that Firebase API key is set when not already in environment."""
        # Import fresh to trigger _setup_cloud_defaults
        import pdd
        pdd._setup_cloud_defaults()

        assert os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY") == EXPECTED_FIREBASE_KEY

    def test_sets_github_client_id_when_not_present(self, clean_env):
        """Test that GitHub Client ID is set when not already in environment."""
        import pdd
        pdd._setup_cloud_defaults()

        assert os.environ.get("GITHUB_CLIENT_ID") == EXPECTED_GITHUB_CLIENT_ID

    def test_does_not_override_existing_firebase_key(self, clean_env):
        """Test that existing Firebase API key is not overridden."""
        custom_key = "my-custom-firebase-key"
        os.environ["NEXT_PUBLIC_FIREBASE_API_KEY"] = custom_key

        import pdd
        pdd._setup_cloud_defaults()

        assert os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY") == custom_key

    def test_does_not_override_existing_github_client_id(self, clean_env):
        """Test that existing GitHub Client ID is not overridden."""
        custom_id = "my-custom-github-id"
        os.environ["GITHUB_CLIENT_ID"] = custom_id

        import pdd
        pdd._setup_cloud_defaults()

        assert os.environ.get("GITHUB_CLIENT_ID") == custom_id

    def test_skips_setup_when_k_service_is_set(self, clean_env):
        """Test that defaults are NOT set when running in Cloud Functions (K_SERVICE)."""
        os.environ["K_SERVICE"] = "my-cloud-function"

        import pdd
        pdd._setup_cloud_defaults()

        # Should NOT have set the defaults
        assert os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY") is None
        assert os.environ.get("GITHUB_CLIENT_ID") is None

    def test_skips_setup_when_functions_emulator_is_set(self, clean_env):
        """Test that defaults are NOT set when running in emulator."""
        os.environ["FUNCTIONS_EMULATOR"] = "true"

        import pdd
        pdd._setup_cloud_defaults()

        # Should NOT have set the defaults
        assert os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY") is None
        assert os.environ.get("GITHUB_CLIENT_ID") is None

    def test_default_values_are_correct(self, clean_env):
        """Test that the embedded default values are the expected public keys."""
        import pdd

        assert pdd._DEFAULT_FIREBASE_API_KEY == EXPECTED_FIREBASE_KEY
        assert pdd._DEFAULT_GITHUB_CLIENT_ID == EXPECTED_GITHUB_CLIENT_ID

    def test_partial_override_firebase_only(self, clean_env):
        """Test that only missing keys are set when one is already present."""
        custom_key = "custom-firebase-key"
        os.environ["NEXT_PUBLIC_FIREBASE_API_KEY"] = custom_key

        import pdd
        pdd._setup_cloud_defaults()

        # Firebase should keep custom value
        assert os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY") == custom_key
        # GitHub should get default
        assert os.environ.get("GITHUB_CLIENT_ID") == EXPECTED_GITHUB_CLIENT_ID

    def test_partial_override_github_only(self, clean_env):
        """Test that only missing keys are set when one is already present."""
        custom_id = "custom-github-id"
        os.environ["GITHUB_CLIENT_ID"] = custom_id

        import pdd
        pdd._setup_cloud_defaults()

        # Firebase should get default
        assert os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY") == EXPECTED_FIREBASE_KEY
        # GitHub should keep custom value
        assert os.environ.get("GITHUB_CLIENT_ID") == custom_id


class TestModuleConstants:
    """Tests for module-level constants."""

    def test_version_is_string(self):
        """Test that __version__ is a string."""
        import pdd
        assert isinstance(pdd.__version__, str)

    def test_version_format(self):
        """Test that __version__ follows semantic versioning format."""
        import pdd
        parts = pdd.__version__.split(".")
        assert len(parts) >= 2, "Version should have at least major.minor"
        # Each part should be numeric (or numeric with suffix for pre-releases)
        assert parts[0].isdigit(), "Major version should be numeric"
        assert parts[1].isdigit(), "Minor version should be numeric"

    def test_default_constants_exist(self):
        """Test that expected default constants are defined."""
        import pdd
        assert hasattr(pdd, "EXTRACTION_STRENGTH")
        assert hasattr(pdd, "DEFAULT_STRENGTH")
        assert hasattr(pdd, "DEFAULT_TEMPERATURE")
        assert hasattr(pdd, "DEFAULT_TIME")
        assert hasattr(pdd, "DEFAULT_LLM_MODEL")
