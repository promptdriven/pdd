"""PDD - Prompt Driven Development"""

import os

__version__ = "0.0.135"

# Strength parameter used for LLM extraction across the codebase
# Used in postprocessing, XML tagging, code generation, and other extraction
# operations. The module should have a large context window and be affordable.
EXTRACTION_STRENGTH = 0.5

DEFAULT_STRENGTH = 1.0

DEFAULT_TEMPERATURE = 0.0

DEFAULT_TIME = 0.25

# Public OAuth credentials for cloud mode
# These are safe to embed as they are public client identifiers:
# - Firebase API keys are designed to be public (client-side)
# - GitHub OAuth Client IDs are public (the secret stays server-side)
# Users still need to authenticate via GitHub OAuth to use cloud features.
_DEFAULT_FIREBASE_API_KEY = "AIzaSyC0w2jwRR82ZFgQs_YXJoEBqnnTH71X6BE"
_DEFAULT_GITHUB_CLIENT_ID = "Ov23liJ4eSm0y5W1L20u"


def _setup_cloud_defaults() -> None:
    """Set up default cloud credentials if not already set.

    Only sets defaults when:
    1. Not running inside cloud environment (K_SERVICE or FUNCTIONS_EMULATOR)
    2. Environment variables are not already set

    This prevents infinite loops when cloud endpoints call CLI internally,
    while providing a seamless experience for local users.
    """
    # Skip if running in cloud environment to prevent infinite loops
    if os.environ.get("K_SERVICE") or os.environ.get("FUNCTIONS_EMULATOR"):
        return

    # Set Firebase API key if not already set
    if not os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY"):
        os.environ["NEXT_PUBLIC_FIREBASE_API_KEY"] = _DEFAULT_FIREBASE_API_KEY

    # Set GitHub Client ID if not already set
    if not os.environ.get("GITHUB_CLIENT_ID"):
        os.environ["GITHUB_CLIENT_ID"] = _DEFAULT_GITHUB_CLIENT_ID


# Initialize cloud defaults on package import
_setup_cloud_defaults()

