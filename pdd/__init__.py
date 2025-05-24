__version__ = "0.0.32"

# Strength parameter used for LLM extraction across the codebase
# Used in postprocessing, XML tagging, code generation, and other extraction operations. The module should have a large context window and be affordable.
EXTRACTION_STRENGTH = 0.9

DEFAULT_STRENGTH = 0.9

DEFAULT_TEMPERATURE = 0.0

DEFAULT_TIME = 0.25

"""PDD - Prompt Driven Development"""

# Define constants used across the package
DEFAULT_LLM_MODEL = "gpt-4.1-nano"
# When going to production, set the following constants:
# REACT_APP_FIREBASE_API_KEY
# GITHUB_CLIENT_ID

# You can add other package-level initializations or imports here

