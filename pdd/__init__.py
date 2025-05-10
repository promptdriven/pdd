__version__ = "0.0.28"

# Strength parameter used for LLM extraction across the codebase
# Used in postprocessing, XML tagging, code generation, and other extraction operations. The module should have a large context window and be affordable.
EXTRACTION_STRENGTH = 0.9

DEFAULT_STRENGTH = 0.9

"""PDD - Prompt Driven Development"""

# Define constants used across the package
DEFAULT_LLM_MODEL = "gpt-4.1-nano"

# You can add other package-level initializations or imports here