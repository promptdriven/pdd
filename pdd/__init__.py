__version__ = "0.0.25"

# Strength parameter used for LLM extraction across the codebase
# Used in postprocessing, XML tagging, code generation, and other extraction operations. The module should have a large context window and be affordable.
EXTRACTION_STRENGTH = 0.97

DEFAULT_STRENGTH = 0.8