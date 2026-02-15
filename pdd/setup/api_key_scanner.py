"""
pdd/setup/api_key_scanner.py

Discovers API keys from CSV providers, checking existence across
shell, .env, and PDD config with source transparency.
"""

import csv
import logging
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional

logger = logging.getLogger(__name__)


@dataclass
class KeyInfo:
    """Information about an API key's availability."""
    source: str
    is_set: bool


def _get_csv_path() -> Path:
    """Return the path to the master llm_model.csv file."""
    # Navigate from this file's location to pdd/data/llm_model.csv
    module_dir = Path(__file__).resolve().parent  # pdd/setup/
    pdd_dir = module_dir.parent  # pdd/
    return pdd_dir / "data" / "llm_model.csv"


def get_provider_key_names() -> List[str]:
    """
    Returns a deduplicated, sorted list of all non-empty api_key values
    from the master CSV (pdd/data/llm_model.csv).

    Returns an empty list if the CSV is missing or malformed.
    """
    csv_path = _get_csv_path()
    key_names: set = set()

    try:
        if not csv_path.exists():
            logger.warning("llm_model.csv not found at %s", csv_path)
            return []

        with open(csv_path, "r", newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)

            if reader.fieldnames is None or "api_key" not in reader.fieldnames:
                logger.warning(
                    "llm_model.csv at %s is missing the 'api_key' column.", csv_path
                )
                return []

            for row in reader:
                api_key_name = row.get("api_key", "").strip()
                if api_key_name:
                    key_names.add(api_key_name)

    except Exception as e:
        logger.error("Error reading llm_model.csv: %s", e)
        return []

    return sorted(key_names)


def _load_dotenv_values() -> Dict[str, str]:
    """
    Load values from a .env file using python-dotenv's dotenv_values (read-only).
    Returns an empty dict on any failure.
    """
    try:
        from dotenv import dotenv_values  # type: ignore

        values = dotenv_values()
        # dotenv_values returns an OrderedDict; values can be None for keys without values
        return {k: v for k, v in values.items() if v is not None}
    except ImportError:
        logger.debug("python-dotenv not installed; skipping .env file check.")
        return {}
    except Exception as e:
        logger.error("Error loading .env file: %s", e)
        return {}


def _detect_shell() -> Optional[str]:
    """
    Detect the current shell name from the SHELL environment variable.
    Returns the shell name (e.g. 'zsh', 'bash') or None if not detectable.
    """
    shell_path = os.environ.get("SHELL", "")
    if shell_path:
        return os.path.basename(shell_path)
    return None


def _parse_api_env_file(file_path: Path) -> Dict[str, str]:
    """
    Parse a ~/.pdd/api-env.{shell} file for uncommented `export KEY=value` lines.
    Returns a dict of key names to values found.
    """
    result: Dict[str, str] = {}

    try:
        if not file_path.exists():
            logger.debug("api-env file not found at %s", file_path)
            return result

        with open(file_path, "r", encoding="utf-8") as f:
            for line in f:
                stripped = line.strip()

                # Skip empty lines and comments
                if not stripped or stripped.startswith("#"):
                    continue

                # Match lines like: export KEY=value or export KEY="value"
                if stripped.startswith("export "):
                    remainder = stripped[len("export "):].strip()
                    if "=" in remainder:
                        key, _, value = remainder.partition("=")
                        key = key.strip()
                        value = value.strip()

                        # Remove surrounding quotes if present
                        if len(value) >= 2 and (
                            (value.startswith('"') and value.endswith('"'))
                            or (value.startswith("'") and value.endswith("'"))
                        ):
                            value = value[1:-1]

                        if key and value:
                            result[key] = value

    except Exception as e:
        logger.error("Error parsing api-env file %s: %s", file_path, e)

    return result


def scan_environment() -> Dict[str, KeyInfo]:
    """
    Scan for API key existence across all known sources.

    Checks sources in priority order:
      1. .env file (via python-dotenv dotenv_values, read-only)
      2. Shell environment (os.environ - note: may include stale .env values if edited during session)
      3. ~/.pdd/api-env.{shell} file

    Returns a mapping of key name -> KeyInfo(source, is_set).
    Never raises exceptions; returns best-effort results.

    Note: If you edit .env during a pdd setup session, restart pdd setup to see updated shell environment.
    """
    result: Dict[str, KeyInfo] = {}

    try:
        key_names = get_provider_key_names()

        if not key_names:
            logger.info("No API key names discovered from CSV.")
            return result

        # Load all sources once
        dotenv_vals = _load_dotenv_values()
        shell_name = _detect_shell()

        api_env_file_path: Optional[Path] = None
        api_env_vals: Dict[str, str] = {}
        api_env_source_label = ""

        if shell_name:
            api_env_file_path = Path.home() / ".pdd" / f"api-env.{shell_name}"
            api_env_vals = _parse_api_env_file(api_env_file_path)
            api_env_source_label = f"~/.pdd/api-env.{shell_name}"

        for key_name in key_names:
            # Check in priority order
            if key_name in dotenv_vals:
                result[key_name] = KeyInfo(source=".env file", is_set=True)
            elif key_name in os.environ:
                result[key_name] = KeyInfo(source="shell environment", is_set=True)
            elif key_name in api_env_vals:
                result[key_name] = KeyInfo(
                    source=api_env_source_label, is_set=True
                )
            else:
                # Key not found in any source
                result[key_name] = KeyInfo(source="", is_set=False)

    except Exception as e:
        logger.error("Unexpected error during environment scan: %s", e)

    return result