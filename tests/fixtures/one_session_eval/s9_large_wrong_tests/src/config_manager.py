"""
config_manager.py - Hierarchical configuration management with lazy validation.

A comprehensive configuration management system supporting layered sources,
schema-driven type coercion, lazy validation, change tracking, atomic saves,
snapshot/restore, and namespace resolution.

Key design decision: Validation is LAZY. Values are validated only when
accessed via get(), when save() is called, or via explicit validate().
set() never validates and never raises.
"""

import json
import os
import copy
import time
import uuid
import tempfile
import re
from enum import IntEnum
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple, Type, Set


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------

class ConfigLayer(IntEnum):
    """Configuration layers in priority order (higher value = higher priority)."""
    DEFAULT = 0
    FILE = 1
    ENVIRONMENT = 2
    OVERRIDE = 3


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class SchemaEntry:
    """Schema definition for a configuration key."""
    key: str
    type: Type = str
    default: Any = None
    required: bool = False
    validator: Optional[Callable[[Any], bool]] = None
    description: str = ""

    def __post_init__(self):
        if self.key and not isinstance(self.key, str):
            raise TypeError("Schema key must be a string")


@dataclass
class ChangeRecord:
    """Record of a configuration change."""
    key: str
    old_value: Any
    new_value: Any
    layer: ConfigLayer
    timestamp: float

    def to_dict(self) -> dict:
        """Serialize change record to a dictionary."""
        return {
            "key": self.key,
            "old_value": self.old_value,
            "new_value": self.new_value,
            "layer": self.layer.name,
            "timestamp": self.timestamp,
        }

    @classmethod
    def from_dict(cls, data: dict) -> "ChangeRecord":
        """Deserialize a change record from a dictionary."""
        layer = ConfigLayer[data["layer"]] if isinstance(data["layer"], str) else ConfigLayer(data["layer"])
        return cls(
            key=data["key"],
            old_value=data["old_value"],
            new_value=data["new_value"],
            layer=layer,
            timestamp=data["timestamp"],
        )


@dataclass
class Snapshot:
    """A saved configuration state."""
    id: str
    timestamp: float
    state: Dict[str, Dict[str, Any]]
    schema_state: Dict[str, dict]
    change_records: List[dict]

    def to_dict(self) -> dict:
        """Serialize snapshot to dictionary."""
        return {
            "id": self.id,
            "timestamp": self.timestamp,
            "state": self.state,
            "schema_state": self.schema_state,
            "change_records": self.change_records,
        }


# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------

class ValidationError(Exception):
    """Raised when a configuration value fails validation."""

    def __init__(self, message: str = "", key: str = "", expected_type: Type = None,
                 actual_value: Any = None, errors: List["ValidationError"] = None):
        self.key = key
        self.expected_type = expected_type
        self.actual_value = actual_value
        self.errors = errors or []
        if not message:
            if key and expected_type is not None:
                message = (
                    f"Validation failed for key '{key}': "
                    f"expected {expected_type.__name__}, got {type(actual_value).__name__} "
                    f"(value: {actual_value!r})"
                )
            elif key:
                message = f"Validation failed for key '{key}'"
            else:
                message = "Configuration validation failed"
        super().__init__(message)


class ConfigurationError(Exception):
    """General configuration error."""
    pass


class SchemaError(Exception):
    """Error in schema definition."""
    pass


class ParseError(Exception):
    """Error parsing configuration file."""

    def __init__(self, message: str = "", line_number: int = 0, line_content: str = ""):
        self.line_number = line_number
        self.line_content = line_content
        if line_number and not message:
            message = f"Parse error at line {line_number}: {line_content}"
        super().__init__(message)


# ---------------------------------------------------------------------------
# TypeCoercer - handles string-to-type conversions
# ---------------------------------------------------------------------------

class TypeCoercer:
    """Converts string values to their target types.

    Used primarily when loading from environment variables or config files
    where all values arrive as strings.
    """

    # Boolean true/false string representations
    BOOL_TRUE = frozenset({"true", "yes", "1", "on", "enabled", "t", "y"})
    BOOL_FALSE = frozenset({"false", "no", "0", "off", "disabled", "f", "n"})

    def __init__(self):
        self._coercers: Dict[Type, Callable] = {
            int: self._coerce_int,
            float: self._coerce_float,
            bool: self._coerce_bool,
            str: self._coerce_str,
            list: self._coerce_list,
            dict: self._coerce_dict,
        }
        self._coercion_cache: Dict[Tuple[str, Type], Any] = {}
        self._cache_max_size = 1024

    def can_coerce(self, target_type: Type) -> bool:
        """Check if a type is supported for coercion."""
        return target_type in self._coercers

    def coerce(self, value: Any, target_type: Type) -> Any:
        """Coerce a value to the target type.

        If value is already the target type, return as-is.
        If value is a string, attempt conversion.
        Otherwise, attempt direct type conversion.
        """
        if value is None:
            return None

        if isinstance(value, target_type) and not (isinstance(value, (int, bool)) and target_type in (float, int, bool)):
            # Special handling for bool/int since bool is subclass of int
            if isinstance(value, bool) and target_type is int:
                pass  # Need conversion
            elif isinstance(value, int) and not isinstance(value, bool) and target_type is bool:
                pass  # Need conversion
            else:
                return value

        if isinstance(value, str):
            cache_key = (value, target_type)
            if cache_key in self._coercion_cache:
                return self._coercion_cache[cache_key]

            coercer = self._coercers.get(target_type)
            if coercer is None:
                raise TypeError(f"Cannot coerce string to {target_type.__name__}")

            result = coercer(value)

            if len(self._coercion_cache) < self._cache_max_size:
                self._coercion_cache[cache_key] = result

            return result

        # Non-string, non-matching type: try direct conversion
        return self._direct_convert(value, target_type)

    def _direct_convert(self, value: Any, target_type: Type) -> Any:
        """Attempt direct type conversion for non-string values."""
        if target_type is bool:
            if isinstance(value, (int, float)):
                return bool(value)
            return bool(value)
        if target_type is int:
            if isinstance(value, bool):
                return 1 if value else 0
            if isinstance(value, float):
                if value != int(value):
                    raise ValueError(f"Cannot convert {value} to int without losing precision")
                return int(value)
            return int(value)
        if target_type is float:
            if isinstance(value, bool):
                return 1.0 if value else 0.0
            return float(value)
        if target_type is str:
            return str(value)
        if target_type is list:
            if isinstance(value, (tuple, set, frozenset)):
                return list(value)
            raise TypeError(f"Cannot convert {type(value).__name__} to list")
        if target_type is dict:
            if hasattr(value, "__dict__"):
                return dict(value.__dict__)
            raise TypeError(f"Cannot convert {type(value).__name__} to dict")
        return target_type(value)

    def _coerce_int(self, value: str) -> int:
        """Coerce a string to int, handling various formats."""
        stripped = value.strip()
        if not stripped:
            raise ValueError("Cannot convert empty string to int")

        # Handle hex, octal, binary prefixes
        lower = stripped.lower()
        if lower.startswith("0x"):
            return int(stripped, 16)
        if lower.startswith("0o"):
            return int(stripped, 8)
        if lower.startswith("0b"):
            return int(stripped, 2)

        # Handle negative numbers
        if stripped.startswith("-") or stripped.startswith("+"):
            sign = -1 if stripped[0] == "-" else 1
            rest = stripped[1:].strip()
            if not rest:
                raise ValueError(f"Cannot convert '{value}' to int")
            return sign * int(rest)

        # Handle numbers with underscores (e.g., "1_000_000")
        cleaned = stripped.replace("_", "")

        # Handle float-like strings (e.g., "42.0")
        if "." in cleaned:
            float_val = float(cleaned)
            if float_val != int(float_val):
                raise ValueError(f"Cannot convert '{value}' to int without losing precision")
            return int(float_val)

        return int(cleaned)

    def _coerce_float(self, value: str) -> float:
        """Coerce a string to float."""
        stripped = value.strip()
        if not stripped:
            raise ValueError("Cannot convert empty string to float")

        # Handle special float values
        lower = stripped.lower()
        if lower in ("inf", "+inf", "infinity", "+infinity"):
            return float("inf")
        if lower in ("-inf", "-infinity"):
            return float("-inf")
        if lower == "nan":
            return float("nan")

        # Handle underscores
        cleaned = stripped.replace("_", "")
        return float(cleaned)

    def _coerce_bool(self, value: str) -> bool:
        """Coerce a string to bool."""
        stripped = value.strip().lower()
        if stripped in self.BOOL_TRUE:
            return True
        if stripped in self.BOOL_FALSE:
            return False
        raise ValueError(f"Cannot convert '{value}' to bool")

    def _coerce_str(self, value: str) -> str:
        """Coerce a string to str (identity)."""
        return value

    def _coerce_list(self, value: str) -> list:
        """Coerce a string to list.

        Supports JSON array format and comma-separated values.
        """
        stripped = value.strip()
        if not stripped:
            return []

        # Try JSON array first
        if stripped.startswith("["):
            try:
                result = json.loads(stripped)
                if isinstance(result, list):
                    return result
            except json.JSONDecodeError:
                pass

        # Fall back to comma-separated
        items = []
        for item in stripped.split(","):
            item = item.strip()
            if item:
                # Try to parse individual items
                item = self._auto_parse_value(item)
                items.append(item)
        return items

    def _coerce_dict(self, value: str) -> dict:
        """Coerce a string to dict.

        Supports JSON object format and key=value pairs.
        """
        stripped = value.strip()
        if not stripped:
            return {}

        # Try JSON object first
        if stripped.startswith("{"):
            try:
                result = json.loads(stripped)
                if isinstance(result, dict):
                    return result
            except json.JSONDecodeError:
                pass

        # Fall back to key=value pairs (semicolon or comma separated)
        result = {}
        separator = ";" if ";" in stripped else ","
        for pair in stripped.split(separator):
            pair = pair.strip()
            if "=" in pair:
                key, val = pair.split("=", 1)
                result[key.strip()] = self._auto_parse_value(val.strip())
        return result

    def _auto_parse_value(self, value: str) -> Any:
        """Attempt to automatically parse a string value to a native type."""
        if not value:
            return value

        # Try integer
        try:
            return int(value)
        except (ValueError, TypeError):
            pass

        # Try float
        try:
            return float(value)
        except (ValueError, TypeError):
            pass

        # Try boolean
        lower = value.lower()
        if lower in self.BOOL_TRUE:
            return True
        if lower in self.BOOL_FALSE:
            return False

        # Try null
        if lower in ("null", "none", "nil"):
            return None

        return value

    def clear_cache(self):
        """Clear the coercion cache."""
        self._coercion_cache.clear()


# ---------------------------------------------------------------------------
# NamespaceResolver - handles dot-separated key hierarchies
# ---------------------------------------------------------------------------

class NamespaceResolver:
    """Manages dot-separated namespace hierarchies for configuration keys.

    Provides efficient lookup of keys within namespaces, parent/child
    relationships, and namespace flattening/unflattening.
    """

    def __init__(self):
        self._separator = "."
        self._namespace_cache: Dict[str, List[str]] = {}
        self._children_cache: Dict[str, Set[str]] = {}

    @property
    def separator(self) -> str:
        """Get the namespace separator."""
        return self._separator

    def split_key(self, key: str) -> List[str]:
        """Split a key into its namespace parts."""
        if key in self._namespace_cache:
            return self._namespace_cache[key]
        parts = key.split(self._separator)
        self._namespace_cache[key] = parts
        return parts

    def join_parts(self, parts: List[str]) -> str:
        """Join namespace parts into a key."""
        return self._separator.join(parts)

    def get_namespace(self, key: str) -> str:
        """Get the namespace (parent) portion of a key.

        Example: "database.connection.host" -> "database.connection"
        """
        parts = self.split_key(key)
        if len(parts) <= 1:
            return ""
        return self.join_parts(parts[:-1])

    def get_leaf(self, key: str) -> str:
        """Get the leaf (final) portion of a key.

        Example: "database.connection.host" -> "host"
        """
        parts = self.split_key(key)
        return parts[-1] if parts else key

    def is_child_of(self, key: str, prefix: str) -> bool:
        """Check if a key is a direct or nested child of a prefix.

        Example: "database.host" is child of "database"
                 "database.connection.host" is child of "database"
        """
        if not prefix:
            return True
        return key.startswith(prefix + self._separator)

    def is_direct_child_of(self, key: str, prefix: str) -> bool:
        """Check if a key is a direct (not nested) child of a prefix.

        Example: "database.host" is direct child of "database"
                 "database.connection.host" is NOT direct child of "database"
        """
        if not self.is_child_of(key, prefix):
            return False
        remainder = key[len(prefix) + 1:]
        return self._separator not in remainder

    def get_children(self, prefix: str, keys: set) -> Dict[str, Any]:
        """Get all keys under a prefix with the prefix stripped.

        Returns a dict mapping stripped keys to None (values to be filled by caller).
        """
        result = {}
        prefix_dot = prefix + self._separator if prefix else ""
        prefix_len = len(prefix_dot)

        for key in keys:
            if prefix and not key.startswith(prefix_dot):
                continue
            if not prefix or key.startswith(prefix_dot):
                stripped = key[prefix_len:] if prefix else key
                result[stripped] = None
        return result

    def get_direct_children_names(self, prefix: str, keys: set) -> Set[str]:
        """Get names of direct child namespaces under a prefix.

        Example: Given keys ["db.host", "db.port", "db.pool.size", "db.pool.max"],
                 get_direct_children_names("db", keys) -> {"host", "port", "pool"}
        """
        result = set()
        prefix_dot = prefix + self._separator if prefix else ""
        prefix_len = len(prefix_dot)

        for key in keys:
            if prefix and not key.startswith(prefix_dot):
                continue
            remainder = key[prefix_len:]
            parts = remainder.split(self._separator)
            if parts:
                result.add(parts[0])
        return result

    def flatten(self, nested: dict, prefix: str = "") -> Dict[str, Any]:
        """Flatten a nested dictionary into dot-separated keys.

        Example: {"database": {"host": "localhost"}} -> {"database.host": "localhost"}
        """
        result = {}
        for key, value in nested.items():
            full_key = f"{prefix}{self._separator}{key}" if prefix else key
            if isinstance(value, dict) and value:
                result.update(self.flatten(value, full_key))
            else:
                result[full_key] = value
        return result

    def unflatten(self, flat: Dict[str, Any]) -> dict:
        """Unflatten dot-separated keys into a nested dictionary.

        Example: {"database.host": "localhost"} -> {"database": {"host": "localhost"}}
        """
        result = {}
        for key, value in sorted(flat.items()):
            parts = self.split_key(key)
            current = result
            for part in parts[:-1]:
                if part not in current:
                    current[part] = {}
                elif not isinstance(current[part], dict):
                    # Conflict: a leaf value is also a namespace
                    current[part] = {"__value__": current[part]}
                current = current[part]
            if parts:
                current[parts[-1]] = value
        return result

    def get_all_namespaces(self, keys: set) -> Set[str]:
        """Get all unique namespace prefixes from a set of keys."""
        namespaces = set()
        for key in keys:
            parts = self.split_key(key)
            for i in range(1, len(parts)):
                namespaces.add(self.join_parts(parts[:i]))
        return namespaces

    def matches_pattern(self, key: str, pattern: str) -> bool:
        """Check if a key matches a glob-like pattern.

        Supports '*' for single namespace level and '**' for any depth.
        Example: "database.*.host" matches "database.primary.host"
                 "database.**" matches "database.primary.connection.host"
        """
        key_parts = self.split_key(key)
        pattern_parts = pattern.split(self._separator)
        return self._match_parts(key_parts, 0, pattern_parts, 0)

    def _match_parts(self, key_parts: list, ki: int,
                     pattern_parts: list, pi: int) -> bool:
        """Recursive helper for pattern matching."""
        if pi == len(pattern_parts):
            return ki == len(key_parts)
        if ki == len(key_parts):
            # Only match if remaining pattern parts are all "**"
            return all(p == "**" for p in pattern_parts[pi:])

        current_pattern = pattern_parts[pi]

        if current_pattern == "**":
            # ** matches zero or more parts
            # Try matching ** against zero parts
            if self._match_parts(key_parts, ki, pattern_parts, pi + 1):
                return True
            # Try matching ** against one or more parts
            for skip in range(ki, len(key_parts)):
                if self._match_parts(key_parts, skip + 1, pattern_parts, pi + 1):
                    return True
            return False
        elif current_pattern == "*":
            # * matches exactly one part
            return self._match_parts(key_parts, ki + 1, pattern_parts, pi + 1)
        else:
            # Literal match
            if key_parts[ki] == current_pattern:
                return self._match_parts(key_parts, ki + 1, pattern_parts, pi + 1)
            return False

    def clear_cache(self):
        """Clear all caches."""
        self._namespace_cache.clear()
        self._children_cache.clear()


# ---------------------------------------------------------------------------
# ChangeTracker - records configuration changes
# ---------------------------------------------------------------------------

class ChangeTracker:
    """Tracks changes to configuration values with timestamps.

    Each modification is recorded as a ChangeRecord. The tracker can be
    reset to clear all recorded changes (typically after a save).
    """

    def __init__(self):
        self._changes: Dict[str, ChangeRecord] = {}
        self._history: List[ChangeRecord] = []
        self._tracking_enabled = True
        self._batch_mode = False
        self._batch_changes: List[ChangeRecord] = []

    @property
    def is_tracking(self) -> bool:
        """Check if change tracking is enabled."""
        return self._tracking_enabled

    def enable(self):
        """Enable change tracking."""
        self._tracking_enabled = True

    def disable(self):
        """Disable change tracking."""
        self._tracking_enabled = False

    def record(self, key: str, old_value: Any, new_value: Any,
               layer: ConfigLayer) -> Optional[ChangeRecord]:
        """Record a configuration change.

        Returns the ChangeRecord if tracking is enabled, None otherwise.
        """
        if not self._tracking_enabled:
            return None

        record = ChangeRecord(
            key=key,
            old_value=old_value,
            new_value=new_value,
            layer=layer,
            timestamp=time.time(),
        )

        if self._batch_mode:
            self._batch_changes.append(record)
        else:
            self._changes[key] = record
            self._history.append(record)

        return record

    def get_changes(self) -> Dict[str, ChangeRecord]:
        """Get all changes since last reset."""
        return dict(self._changes)

    def get_change(self, key: str) -> Optional[ChangeRecord]:
        """Get the change record for a specific key."""
        return self._changes.get(key)

    def has_changes(self) -> bool:
        """Check if there are any recorded changes."""
        return len(self._changes) > 0

    def get_changed_keys(self) -> Set[str]:
        """Get the set of all changed keys."""
        return set(self._changes.keys())

    def get_history(self) -> List[ChangeRecord]:
        """Get the full change history."""
        return list(self._history)

    def get_history_for_key(self, key: str) -> List[ChangeRecord]:
        """Get the change history for a specific key."""
        return [r for r in self._history if r.key == key]

    def reset(self):
        """Clear all recorded changes."""
        self._changes.clear()

    def clear_history(self):
        """Clear the full change history."""
        self._history.clear()

    def full_reset(self):
        """Clear both current changes and history."""
        self._changes.clear()
        self._history.clear()

    def begin_batch(self):
        """Start a batch operation — changes are buffered."""
        self._batch_mode = True
        self._batch_changes.clear()

    def commit_batch(self):
        """Commit all batched changes."""
        for record in self._batch_changes:
            self._changes[record.key] = record
            self._history.append(record)
        self._batch_changes.clear()
        self._batch_mode = False

    def rollback_batch(self):
        """Discard all batched changes."""
        self._batch_changes.clear()
        self._batch_mode = False

    def serialize(self) -> list:
        """Serialize current changes to a list of dicts."""
        return [record.to_dict() for record in self._changes.values()]

    def deserialize(self, data: list):
        """Restore changes from serialized data."""
        self._changes.clear()
        for item in data:
            record = ChangeRecord.from_dict(item)
            self._changes[record.key] = record


# ---------------------------------------------------------------------------
# SnapshotManager - manages configuration snapshots
# ---------------------------------------------------------------------------

class SnapshotManager:
    """Manages snapshots of configuration state.

    Snapshots capture the full state of all configuration layers,
    schemas, and change records, allowing rollback to any saved point.
    """

    def __init__(self, max_snapshots: int = 50):
        self._snapshots: Dict[str, Snapshot] = {}
        self._snapshot_order: List[str] = []
        self._max_snapshots = max_snapshots

    @property
    def count(self) -> int:
        """Number of stored snapshots."""
        return len(self._snapshots)

    def create(self, state: Dict[str, Dict[str, Any]],
               schema_state: Dict[str, dict],
               change_records: List[dict]) -> str:
        """Create a new snapshot and return its ID."""
        snapshot_id = str(uuid.uuid4())[:8]
        timestamp = time.time()

        snapshot = Snapshot(
            id=snapshot_id,
            timestamp=timestamp,
            state=copy.deepcopy(state),
            schema_state=copy.deepcopy(schema_state),
            change_records=copy.deepcopy(change_records),
        )

        self._snapshots[snapshot_id] = snapshot
        self._snapshot_order.append(snapshot_id)

        # Enforce max snapshots
        while len(self._snapshots) > self._max_snapshots:
            oldest_id = self._snapshot_order.pop(0)
            del self._snapshots[oldest_id]

        return snapshot_id

    def get(self, snapshot_id: str) -> Snapshot:
        """Retrieve a snapshot by ID. Raises KeyError if not found."""
        if snapshot_id not in self._snapshots:
            raise KeyError(f"Snapshot '{snapshot_id}' not found")
        return self._snapshots[snapshot_id]

    def delete(self, snapshot_id: str):
        """Delete a snapshot by ID."""
        if snapshot_id in self._snapshots:
            del self._snapshots[snapshot_id]
            self._snapshot_order.remove(snapshot_id)

    def list_snapshots(self) -> List[dict]:
        """List all snapshots with metadata."""
        result = []
        for sid in self._snapshot_order:
            snap = self._snapshots[sid]
            result.append({
                "id": snap.id,
                "timestamp": snap.timestamp,
                "keys": len(snap.state.get("OVERRIDE", {})),
            })
        return result

    def clear(self):
        """Remove all snapshots."""
        self._snapshots.clear()
        self._snapshot_order.clear()

    def get_latest(self) -> Optional[Snapshot]:
        """Get the most recent snapshot."""
        if not self._snapshot_order:
            return None
        return self._snapshots[self._snapshot_order[-1]]


# ---------------------------------------------------------------------------
# AtomicWriter - atomic file writing with temp file + rename
# ---------------------------------------------------------------------------

class AtomicWriter:
    """Writes files atomically using temp file + rename strategy.

    Ensures that readers never see a partially-written file.
    """

    def __init__(self):
        self._backup_enabled = True
        self._backup_suffix = ".bak"

    def write(self, path: str, content: str, encoding: str = "utf-8",
              backup: bool = False) -> bool:
        """Write content to a file atomically.

        Steps:
        1. Write to a temporary file in the same directory
        2. Flush and sync to disk
        3. Optionally create a backup of the original
        4. Atomically rename temp file to target path

        Returns True on success, raises on failure.
        """
        path = os.path.abspath(path)
        directory = os.path.dirname(path)

        # Ensure directory exists
        if directory and not os.path.exists(directory):
            os.makedirs(directory, exist_ok=True)

        # Write to temp file in the same directory (for same-filesystem rename)
        fd = None
        tmp_path = None
        try:
            fd, tmp_path = tempfile.mkstemp(
                dir=directory,
                prefix=".config_tmp_",
                suffix=".tmp"
            )
            # Write content
            with os.fdopen(fd, "w", encoding=encoding) as f:
                fd = None  # os.fdopen takes ownership of fd
                f.write(content)
                f.flush()
                os.fsync(f.fileno())

            # Create backup if requested and original exists
            if backup and self._backup_enabled and os.path.exists(path):
                backup_path = path + self._backup_suffix
                try:
                    if os.path.exists(backup_path):
                        os.remove(backup_path)
                    os.rename(path, backup_path)
                except OSError:
                    pass  # Best effort backup

            # Atomic rename
            os.replace(tmp_path, path)
            tmp_path = None  # Rename succeeded, don't delete in finally
            return True

        except Exception:
            raise
        finally:
            # Clean up fd if still open
            if fd is not None:
                try:
                    os.close(fd)
                except OSError:
                    pass
            # Clean up temp file if rename didn't happen
            if tmp_path is not None:
                try:
                    os.remove(tmp_path)
                except OSError:
                    pass

    def read(self, path: str, encoding: str = "utf-8") -> str:
        """Read a file's contents."""
        with open(path, "r", encoding=encoding) as f:
            return f.read()


# ---------------------------------------------------------------------------
# SimpleYamlParser - minimal YAML-like parser (no external deps)
# ---------------------------------------------------------------------------

class SimpleYamlParser:
    """A simplified YAML-like parser that handles basic key-value pairs
    and nested structures using indentation.

    Supports:
    - Key: value pairs
    - Nested maps via indentation (2 spaces per level)
    - Lists with - prefix
    - Comments with #
    - Quoted strings
    - Basic type inference (int, float, bool, null)

    Does NOT support:
    - Anchors and aliases
    - Multi-line strings (|, >)
    - Flow sequences/mappings
    - Tags
    - Complex keys
    """

    INDENT_SIZE = 2

    def __init__(self):
        self._type_coercer = TypeCoercer()

    def parse(self, text: str) -> dict:
        """Parse YAML-like text into a dictionary."""
        lines = text.split("\n")
        processed = self._preprocess_lines(lines)
        result, _ = self._parse_block(processed, 0, 0)
        return result

    def dump(self, data: dict, indent: int = 0) -> str:
        """Serialize a dictionary to YAML-like text."""
        lines = []
        self._dump_value(data, lines, indent)
        return "\n".join(lines)

    def _preprocess_lines(self, lines: list) -> list:
        """Remove comments, blank lines, and calculate indentation."""
        processed = []
        for i, line in enumerate(lines):
            # Remove inline comments (not inside quotes)
            stripped = self._remove_comment(line)
            if not stripped.strip():
                continue

            indent = len(stripped) - len(stripped.lstrip())
            content = stripped.strip()
            processed.append((i + 1, indent, content))
        return processed

    def _remove_comment(self, line: str) -> str:
        """Remove comments that aren't inside quoted strings."""
        in_single = False
        in_double = False
        result = []
        i = 0
        while i < len(line):
            ch = line[i]
            if ch == "'" and not in_double:
                in_single = not in_single
                result.append(ch)
            elif ch == '"' and not in_single:
                in_double = not in_double
                result.append(ch)
            elif ch == "#" and not in_single and not in_double:
                break
            else:
                result.append(ch)
            i += 1
        return "".join(result)

    def _parse_block(self, lines: list, start: int,
                     expected_indent: int) -> Tuple[dict, int]:
        """Parse a block of YAML at a given indentation level."""
        result = {}
        i = start

        while i < len(lines):
            line_num, indent, content = lines[i]

            if indent < expected_indent:
                break  # Dedented — end of this block

            if indent > expected_indent:
                # Unexpected indentation
                raise ParseError(
                    f"Unexpected indentation at line {line_num}",
                    line_number=line_num,
                    line_content=content,
                )

            # Check for list item
            if content.startswith("- "):
                # This is a list at the current level
                list_result, i = self._parse_list(lines, i, expected_indent)
                return list_result, i

            # Parse key: value
            if ":" in content:
                key, value = self._split_key_value(content)

                if value == "":
                    # Check if next lines are indented (nested block)
                    if i + 1 < len(lines) and lines[i + 1][1] > expected_indent:
                        nested, i = self._parse_block(
                            lines, i + 1,
                            lines[i + 1][1]
                        )
                        result[key] = nested
                    else:
                        result[key] = None
                        i += 1
                else:
                    result[key] = self._parse_scalar(value)
                    i += 1
            else:
                # Plain value or error
                raise ParseError(
                    f"Expected key:value pair at line {line_num}",
                    line_number=line_num,
                    line_content=content,
                )

        return result, i

    def _parse_list(self, lines: list, start: int,
                    expected_indent: int) -> Tuple[list, int]:
        """Parse a YAML-like list."""
        result = []
        i = start

        while i < len(lines):
            line_num, indent, content = lines[i]

            if indent < expected_indent:
                break

            if indent > expected_indent:
                raise ParseError(
                    f"Unexpected indentation in list at line {line_num}",
                    line_number=line_num,
                    line_content=content,
                )

            if content.startswith("- "):
                item_content = content[2:].strip()

                if ":" in item_content and not self._is_quoted(item_content):
                    # List item is a mapping
                    key, value = self._split_key_value(item_content)
                    item_dict = {}

                    if value == "":
                        if i + 1 < len(lines) and lines[i + 1][1] > expected_indent:
                            nested, i = self._parse_block(
                                lines, i + 1, lines[i + 1][1]
                            )
                            item_dict[key] = nested
                        else:
                            item_dict[key] = None
                            i += 1
                    else:
                        item_dict[key] = self._parse_scalar(value)
                        i += 1

                    # Check for continuation of this map item
                    while (i < len(lines) and
                           lines[i][1] > expected_indent and
                           not lines[i][2].startswith("- ")):
                        nested_line = lines[i]
                        if ":" in nested_line[2]:
                            nk, nv = self._split_key_value(nested_line[2])
                            item_dict[nk] = self._parse_scalar(nv) if nv else None
                        i += 1

                    result.append(item_dict)
                else:
                    result.append(self._parse_scalar(item_content))
                    i += 1
            else:
                break

        return result, i

    def _split_key_value(self, content: str) -> Tuple[str, str]:
        """Split a 'key: value' string, handling quoted keys."""
        # Handle quoted keys
        if content.startswith('"') or content.startswith("'"):
            quote = content[0]
            end = content.index(quote, 1)
            key = content[1:end]
            rest = content[end + 1:].strip()
            if rest.startswith(":"):
                value = rest[1:].strip()
            else:
                value = ""
            return key, value

        colon_idx = content.index(":")
        key = content[:colon_idx].strip()
        value = content[colon_idx + 1:].strip()
        return key, value

    def _is_quoted(self, text: str) -> bool:
        """Check if text starts with a quote."""
        stripped = text.strip()
        return (stripped.startswith('"') and stripped.endswith('"')) or \
               (stripped.startswith("'") and stripped.endswith("'"))

    def _parse_scalar(self, value: str) -> Any:
        """Parse a scalar YAML value."""
        if not value:
            return None

        # Handle quoted strings
        if (value.startswith('"') and value.endswith('"')) or \
           (value.startswith("'") and value.endswith("'")):
            return value[1:-1]

        # Handle null
        lower = value.lower()
        if lower in ("null", "~", "none"):
            return None

        # Handle booleans
        if lower in ("true", "yes", "on"):
            return True
        if lower in ("false", "no", "off"):
            return False

        # Handle numbers
        try:
            if "." in value or "e" in value.lower():
                return float(value)
            return int(value)
        except ValueError:
            pass

        return value

    def _dump_value(self, data: Any, lines: list, indent: int):
        """Recursively dump a value to YAML-like lines."""
        prefix = " " * indent

        if isinstance(data, dict):
            for key, value in data.items():
                if isinstance(value, dict):
                    lines.append(f"{prefix}{key}:")
                    self._dump_value(value, lines, indent + self.INDENT_SIZE)
                elif isinstance(value, list):
                    lines.append(f"{prefix}{key}:")
                    self._dump_list(value, lines, indent + self.INDENT_SIZE)
                else:
                    formatted = self._format_scalar(value)
                    lines.append(f"{prefix}{key}: {formatted}")
        elif isinstance(data, list):
            self._dump_list(data, lines, indent)
        else:
            formatted = self._format_scalar(data)
            lines.append(f"{prefix}{formatted}")

    def _dump_list(self, data: list, lines: list, indent: int):
        """Dump a list to YAML-like lines."""
        prefix = " " * indent
        for item in data:
            if isinstance(item, dict):
                first = True
                for key, value in item.items():
                    formatted = self._format_scalar(value) if not isinstance(value, (dict, list)) else ""
                    if first:
                        if formatted:
                            lines.append(f"{prefix}- {key}: {formatted}")
                        else:
                            lines.append(f"{prefix}- {key}:")
                            if isinstance(value, dict):
                                self._dump_value(value, lines, indent + self.INDENT_SIZE + 2)
                        first = False
                    else:
                        if formatted:
                            lines.append(f"{prefix}  {key}: {formatted}")
                        else:
                            lines.append(f"{prefix}  {key}:")
                            if isinstance(value, dict):
                                self._dump_value(value, lines, indent + self.INDENT_SIZE + 2)
            else:
                formatted = self._format_scalar(item)
                lines.append(f"{prefix}- {formatted}")

    def _format_scalar(self, value: Any) -> str:
        """Format a scalar value for YAML output."""
        if value is None:
            return "null"
        if isinstance(value, bool):
            return "true" if value else "false"
        if isinstance(value, str):
            # Quote strings that could be misinterpreted
            if (value.lower() in ("true", "false", "null", "yes", "no", "on", "off", "~") or
                    value == "" or ":" in value or "#" in value or
                    value.startswith(" ") or value.endswith(" ")):
                return f'"{value}"'
            try:
                float(value)
                return f'"{value}"'
            except ValueError:
                return value
        return str(value)


# ---------------------------------------------------------------------------
# SchemaRegistry - manages schema definitions
# ---------------------------------------------------------------------------

class SchemaRegistry:
    """Registry for configuration schema entries.

    Provides methods for registering, querying, and validating
    configuration keys against their schema definitions.
    """

    def __init__(self):
        self._entries: Dict[str, SchemaEntry] = {}
        self._namespace_resolver = NamespaceResolver()

    def define(self, key: str, type: Type = str, default: Any = None,
               required: bool = False, validator: Callable = None,
               description: str = "") -> SchemaEntry:
        """Register a schema entry for a key."""
        entry = SchemaEntry(
            key=key,
            type=type,
            default=default,
            required=required,
            validator=validator,
            description=description,
        )
        self._entries[key] = entry
        return entry

    def get(self, key: str) -> Optional[SchemaEntry]:
        """Get the schema entry for a key."""
        return self._entries.get(key)

    def has(self, key: str) -> bool:
        """Check if a key has a schema entry."""
        return key in self._entries

    def remove(self, key: str) -> bool:
        """Remove a schema entry."""
        if key in self._entries:
            del self._entries[key]
            return True
        return False

    def keys(self) -> Set[str]:
        """Get all registered keys."""
        return set(self._entries.keys())

    def required_keys(self) -> Set[str]:
        """Get all required keys."""
        return {k for k, v in self._entries.items() if v.required}

    def get_defaults(self) -> Dict[str, Any]:
        """Get all default values."""
        return {k: v.default for k, v in self._entries.items()
                if v.default is not None}

    def get_namespace_entries(self, prefix: str) -> Dict[str, SchemaEntry]:
        """Get all schema entries under a namespace prefix."""
        result = {}
        prefix_dot = prefix + "."
        for key, entry in self._entries.items():
            if key.startswith(prefix_dot):
                result[key] = entry
        return result

    def validate_value(self, key: str, value: Any,
                       coercer: TypeCoercer) -> Optional[ValidationError]:
        """Validate a single value against its schema.

        Returns a ValidationError if validation fails, None if it passes.
        This is the core validation logic used by lazy validation.
        """
        entry = self._entries.get(key)
        if entry is None:
            return None  # No schema, no validation

        # Check required
        if entry.required and value is None:
            return ValidationError(
                message=f"Required key '{key}' is missing or None",
                key=key,
            )

        if value is None:
            return None  # Not required, None is OK

        # Type coercion attempt
        actual_value = value
        if isinstance(value, str) and entry.type is not str:
            try:
                actual_value = coercer.coerce(value, entry.type)
            except (ValueError, TypeError) as e:
                return ValidationError(
                    message=f"Cannot coerce value for key '{key}': {e}",
                    key=key,
                    expected_type=entry.type,
                    actual_value=value,
                )

        # Type check (after coercion)
        if not isinstance(actual_value, entry.type):
            # Special case: int/bool overlap
            if entry.type is int and isinstance(actual_value, bool):
                return ValidationError(
                    message=f"Key '{key}': expected int, got bool",
                    key=key,
                    expected_type=entry.type,
                    actual_value=actual_value,
                )
            if not isinstance(actual_value, entry.type):
                return ValidationError(
                    key=key,
                    expected_type=entry.type,
                    actual_value=actual_value,
                )

        # Custom validator
        if entry.validator is not None:
            try:
                result = entry.validator(actual_value)
                if result is False:
                    return ValidationError(
                        message=f"Custom validator failed for key '{key}' with value {actual_value!r}",
                        key=key,
                        expected_type=entry.type,
                        actual_value=actual_value,
                    )
            except Exception as e:
                return ValidationError(
                    message=f"Validator error for key '{key}': {e}",
                    key=key,
                    expected_type=entry.type,
                    actual_value=actual_value,
                )

        return None

    def serialize(self) -> Dict[str, dict]:
        """Serialize all schema entries to a dict (minus validators)."""
        result = {}
        for key, entry in self._entries.items():
            result[key] = {
                "key": entry.key,
                "type": entry.type.__name__,
                "default": entry.default,
                "required": entry.required,
                "description": entry.description,
            }
        return result

    def get_info(self) -> List[dict]:
        """Get human-readable info about all schema entries."""
        info = []
        for key in sorted(self._entries.keys()):
            entry = self._entries[key]
            info.append({
                "key": key,
                "type": entry.type.__name__,
                "default": entry.default,
                "required": entry.required,
                "has_validator": entry.validator is not None,
                "description": entry.description,
            })
        return info


# ---------------------------------------------------------------------------
# LayerStore - manages the four configuration layers
# ---------------------------------------------------------------------------

class LayerStore:
    """Manages the four configuration layers and resolves values
    according to layer priority.

    Layer priority (highest to lowest):
    OVERRIDE > ENVIRONMENT > FILE > DEFAULT
    """

    def __init__(self):
        self._layers: Dict[ConfigLayer, Dict[str, Any]] = {
            ConfigLayer.DEFAULT: {},
            ConfigLayer.FILE: {},
            ConfigLayer.ENVIRONMENT: {},
            ConfigLayer.OVERRIDE: {},
        }

    def set(self, key: str, value: Any, layer: ConfigLayer):
        """Set a value in a specific layer."""
        self._layers[layer][key] = value

    def get(self, key: str, layer: ConfigLayer = None) -> Tuple[Any, Optional[ConfigLayer]]:
        """Get a value, optionally from a specific layer.

        If layer is None, resolves from highest to lowest priority.
        Returns (value, source_layer) tuple.
        """
        if layer is not None:
            value = self._layers[layer].get(key)
            return (value, layer) if value is not None or key in self._layers[layer] else (None, None)

        # Resolve through layers in priority order
        for check_layer in reversed(list(ConfigLayer)):
            if key in self._layers[check_layer]:
                return self._layers[check_layer][key], check_layer

        return None, None

    def delete(self, key: str, layer: ConfigLayer) -> bool:
        """Delete a key from a specific layer."""
        if key in self._layers[layer]:
            del self._layers[layer][key]
            return True
        return False

    def has(self, key: str, layer: ConfigLayer = None) -> bool:
        """Check if a key exists, optionally in a specific layer."""
        if layer is not None:
            return key in self._layers[layer]
        return any(key in self._layers[l] for l in ConfigLayer)

    def keys(self, layer: ConfigLayer = None) -> Set[str]:
        """Get all keys, optionally for a specific layer."""
        if layer is not None:
            return set(self._layers[layer].keys())
        all_keys = set()
        for l in ConfigLayer:
            all_keys.update(self._layers[l].keys())
        return all_keys

    def get_layer(self, layer: ConfigLayer) -> Dict[str, Any]:
        """Get a copy of all values in a layer."""
        return dict(self._layers[layer])

    def set_layer(self, layer: ConfigLayer, data: Dict[str, Any]):
        """Replace all values in a layer."""
        self._layers[layer] = dict(data)

    def clear_layer(self, layer: ConfigLayer):
        """Clear all values in a layer."""
        self._layers[layer].clear()

    def clear_all(self):
        """Clear all layers."""
        for layer in ConfigLayer:
            self._layers[layer].clear()

    def resolve_all(self) -> Dict[str, Any]:
        """Resolve all keys through the layer stack."""
        result = {}
        # Start from lowest priority and let higher override
        for layer in ConfigLayer:
            for key, value in self._layers[layer].items():
                result[key] = value
        return result

    def get_resolution_info(self, key: str) -> List[dict]:
        """Get information about which layers contain a key."""
        info = []
        for layer in reversed(list(ConfigLayer)):
            if key in self._layers[layer]:
                info.append({
                    "layer": layer.name,
                    "value": self._layers[layer][key],
                    "priority": layer.value,
                })
        return info

    def serialize(self) -> Dict[str, Dict[str, Any]]:
        """Serialize all layers to a dict."""
        return {
            layer.name: dict(values)
            for layer, values in self._layers.items()
        }

    def deserialize(self, data: Dict[str, Dict[str, Any]]):
        """Restore layers from serialized data."""
        for layer_name, values in data.items():
            layer = ConfigLayer[layer_name]
            self._layers[layer] = dict(values)

    def merge_into_layer(self, layer: ConfigLayer, data: Dict[str, Any],
                         overwrite: bool = True):
        """Merge a dict of values into a layer."""
        if overwrite:
            self._layers[layer].update(data)
        else:
            for key, value in data.items():
                if key not in self._layers[layer]:
                    self._layers[layer][key] = value

    def get_layer_for_key(self, key: str) -> Optional[ConfigLayer]:
        """Get the highest-priority layer that contains a key."""
        for layer in reversed(list(ConfigLayer)):
            if key in self._layers[layer]:
                return layer
        return None


# ---------------------------------------------------------------------------
# ConfigMerger - handles merging configurations from various sources
# ---------------------------------------------------------------------------

class ConfigMerger:
    """Handles merging of configuration data from various sources
    with support for deep merging of nested dictionaries.
    """

    def __init__(self, namespace_resolver: NamespaceResolver):
        self._ns = namespace_resolver

    def merge_flat(self, base: Dict[str, Any], updates: Dict[str, Any],
                   overwrite: bool = True) -> Dict[str, Any]:
        """Merge flat key-value dicts."""
        result = dict(base)
        for key, value in updates.items():
            if overwrite or key not in result:
                result[key] = value
        return result

    def merge_nested(self, base: dict, updates: dict,
                     overwrite: bool = True) -> dict:
        """Deep merge two nested dictionaries."""
        result = copy.deepcopy(base)
        self._deep_merge(result, updates, overwrite)
        return result

    def _deep_merge(self, base: dict, updates: dict, overwrite: bool):
        """Recursively merge updates into base."""
        for key, value in updates.items():
            if (key in base and isinstance(base[key], dict)
                    and isinstance(value, dict)):
                self._deep_merge(base[key], value, overwrite)
            elif overwrite or key not in base:
                base[key] = copy.deepcopy(value)

    def flatten_and_merge(self, base_flat: Dict[str, Any],
                          nested_updates: dict) -> Dict[str, Any]:
        """Flatten nested updates and merge into a flat dict."""
        flat_updates = self._ns.flatten(nested_updates)
        return self.merge_flat(base_flat, flat_updates)

    def diff(self, old: Dict[str, Any], new: Dict[str, Any]) -> dict:
        """Compute the difference between two flat configs."""
        added = {}
        removed = {}
        changed = {}

        all_keys = set(old.keys()) | set(new.keys())
        for key in all_keys:
            if key not in old:
                added[key] = new[key]
            elif key not in new:
                removed[key] = old[key]
            elif old[key] != new[key]:
                changed[key] = {"old": old[key], "new": new[key]}

        return {"added": added, "removed": removed, "changed": changed}


# ---------------------------------------------------------------------------
# EnvironmentLoader - loads configuration from environment variables
# ---------------------------------------------------------------------------

class EnvironmentLoader:
    """Loads configuration from environment variables.

    Convention: given prefix "MYAPP", environment variable "MYAPP_DATABASE_HOST"
    becomes key "database.host" (prefix stripped, lowercased, underscores to dots).
    """

    def __init__(self, namespace_resolver: NamespaceResolver):
        self._ns = namespace_resolver
        self._separator_replacement = "."

    def load(self, prefix: str, environ: dict = None) -> Dict[str, str]:
        """Load all environment variables with the given prefix.

        Args:
            prefix: The prefix to filter by (e.g., "MYAPP")
            environ: Optional dict to use instead of os.environ

        Returns:
            Dict of config keys to string values.
        """
        if environ is None:
            environ = os.environ

        prefix_upper = prefix.upper()
        if not prefix_upper.endswith("_"):
            prefix_upper += "_"

        result = {}
        prefix_len = len(prefix_upper)

        for env_key, env_value in environ.items():
            if env_key.upper().startswith(prefix_upper):
                # Strip prefix, lowercase, replace underscores with dots
                config_key = env_key[prefix_len:].lower()
                config_key = config_key.replace("_", self._separator_replacement)
                result[config_key] = env_value

        return result

    def build_env_key(self, prefix: str, config_key: str) -> str:
        """Convert a config key back to an environment variable name.

        Example: "database.host" with prefix "MYAPP" -> "MYAPP_DATABASE_HOST"
        """
        env_suffix = config_key.upper().replace(".", "_")
        prefix_upper = prefix.upper()
        if prefix_upper.endswith("_"):
            return f"{prefix_upper}{env_suffix}"
        return f"{prefix_upper}_{env_suffix}"

    def get_matching_vars(self, prefix: str, environ: dict = None) -> List[str]:
        """Get list of environment variable names matching the prefix."""
        if environ is None:
            environ = os.environ
        prefix_upper = prefix.upper()
        if not prefix_upper.endswith("_"):
            prefix_upper += "_"
        return [k for k in environ.keys() if k.upper().startswith(prefix_upper)]


# ---------------------------------------------------------------------------
# FileFormatHandler - handles reading/writing different config formats
# ---------------------------------------------------------------------------

class FileFormatHandler:
    """Handles reading and writing configuration in multiple formats.

    Supported formats: JSON, simplified YAML.
    """

    def __init__(self):
        self._yaml_parser = SimpleYamlParser()
        self._namespace_resolver = NamespaceResolver()

    def detect_format(self, path: str) -> str:
        """Detect file format from extension."""
        lower = path.lower()
        if lower.endswith((".yml", ".yaml")):
            return "yaml"
        if lower.endswith(".json"):
            return "json"
        # Try to detect from content
        return "json"  # Default

    def read_file(self, path: str) -> Dict[str, Any]:
        """Read a config file and return a flat dict."""
        fmt = self.detect_format(path)
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        if fmt == "yaml":
            return self.parse_yaml(content)
        return self.parse_json(content)

    def parse_json(self, content: str) -> Dict[str, Any]:
        """Parse JSON content into a flat config dict."""
        try:
            data = json.loads(content)
        except json.JSONDecodeError as e:
            raise ParseError(f"Invalid JSON: {e}")

        if isinstance(data, dict):
            return self._namespace_resolver.flatten(data)
        raise ParseError("JSON root must be an object")

    def parse_yaml(self, content: str) -> Dict[str, Any]:
        """Parse simplified YAML content into a flat config dict."""
        try:
            data = self._yaml_parser.parse(content)
        except ParseError:
            raise
        except Exception as e:
            raise ParseError(f"Invalid YAML: {e}")

        if isinstance(data, dict):
            return self._namespace_resolver.flatten(data)
        raise ParseError("YAML root must be a mapping")

    def serialize_json(self, flat_config: Dict[str, Any],
                       pretty: bool = True) -> str:
        """Serialize a flat config dict to JSON (nested)."""
        nested = self._namespace_resolver.unflatten(flat_config)
        if pretty:
            return json.dumps(nested, indent=2, sort_keys=True, default=str)
        return json.dumps(nested, sort_keys=True, default=str)

    def serialize_yaml(self, flat_config: Dict[str, Any]) -> str:
        """Serialize a flat config dict to simplified YAML."""
        nested = self._namespace_resolver.unflatten(flat_config)
        return self._yaml_parser.dump(nested)

    def write_file(self, path: str, flat_config: Dict[str, Any],
                   writer: AtomicWriter):
        """Write a flat config dict to a file."""
        fmt = self.detect_format(path)
        if fmt == "yaml":
            content = self.serialize_yaml(flat_config)
        else:
            content = self.serialize_json(flat_config)
        writer.write(path, content)


# ---------------------------------------------------------------------------
# ConfigValidator - orchestrates validation across all keys
# ---------------------------------------------------------------------------

class ConfigValidator:
    """Orchestrates validation of the entire configuration.

    Performs lazy validation: only called when explicitly requested
    (via get(), save(), or validate()).
    """

    def __init__(self, schema_registry: SchemaRegistry,
                 type_coercer: TypeCoercer):
        self._schema = schema_registry
        self._coercer = type_coercer
        self._validation_cache: Dict[str, Tuple[float, Optional[ValidationError]]] = {}
        self._cache_ttl = 1.0  # seconds

    def validate_single(self, key: str, value: Any) -> Optional[ValidationError]:
        """Validate a single key-value pair.

        This is called lazily — on get() or save(), never on set().
        """
        return self._schema.validate_value(key, value, self._coercer)

    def validate_all(self, resolved_values: Dict[str, Any]) -> List[ValidationError]:
        """Validate all resolved values against their schemas.

        Returns a list of all validation errors found.
        """
        errors = []

        # Check all schema-defined keys
        for key in self._schema.keys():
            value = resolved_values.get(key)
            error = self._schema.validate_value(key, value, self._coercer)
            if error is not None:
                errors.append(error)

        return errors

    def validate_required(self, resolved_values: Dict[str, Any]) -> List[ValidationError]:
        """Check that all required keys have non-None values."""
        errors = []
        for key in self._schema.required_keys():
            value = resolved_values.get(key)
            if value is None:
                errors.append(ValidationError(
                    message=f"Required key '{key}' is missing or None",
                    key=key,
                ))
        return errors

    def validate_namespace(self, prefix: str,
                           resolved_values: Dict[str, Any]) -> List[ValidationError]:
        """Validate all keys within a namespace."""
        errors = []
        ns_entries = self._schema.get_namespace_entries(prefix)
        for key, entry in ns_entries.items():
            value = resolved_values.get(key)
            error = self._schema.validate_value(key, value, self._coercer)
            if error is not None:
                errors.append(error)
        return errors

    def clear_cache(self):
        """Clear the validation cache."""
        self._validation_cache.clear()


# ---------------------------------------------------------------------------
# ConfigIterator - iteration support for configuration
# ---------------------------------------------------------------------------

class ConfigIterator:
    """Provides iteration capabilities over configuration entries."""

    def __init__(self, layer_store: LayerStore,
                 namespace_resolver: NamespaceResolver):
        self._store = layer_store
        self._ns = namespace_resolver

    def iter_keys(self, prefix: str = "") -> List[str]:
        """Iterate over all keys, optionally filtered by prefix."""
        all_keys = self._store.keys()
        if not prefix:
            return sorted(all_keys)
        prefix_dot = prefix + "."
        return sorted(k for k in all_keys if k.startswith(prefix_dot) or k == prefix)

    def iter_items(self, prefix: str = "") -> List[Tuple[str, Any]]:
        """Iterate over all key-value pairs."""
        items = []
        for key in self.iter_keys(prefix):
            value, _ = self._store.get(key)
            items.append((key, value))
        return items

    def iter_layers(self, key: str) -> List[Tuple[ConfigLayer, Any]]:
        """Iterate over all layers that contain a key."""
        result = []
        for layer in ConfigLayer:
            value, found_layer = self._store.get(key, layer)
            if found_layer is not None:
                result.append((layer, value))
        return result

    def count(self, prefix: str = "") -> int:
        """Count keys, optionally filtered by prefix."""
        return len(self.iter_keys(prefix))

    def namespaces(self) -> Set[str]:
        """Get all unique top-level namespaces."""
        result = set()
        for key in self._store.keys():
            parts = self._ns.split_key(key)
            if len(parts) > 1:
                result.add(parts[0])
        return result


# ---------------------------------------------------------------------------
# ConfigManager - main public API
# ---------------------------------------------------------------------------

class ConfigManager:
    """Hierarchical configuration manager with layered sources,
    lazy validation, type coercion, and snapshot/restore.

    IMPORTANT: Validation is LAZY.
    - set() NEVER validates. It stores whatever value is given.
    - Validation happens on get(), save(), or explicit validate() calls.
    - This is a deliberate design decision for flexibility.

    Layer priority (highest to lowest):
    OVERRIDE > ENVIRONMENT > FILE > DEFAULT
    """

    def __init__(self, schema_path: str = None):
        """Initialize the ConfigManager.

        Args:
            schema_path: Optional path to a JSON schema file to load.
        """
        # Internal components
        self._layer_store = LayerStore()
        self._schema_registry = SchemaRegistry()
        self._type_coercer = TypeCoercer()
        self._namespace_resolver = NamespaceResolver()
        self._change_tracker = ChangeTracker()
        self._snapshot_manager = SnapshotManager()
        self._atomic_writer = AtomicWriter()
        self._file_handler = FileFormatHandler()
        self._validator = ConfigValidator(self._schema_registry, self._type_coercer)
        self._merger = ConfigMerger(self._namespace_resolver)
        self._env_loader = EnvironmentLoader(self._namespace_resolver)
        self._iterator = ConfigIterator(self._layer_store, self._namespace_resolver)

        # State
        self._loaded_files: List[str] = []
        self._env_prefixes: List[str] = []
        self._last_save_time: Optional[float] = None
        self._metadata: Dict[str, Any] = {}

        # Load schema from file if provided
        if schema_path:
            self._load_schema_file(schema_path)

    # ------------------------------------------------------------------
    # Schema definition
    # ------------------------------------------------------------------

    def define_schema(self, key: str, type: Type = str,
                      default: Any = None, required: bool = False,
                      validator: Callable = None,
                      description: str = "") -> "ConfigManager":
        """Register a schema entry for a configuration key.

        The schema defines the expected type, default value, whether the
        key is required, and an optional custom validator function.

        Args:
            key: The configuration key (dot-separated for namespaces).
            type: Expected Python type (int, str, float, bool, list, dict).
            default: Default value if not set in any layer.
            required: If True, save() will fail if the key has no value.
            validator: Optional callable(value) -> bool.
            description: Human-readable description of the key.

        Returns:
            self (for method chaining)
        """
        self._schema_registry.define(
            key=key,
            type=type,
            default=default,
            required=required,
            validator=validator,
            description=description,
        )

        # Set default value in the DEFAULT layer
        if default is not None:
            self._layer_store.set(key, default, ConfigLayer.DEFAULT)

        return self

    # ------------------------------------------------------------------
    # Set / Get / Delete
    # ------------------------------------------------------------------

    def set(self, key: str, value: Any,
            layer: ConfigLayer = ConfigLayer.OVERRIDE) -> "ConfigManager":
        """Set a configuration value in the specified layer.

        IMPORTANT: This method does NOT validate the value. Validation
        is lazy and only happens on get(), save(), or validate().
        Setting an invalid value will succeed silently. The error
        will surface when the value is accessed or saved.

        Args:
            key: The configuration key.
            value: The value to set (any type accepted).
            layer: The layer to set the value in (default: OVERRIDE).

        Returns:
            self (for method chaining)
        """
        # Record the old value for change tracking
        old_value, _ = self._layer_store.get(key, layer)

        # Store the value — NO VALIDATION
        self._layer_store.set(key, value, layer)

        # Track the change
        self._change_tracker.record(key, old_value, value, layer)

        return self

    def get(self, key: str, default: Any = None) -> Any:
        """Get a configuration value, resolving through layers.

        Resolution order: OVERRIDE > ENVIRONMENT > FILE > DEFAULT.

        This method performs LAZY VALIDATION:
        - Resolves the value from the layer stack
        - If a schema exists, validates the value
        - If validation fails, raises ValidationError
        - If the value is a string and the schema expects a different type,
          attempts type coercion

        Args:
            key: The configuration key.
            default: Default value if key not found in any layer
                     and no schema default exists.

        Returns:
            The resolved, coerced, validated value.

        Raises:
            ValidationError: If the resolved value fails validation.
        """
        # Resolve from layers
        value, source_layer = self._layer_store.get(key)

        # If not found in any layer, use provided default
        if value is None and source_layer is None:
            schema = self._schema_registry.get(key)
            if schema is not None and schema.default is not None:
                value = schema.default
            else:
                value = default

        if value is None:
            # Check if required
            schema = self._schema_registry.get(key)
            if schema is not None and schema.required:
                raise ValidationError(
                    message=f"Required key '{key}' is missing or None",
                    key=key,
                )
            return default

        # Schema-based validation and coercion (LAZY — happens here, not in set())
        schema = self._schema_registry.get(key)
        if schema is not None:
            # Type coercion for string values
            if isinstance(value, str) and schema.type is not str:
                try:
                    value = self._type_coercer.coerce(value, schema.type)
                except (ValueError, TypeError) as e:
                    raise ValidationError(
                        message=f"Cannot coerce value for key '{key}': {e}",
                        key=key,
                        expected_type=schema.type,
                        actual_value=value,
                    )

            # Type validation
            if not isinstance(value, schema.type):
                # Special case: bool is subclass of int
                if schema.type is int and isinstance(value, bool):
                    raise ValidationError(
                        key=key,
                        expected_type=schema.type,
                        actual_value=value,
                    )
                if not isinstance(value, schema.type):
                    raise ValidationError(
                        key=key,
                        expected_type=schema.type,
                        actual_value=value,
                    )

            # Custom validator
            if schema.validator is not None:
                try:
                    result = schema.validator(value)
                    if result is False:
                        raise ValidationError(
                            message=f"Custom validator failed for key '{key}' "
                                    f"with value {value!r}",
                            key=key,
                            expected_type=schema.type,
                            actual_value=value,
                        )
                except ValidationError:
                    raise
                except Exception as e:
                    raise ValidationError(
                        message=f"Validator error for key '{key}': {e}",
                        key=key,
                        expected_type=schema.type,
                        actual_value=value,
                    )

        return value

    def delete(self, key: str,
               layer: ConfigLayer = ConfigLayer.OVERRIDE) -> bool:
        """Delete a key from a specific layer.

        Args:
            key: The configuration key to delete.
            layer: The layer to delete from (default: OVERRIDE).

        Returns:
            True if the key was found and deleted, False otherwise.
        """
        old_value, _ = self._layer_store.get(key, layer)
        deleted = self._layer_store.delete(key, layer)

        if deleted:
            self._change_tracker.record(key, old_value, None, layer)

        return deleted

    def has(self, key: str) -> bool:
        """Check if a key exists in any layer."""
        return self._layer_store.has(key)

    def get_source_layer(self, key: str) -> Optional[ConfigLayer]:
        """Get the layer that would provide a key's value."""
        _, layer = self._layer_store.get(key)
        return layer

    # ------------------------------------------------------------------
    # Bulk operations
    # ------------------------------------------------------------------

    def set_many(self, values: Dict[str, Any],
                 layer: ConfigLayer = ConfigLayer.OVERRIDE) -> "ConfigManager":
        """Set multiple values at once.

        IMPORTANT: Like set(), this does NOT validate values.
        """
        self._change_tracker.begin_batch()
        try:
            for key, value in values.items():
                old_value, _ = self._layer_store.get(key, layer)
                self._layer_store.set(key, value, layer)
                self._change_tracker.record(key, old_value, value, layer)
            self._change_tracker.commit_batch()
        except Exception:
            self._change_tracker.rollback_batch()
            raise
        return self

    def get_many(self, keys: List[str]) -> Dict[str, Any]:
        """Get multiple values at once.

        Validates each value (lazy validation). Collects all errors
        and raises a single ValidationError with all errors if any fail.
        """
        result = {}
        errors = []

        for key in keys:
            try:
                result[key] = self.get(key)
            except ValidationError as e:
                errors.append(e)

        if errors:
            raise ValidationError(
                message=f"Validation failed for {len(errors)} keys",
                errors=errors,
            )

        return result

    # ------------------------------------------------------------------
    # Persistence: save / load
    # ------------------------------------------------------------------

    def save(self, path: str, backup: bool = False) -> bool:
        """Save configuration to a file atomically.

        VALIDATES all values before saving. If any required keys are
        missing or any values fail validation, raises ValidationError.

        Args:
            path: File path to save to (.json or .yml/.yaml).
            backup: If True, create a backup of the existing file.

        Returns:
            True on success.

        Raises:
            ValidationError: If validation fails for any key.
        """
        # Resolve all current values
        resolved = self._resolve_all_coerced()

        # Validate ALL values before saving (lazy validation happens here)
        errors = self._validator.validate_all(resolved)
        if errors:
            if len(errors) == 1:
                raise errors[0]
            raise ValidationError(
                message=f"Validation failed for {len(errors)} keys: "
                        + ", ".join(e.key for e in errors),
                errors=errors,
            )

        # Write atomically
        self._file_handler.write_file(path, resolved, self._atomic_writer)

        # Update state
        self._last_save_time = time.time()
        self._change_tracker.reset()
        self._loaded_files.append(path)

        return True

    def load(self, path: str, layer: ConfigLayer = ConfigLayer.FILE) -> "ConfigManager":
        """Load configuration from a file.

        Does NOT validate loaded values (lazy validation).
        Values are stored in the specified layer.

        Args:
            path: File path to load from.
            layer: Layer to load values into (default: FILE).

        Returns:
            self (for method chaining)
        """
        flat_config = self._file_handler.read_file(path)

        self._change_tracker.begin_batch()
        try:
            for key, value in flat_config.items():
                old_value, _ = self._layer_store.get(key, layer)
                self._layer_store.set(key, value, layer)
                self._change_tracker.record(key, old_value, value, layer)
            self._change_tracker.commit_batch()
        except Exception:
            self._change_tracker.rollback_batch()
            raise

        self._loaded_files.append(path)
        return self

    def load_env(self, prefix: str, environ: dict = None) -> "ConfigManager":
        """Load configuration from environment variables.

        Convention: MYAPP_DATABASE_HOST -> database.host

        Does NOT validate loaded values (lazy validation).
        Values are stored in the ENVIRONMENT layer as strings
        (coercion happens on get()).

        Args:
            prefix: Environment variable prefix (e.g., "MYAPP").
            environ: Optional dict to use instead of os.environ.

        Returns:
            self (for method chaining)
        """
        env_values = self._env_loader.load(prefix, environ)

        self._change_tracker.begin_batch()
        try:
            for key, value in env_values.items():
                old_value, _ = self._layer_store.get(key, ConfigLayer.ENVIRONMENT)
                self._layer_store.set(key, value, ConfigLayer.ENVIRONMENT)
                self._change_tracker.record(
                    key, old_value, value, ConfigLayer.ENVIRONMENT
                )
            self._change_tracker.commit_batch()
        except Exception:
            self._change_tracker.rollback_batch()
            raise

        self._env_prefixes.append(prefix)
        return self

    # ------------------------------------------------------------------
    # Change tracking
    # ------------------------------------------------------------------

    def get_changes(self) -> Dict[str, ChangeRecord]:
        """Get all changes since the last save() or reset().

        Returns a dict mapping key names to ChangeRecord objects.
        """
        return self._change_tracker.get_changes()

    def has_unsaved_changes(self) -> bool:
        """Check if there are any unsaved changes."""
        return self._change_tracker.has_changes()

    def get_change_history(self) -> List[ChangeRecord]:
        """Get the full change history."""
        return self._change_tracker.get_history()

    # ------------------------------------------------------------------
    # Reset
    # ------------------------------------------------------------------

    def reset(self) -> "ConfigManager":
        """Clear all override values and reset change tracking.

        Returns:
            self (for method chaining)
        """
        self._layer_store.clear_layer(ConfigLayer.OVERRIDE)
        self._change_tracker.reset()
        self._change_tracker.clear_history()
        return self

    def reset_all(self) -> "ConfigManager":
        """Clear ALL layers and reset everything.

        Returns:
            self (for method chaining)
        """
        self._layer_store.clear_all()
        self._change_tracker.full_reset()
        self._loaded_files.clear()
        self._env_prefixes.clear()

        # Restore schema defaults
        for key in self._schema_registry.keys():
            entry = self._schema_registry.get(key)
            if entry and entry.default is not None:
                self._layer_store.set(key, entry.default, ConfigLayer.DEFAULT)

        return self

    # ------------------------------------------------------------------
    # Snapshot / Restore
    # ------------------------------------------------------------------

    def snapshot(self) -> str:
        """Create a snapshot of the current configuration state.

        Captures all layers, schema state, and change records.

        Returns:
            A snapshot ID string.
        """
        state = self._layer_store.serialize()
        schema_state = self._schema_registry.serialize()
        change_records = self._change_tracker.serialize()

        return self._snapshot_manager.create(state, schema_state, change_records)

    def restore(self, snapshot_id: str) -> "ConfigManager":
        """Restore configuration to a saved snapshot.

        Args:
            snapshot_id: The ID returned by snapshot().

        Returns:
            self (for method chaining)

        Raises:
            KeyError: If the snapshot ID is not found.
        """
        snap = self._snapshot_manager.get(snapshot_id)

        # Restore layer state
        self._layer_store.deserialize(snap.state)

        # Restore change records
        self._change_tracker.deserialize(snap.change_records)

        return self

    def list_snapshots(self) -> List[dict]:
        """List all available snapshots."""
        return self._snapshot_manager.list_snapshots()

    # ------------------------------------------------------------------
    # Validation (explicit)
    # ------------------------------------------------------------------

    def validate(self) -> List[ValidationError]:
        """Explicitly validate all configuration values.

        Returns a list of ValidationError objects. Empty list means valid.
        This is the explicit validation entry point; validation also
        happens lazily on get() and save().
        """
        resolved = self._resolve_all_coerced()
        return self._validator.validate_all(resolved)

    def validate_namespace(self, prefix: str) -> List[ValidationError]:
        """Validate all keys within a namespace."""
        resolved = self._resolve_all_coerced()
        return self._validator.validate_namespace(prefix, resolved)

    def is_valid(self) -> bool:
        """Check if the entire configuration is valid."""
        return len(self.validate()) == 0

    # ------------------------------------------------------------------
    # Import / Export
    # ------------------------------------------------------------------

    def export_json(self, pretty: bool = True) -> str:
        """Export the current resolved configuration as JSON.

        Args:
            pretty: If True, format with indentation.

        Returns:
            JSON string of the current configuration.
        """
        resolved = self._layer_store.resolve_all()
        nested = self._namespace_resolver.unflatten(resolved)
        if pretty:
            return json.dumps(nested, indent=2, sort_keys=True, default=str)
        return json.dumps(nested, sort_keys=True, default=str)

    def import_json(self, data: str) -> "ConfigManager":
        """Import configuration from a JSON string.

        Values are loaded into the OVERRIDE layer.
        Does NOT validate (lazy validation).

        Args:
            data: JSON string to import.

        Returns:
            self (for method chaining)
        """
        try:
            parsed = json.loads(data)
        except json.JSONDecodeError as e:
            raise ParseError(f"Invalid JSON: {e}")

        if not isinstance(parsed, dict):
            raise ParseError("JSON root must be an object")

        flat = self._namespace_resolver.flatten(parsed)

        self._change_tracker.begin_batch()
        try:
            for key, value in flat.items():
                old_value, _ = self._layer_store.get(key, ConfigLayer.OVERRIDE)
                self._layer_store.set(key, value, ConfigLayer.OVERRIDE)
                self._change_tracker.record(
                    key, old_value, value, ConfigLayer.OVERRIDE
                )
            self._change_tracker.commit_batch()
        except Exception:
            self._change_tracker.rollback_batch()
            raise

        return self

    def export_yaml(self) -> str:
        """Export the current resolved configuration as simplified YAML.

        Returns:
            YAML-like string of the current configuration.
        """
        resolved = self._layer_store.resolve_all()
        nested = self._namespace_resolver.unflatten(resolved)
        parser = SimpleYamlParser()
        return parser.dump(nested)

    def import_yaml(self, data: str) -> "ConfigManager":
        """Import configuration from a simplified YAML string.

        Values are loaded into the OVERRIDE layer.
        Does NOT validate (lazy validation).

        Args:
            data: YAML-like string to import.

        Returns:
            self (for method chaining)
        """
        parser = SimpleYamlParser()
        try:
            parsed = parser.parse(data)
        except ParseError:
            raise
        except Exception as e:
            raise ParseError(f"Invalid YAML: {e}")

        flat = self._namespace_resolver.flatten(parsed)

        self._change_tracker.begin_batch()
        try:
            for key, value in flat.items():
                old_value, _ = self._layer_store.get(key, ConfigLayer.OVERRIDE)
                self._layer_store.set(key, value, ConfigLayer.OVERRIDE)
                self._change_tracker.record(
                    key, old_value, value, ConfigLayer.OVERRIDE
                )
            self._change_tracker.commit_batch()
        except Exception:
            self._change_tracker.rollback_batch()
            raise

        return self

    # ------------------------------------------------------------------
    # Namespace operations
    # ------------------------------------------------------------------

    def get_namespace(self, prefix: str) -> Dict[str, Any]:
        """Get all configuration values under a namespace prefix.

        Keys are returned with the prefix stripped.

        Args:
            prefix: The namespace prefix (e.g., "database").

        Returns:
            Dict of stripped keys to resolved values.
        """
        all_keys = self._layer_store.keys()
        result = {}
        prefix_dot = prefix + "."
        prefix_len = len(prefix_dot)

        for key in sorted(all_keys):
            if key.startswith(prefix_dot):
                stripped_key = key[prefix_len:]
                try:
                    value = self.get(key)
                    result[stripped_key] = value
                except ValidationError:
                    # Include the key but with None on validation failure
                    result[stripped_key] = None

        return result

    def get_namespaces(self) -> Set[str]:
        """Get all top-level namespace prefixes."""
        return self._iterator.namespaces()

    # ------------------------------------------------------------------
    # Iteration and introspection
    # ------------------------------------------------------------------

    def keys(self) -> List[str]:
        """Get all configuration keys."""
        return self._iterator.iter_keys()

    def items(self) -> List[Tuple[str, Any]]:
        """Get all key-value pairs (resolved through layers)."""
        result = []
        for key in self._iterator.iter_keys():
            value, _ = self._layer_store.get(key)
            result.append((key, value))
        return result

    def __len__(self) -> int:
        """Get the number of configuration keys."""
        return self._iterator.count()

    def __contains__(self, key: str) -> bool:
        """Check if a key exists."""
        return self.has(key)

    def __getitem__(self, key: str) -> Any:
        """Get a value using dict-like access."""
        return self.get(key)

    def __setitem__(self, key: str, value: Any):
        """Set a value using dict-like access."""
        self.set(key, value)

    def __repr__(self) -> str:
        """String representation."""
        return (
            f"ConfigManager(keys={len(self)}, "
            f"layers={[l.name for l in ConfigLayer]}, "
            f"snapshots={self._snapshot_manager.count})"
        )

    # ------------------------------------------------------------------
    # Schema introspection
    # ------------------------------------------------------------------

    def get_schema_info(self) -> List[dict]:
        """Get human-readable information about all schema entries."""
        return self._schema_registry.get_info()

    def has_schema(self, key: str) -> bool:
        """Check if a key has a schema definition."""
        return self._schema_registry.has(key)

    # ------------------------------------------------------------------
    # Metadata
    # ------------------------------------------------------------------

    def set_metadata(self, key: str, value: Any):
        """Set a metadata value (not part of configuration)."""
        self._metadata[key] = value

    def get_metadata(self, key: str, default: Any = None) -> Any:
        """Get a metadata value."""
        return self._metadata.get(key, default)

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _resolve_all_coerced(self) -> Dict[str, Any]:
        """Resolve all values with type coercion applied."""
        resolved = self._layer_store.resolve_all()
        coerced = {}

        for key, value in resolved.items():
            schema = self._schema_registry.get(key)
            if schema is not None and isinstance(value, str) and schema.type is not str:
                try:
                    coerced[key] = self._type_coercer.coerce(value, schema.type)
                except (ValueError, TypeError):
                    coerced[key] = value  # Keep original for validation error
            else:
                coerced[key] = value

        # Include schema keys with defaults that aren't in any layer
        for key in self._schema_registry.keys():
            if key not in coerced:
                entry = self._schema_registry.get(key)
                if entry and entry.default is not None:
                    coerced[key] = entry.default

        return coerced

    def _load_schema_file(self, path: str):
        """Load schema definitions from a JSON file."""
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            raise SchemaError(f"Failed to load schema file: {e}")

        if not isinstance(data, dict):
            raise SchemaError("Schema file root must be a JSON object")

        type_map = {
            "str": str, "string": str,
            "int": int, "integer": int,
            "float": float, "number": float,
            "bool": bool, "boolean": bool,
            "list": list, "array": list,
            "dict": dict, "object": dict,
        }

        for key, spec in data.items():
            if not isinstance(spec, dict):
                continue
            type_name = spec.get("type", "str")
            self.define_schema(
                key=key,
                type=type_map.get(type_name, str),
                default=spec.get("default"),
                required=spec.get("required", False),
                description=spec.get("description", ""),
            )


# ---------------------------------------------------------------------------
# Convenience functions
# ---------------------------------------------------------------------------

def create_config(**kwargs) -> ConfigManager:
    """Create a ConfigManager with common defaults.

    Keyword arguments are passed as schema definitions.
    Each kwarg should be a dict with keys: type, default, required, etc.
    """
    mgr = ConfigManager()
    for key, spec in kwargs.items():
        if isinstance(spec, dict):
            mgr.define_schema(
                key=key,
                type=spec.get("type", str),
                default=spec.get("default"),
                required=spec.get("required", False),
                description=spec.get("description", ""),
            )
        else:
            mgr.define_schema(key=key, default=spec)
    return mgr


def load_config(path: str, schema_path: str = None) -> ConfigManager:
    """Load a configuration file, optionally with a schema.

    Args:
        path: Path to the configuration file.
        schema_path: Optional path to a schema file.

    Returns:
        A ConfigManager loaded with the file's values.
    """
    mgr = ConfigManager(schema_path=schema_path)
    mgr.load(path)
    return mgr


def merge_configs(*managers: ConfigManager) -> ConfigManager:
    """Merge multiple ConfigManagers into a new one.

    Later managers take priority over earlier ones.
    """
    result = ConfigManager()

    for mgr in managers:
        for key, value in mgr.items():
            result.set(key, value)

    return result


# ---------------------------------------------------------------------------
# ConfigBuilder - fluent API for building configurations
# ---------------------------------------------------------------------------

class ConfigBuilder:
    """Fluent builder for creating ConfigManager instances.

    Example:
        config = (ConfigBuilder()
            .with_schema("host", str, default="localhost", required=True)
            .with_schema("port", int, default=8080)
            .from_env("MYAPP")
            .from_file("config.json")
            .build())
    """

    def __init__(self):
        self._schemas: List[dict] = []
        self._files: List[Tuple[str, ConfigLayer]] = []
        self._env_prefixes: List[str] = []
        self._overrides: Dict[str, Any] = {}
        self._schema_path: Optional[str] = None

    def with_schema(self, key: str, type: Type = str,
                    default: Any = None, required: bool = False,
                    validator: Callable = None,
                    description: str = "") -> "ConfigBuilder":
        """Add a schema definition."""
        self._schemas.append({
            "key": key,
            "type": type,
            "default": default,
            "required": required,
            "validator": validator,
            "description": description,
        })
        return self

    def from_file(self, path: str,
                  layer: ConfigLayer = ConfigLayer.FILE) -> "ConfigBuilder":
        """Add a file to load."""
        self._files.append((path, layer))
        return self

    def from_env(self, prefix: str) -> "ConfigBuilder":
        """Add an environment prefix to load."""
        self._env_prefixes.append(prefix)
        return self

    def with_override(self, key: str, value: Any) -> "ConfigBuilder":
        """Add an override value."""
        self._overrides[key] = value
        return self

    def with_overrides(self, overrides: Dict[str, Any]) -> "ConfigBuilder":
        """Add multiple override values."""
        self._overrides.update(overrides)
        return self

    def with_schema_file(self, path: str) -> "ConfigBuilder":
        """Set a schema file to load."""
        self._schema_path = path
        return self

    def build(self) -> ConfigManager:
        """Build and return the ConfigManager."""
        mgr = ConfigManager(schema_path=self._schema_path)

        # Define schemas
        for schema in self._schemas:
            mgr.define_schema(**schema)

        # Load files
        for path, layer in self._files:
            mgr.load(path, layer)

        # Load env
        for prefix in self._env_prefixes:
            mgr.load_env(prefix)

        # Apply overrides
        if self._overrides:
            mgr.set_many(self._overrides)

        return mgr


# ---------------------------------------------------------------------------
# ConfigWatcher - monitors configuration for changes (polling-based)
# ---------------------------------------------------------------------------

class ConfigWatcher:
    """Monitors a configuration file for changes by polling.

    Provides a simple mechanism to detect when a config file has been
    modified externally and reload it.
    """

    def __init__(self, manager: ConfigManager, path: str,
                 poll_interval: float = 5.0):
        self._manager = manager
        self._path = os.path.abspath(path)
        self._poll_interval = poll_interval
        self._last_mtime: Optional[float] = None
        self._last_check: float = 0
        self._callbacks: List[Callable] = []
        self._enabled = False

    def start(self):
        """Start watching."""
        self._enabled = True
        self._last_mtime = self._get_mtime()
        self._last_check = time.time()

    def stop(self):
        """Stop watching."""
        self._enabled = False

    def on_change(self, callback: Callable):
        """Register a callback for when the file changes."""
        self._callbacks.append(callback)

    def check(self) -> bool:
        """Check if the file has changed since last check.

        Returns True if the file was reloaded.
        """
        if not self._enabled:
            return False

        now = time.time()
        if now - self._last_check < self._poll_interval:
            return False

        self._last_check = now
        current_mtime = self._get_mtime()

        if current_mtime is None:
            return False

        if self._last_mtime is not None and current_mtime > self._last_mtime:
            self._last_mtime = current_mtime
            self._manager.load(self._path)
            for callback in self._callbacks:
                try:
                    callback(self._manager)
                except Exception:
                    pass
            return True

        self._last_mtime = current_mtime
        return False

    def _get_mtime(self) -> Optional[float]:
        """Get file modification time."""
        try:
            return os.path.getmtime(self._path)
        except OSError:
            return None


# ---------------------------------------------------------------------------
# ConfigDumper - debug/diagnostic output
# ---------------------------------------------------------------------------

class ConfigDumper:
    """Provides diagnostic output for configuration debugging.

    Generates human-readable reports about the current configuration
    state, including layer resolution, schema info, and change history.
    """

    def __init__(self, manager: ConfigManager):
        self._manager = manager

    def dump_resolved(self) -> str:
        """Dump all resolved configuration values."""
        lines = ["=== Resolved Configuration ==="]
        for key, value in self._manager.items():
            source = self._manager.get_source_layer(key)
            source_name = source.name if source else "UNKNOWN"
            lines.append(f"  {key} = {value!r}  (from {source_name})")
        return "\n".join(lines)

    def dump_layers(self) -> str:
        """Dump all configuration layers."""
        lines = ["=== Configuration Layers ==="]
        for layer in ConfigLayer:
            layer_data = self._manager._layer_store.get_layer(layer)
            lines.append(f"\n  [{layer.name}] ({len(layer_data)} keys)")
            for key, value in sorted(layer_data.items()):
                lines.append(f"    {key} = {value!r}")
        return "\n".join(lines)

    def dump_schema(self) -> str:
        """Dump schema information."""
        lines = ["=== Schema Definitions ==="]
        for info in self._manager.get_schema_info():
            req = "*" if info["required"] else " "
            val = "V" if info["has_validator"] else " "
            lines.append(
                f"  {req}{val} {info['key']}: {info['type']}"
                f" (default={info['default']!r})"
            )
            if info["description"]:
                lines.append(f"       {info['description']}")
        return "\n".join(lines)

    def dump_changes(self) -> str:
        """Dump current changes."""
        lines = ["=== Unsaved Changes ==="]
        changes = self._manager.get_changes()
        if not changes:
            lines.append("  (no changes)")
        else:
            for key, record in sorted(changes.items()):
                lines.append(
                    f"  {key}: {record.old_value!r} -> {record.new_value!r}"
                    f" (layer={record.layer.name})"
                )
        return "\n".join(lines)

    def dump_all(self) -> str:
        """Dump complete diagnostic report."""
        sections = [
            self.dump_resolved(),
            self.dump_layers(),
            self.dump_schema(),
            self.dump_changes(),
        ]
        return "\n\n".join(sections)


# ---------------------------------------------------------------------------
# ConfigProfile - named configuration profiles
# ---------------------------------------------------------------------------

class ConfigProfile:
    """Manages named configuration profiles (e.g., dev, staging, prod).

    Each profile is a set of overrides that can be activated or deactivated.
    """

    def __init__(self, manager: ConfigManager):
        self._manager = manager
        self._profiles: Dict[str, Dict[str, Any]] = {}
        self._active_profile: Optional[str] = None

    def define(self, name: str, values: Dict[str, Any]) -> "ConfigProfile":
        """Define a named profile with its values."""
        self._profiles[name] = dict(values)
        return self

    def activate(self, name: str) -> "ConfigProfile":
        """Activate a profile by applying its values as overrides."""
        if name not in self._profiles:
            raise KeyError(f"Profile '{name}' not found")

        # Deactivate current profile first
        if self._active_profile:
            self.deactivate()

        for key, value in self._profiles[name].items():
            self._manager.set(key, value, ConfigLayer.OVERRIDE)

        self._active_profile = name
        return self

    def deactivate(self) -> "ConfigProfile":
        """Deactivate the current profile."""
        if self._active_profile and self._active_profile in self._profiles:
            for key in self._profiles[self._active_profile]:
                self._manager.delete(key, ConfigLayer.OVERRIDE)
        self._active_profile = None
        return self

    @property
    def active(self) -> Optional[str]:
        """Get the name of the active profile."""
        return self._active_profile

    def list_profiles(self) -> List[str]:
        """List all defined profile names."""
        return list(self._profiles.keys())

    def get_profile(self, name: str) -> Dict[str, Any]:
        """Get the values for a profile."""
        if name not in self._profiles:
            raise KeyError(f"Profile '{name}' not found")
        return dict(self._profiles[name])


# ---------------------------------------------------------------------------
# ConfigEncryption - simple obfuscation for sensitive values
# ---------------------------------------------------------------------------

class ConfigEncryption:
    """Simple reversible obfuscation for sensitive configuration values.

    NOTE: This is NOT cryptographic security — it's basic obfuscation
    to avoid plaintext secrets in config files. For real security,
    use a proper secrets manager.
    """

    MARKER = "ENC:"

    def __init__(self, key: int = 42):
        self._key = key

    def encrypt(self, value: str) -> str:
        """Obfuscate a string value."""
        # Simple XOR-based obfuscation
        chars = []
        for i, ch in enumerate(value):
            xored = ord(ch) ^ ((self._key + i) % 256)
            chars.append(f"{xored:02x}")
        return self.MARKER + "".join(chars)

    def decrypt(self, value: str) -> str:
        """De-obfuscate a string value."""
        if not value.startswith(self.MARKER):
            return value
        hex_str = value[len(self.MARKER):]
        chars = []
        for i in range(0, len(hex_str), 2):
            byte_val = int(hex_str[i:i + 2], 16)
            original = byte_val ^ ((self._key + i // 2) % 256)
            chars.append(chr(original))
        return "".join(chars)

    def is_encrypted(self, value: Any) -> bool:
        """Check if a value is encrypted."""
        return isinstance(value, str) and value.startswith(self.MARKER)

    def encrypt_keys(self, manager: ConfigManager, keys: List[str]):
        """Encrypt specific keys in the configuration."""
        for key in keys:
            try:
                value = manager.get(key)
                if isinstance(value, str) and not self.is_encrypted(value):
                    manager.set(key, self.encrypt(value))
            except (ValidationError, KeyError):
                pass

    def decrypt_keys(self, manager: ConfigManager, keys: List[str]):
        """Decrypt specific keys in the configuration."""
        for key in keys:
            try:
                value = manager.get(key)
                if isinstance(value, str) and self.is_encrypted(value):
                    manager.set(key, self.decrypt(value))
            except (ValidationError, KeyError):
                pass


# ---------------------------------------------------------------------------
# ConfigInterpolator - variable interpolation in config values
# ---------------------------------------------------------------------------

class ConfigInterpolator:
    """Supports variable interpolation in configuration values.

    Syntax: ${key} references another config key's value.
    Supports nested references and default values: ${key:-default}
    """

    PATTERN = re.compile(r"\$\{([^}]+)\}")
    MAX_DEPTH = 10

    def __init__(self, manager: ConfigManager):
        self._manager = manager

    def resolve(self, value: Any, depth: int = 0) -> Any:
        """Resolve interpolation references in a value."""
        if not isinstance(value, str):
            return value

        if depth > self.MAX_DEPTH:
            raise ConfigurationError("Maximum interpolation depth exceeded")

        def replacer(match):
            ref = match.group(1)
            # Handle default value syntax: ${key:-default}
            if ":-" in ref:
                ref_key, default_val = ref.split(":-", 1)
            else:
                ref_key = ref
                default_val = ""

            try:
                resolved = self._manager.get(ref_key.strip())
                if resolved is None:
                    return default_val
                resolved_str = str(resolved)
                # Recursively resolve
                return str(self.resolve(resolved_str, depth + 1))
            except (ValidationError, KeyError):
                return default_val

        return self.PATTERN.sub(replacer, value)

    def resolve_all(self) -> Dict[str, Any]:
        """Resolve interpolation in all config values."""
        result = {}
        for key in self._manager.keys():
            try:
                value = self._manager.get(key)
                result[key] = self.resolve(value)
            except (ValidationError, KeyError):
                result[key] = None
        return result

    def has_references(self, value: Any) -> bool:
        """Check if a value contains interpolation references."""
        if not isinstance(value, str):
            return False
        return bool(self.PATTERN.search(value))


# ---------------------------------------------------------------------------
# ConfigMigration - schema migration support
# ---------------------------------------------------------------------------

class ConfigMigration:
    """Supports migrating configuration between schema versions.

    Defines migration steps that transform configuration from one
    version to the next.
    """

    def __init__(self):
        self._migrations: List[dict] = []

    def add_migration(self, from_version: int, to_version: int,
                      transform: Callable[[Dict[str, Any]], Dict[str, Any]],
                      description: str = ""):
        """Add a migration step."""
        self._migrations.append({
            "from": from_version,
            "to": to_version,
            "transform": transform,
            "description": description,
        })
        # Sort by from_version
        self._migrations.sort(key=lambda m: m["from"])

    def migrate(self, config: Dict[str, Any],
                from_version: int, to_version: int) -> Dict[str, Any]:
        """Migrate configuration from one version to another."""
        current = dict(config)
        current_version = from_version

        while current_version < to_version:
            migration = None
            for m in self._migrations:
                if m["from"] == current_version:
                    migration = m
                    break

            if migration is None:
                raise ConfigurationError(
                    f"No migration path from version {current_version}"
                )

            current = migration["transform"](current)
            current_version = migration["to"]

        return current

    def get_migration_path(self, from_version: int,
                           to_version: int) -> List[dict]:
        """Get the list of migrations needed."""
        path = []
        current = from_version
        while current < to_version:
            found = False
            for m in self._migrations:
                if m["from"] == current:
                    path.append(m)
                    current = m["to"]
                    found = True
                    break
            if not found:
                break
        return path


# ---------------------------------------------------------------------------
# ConfigAccessLog - audit log for configuration access
# ---------------------------------------------------------------------------

class ConfigAccessLog:
    """Logs all configuration access for auditing purposes."""

    def __init__(self, max_entries: int = 10000):
        self._entries: List[dict] = []
        self._max_entries = max_entries

    def log_access(self, key: str, operation: str, value: Any = None,
                   success: bool = True, error: str = ""):
        """Log a configuration access event."""
        entry = {
            "timestamp": time.time(),
            "key": key,
            "operation": operation,
            "value_type": type(value).__name__ if value is not None else "None",
            "success": success,
            "error": error,
        }
        self._entries.append(entry)

        # Trim if over max
        if len(self._entries) > self._max_entries:
            self._entries = self._entries[-self._max_entries:]

    def get_entries(self, key: str = None,
                    operation: str = None) -> List[dict]:
        """Get log entries, optionally filtered."""
        entries = self._entries
        if key:
            entries = [e for e in entries if e["key"] == key]
        if operation:
            entries = [e for e in entries if e["operation"] == operation]
        return entries

    def get_stats(self) -> dict:
        """Get access statistics."""
        stats = {
            "total_accesses": len(self._entries),
            "unique_keys": len(set(e["key"] for e in self._entries)),
            "operations": {},
            "error_count": sum(1 for e in self._entries if not e["success"]),
        }
        for entry in self._entries:
            op = entry["operation"]
            stats["operations"][op] = stats["operations"].get(op, 0) + 1
        return stats

    def clear(self):
        """Clear all log entries."""
        self._entries.clear()


# ---------------------------------------------------------------------------
# ConfigConstraint - cross-key constraints
# ---------------------------------------------------------------------------

class ConfigConstraint:
    """Defines constraints that span multiple configuration keys.

    Example: "max_connections must be >= min_connections"
    """

    def __init__(self):
        self._constraints: List[dict] = []

    def add(self, name: str, keys: List[str],
            check: Callable[[Dict[str, Any]], bool],
            message: str = "") -> "ConfigConstraint":
        """Add a cross-key constraint."""
        self._constraints.append({
            "name": name,
            "keys": keys,
            "check": check,
            "message": message,
        })
        return self

    def validate(self, manager: ConfigManager) -> List[str]:
        """Validate all constraints. Returns list of error messages."""
        errors = []
        for constraint in self._constraints:
            values = {}
            try:
                for key in constraint["keys"]:
                    values[key] = manager.get(key)
            except (ValidationError, KeyError):
                continue  # Skip if keys don't exist

            try:
                if not constraint["check"](values):
                    msg = constraint["message"] or f"Constraint '{constraint['name']}' failed"
                    errors.append(msg)
            except Exception as e:
                errors.append(f"Constraint '{constraint['name']}' error: {e}")

        return errors

    def list_constraints(self) -> List[dict]:
        """List all defined constraints."""
        return [
            {"name": c["name"], "keys": c["keys"], "message": c["message"]}
            for c in self._constraints
        ]


# ---------------------------------------------------------------------------
# ConfigTemplate - configuration templates with placeholders
# ---------------------------------------------------------------------------

class ConfigTemplate:
    """Generates configuration from templates with placeholder substitution.

    Templates define a configuration structure with ${placeholder} values
    that get filled in when the template is applied.
    """

    def __init__(self):
        self._templates: Dict[str, Dict[str, Any]] = {}

    def define(self, name: str, template: Dict[str, Any]) -> "ConfigTemplate":
        """Define a named template."""
        self._templates[name] = dict(template)
        return self

    def apply(self, name: str, variables: Dict[str, str],
              manager: ConfigManager) -> ConfigManager:
        """Apply a template to a ConfigManager with variable substitution."""
        if name not in self._templates:
            raise KeyError(f"Template '{name}' not found")

        template = self._templates[name]
        for key, value in template.items():
            if isinstance(value, str):
                # Substitute ${var} placeholders
                resolved = value
                for var_name, var_value in variables.items():
                    resolved = resolved.replace(f"${{{var_name}}}", str(var_value))
                manager.set(key, resolved)
            else:
                manager.set(key, value)

        return manager

    def list_templates(self) -> List[str]:
        """List all defined template names."""
        return list(self._templates.keys())

    def get_placeholders(self, name: str) -> Set[str]:
        """Get all placeholder names in a template."""
        if name not in self._templates:
            raise KeyError(f"Template '{name}' not found")

        placeholders = set()
        pattern = re.compile(r"\$\{(\w+)\}")
        for value in self._templates[name].values():
            if isinstance(value, str):
                for match in pattern.finditer(value):
                    placeholders.add(match.group(1))
        return placeholders


# ---------------------------------------------------------------------------
# ConfigDiff - comparison between two ConfigManager instances
# ---------------------------------------------------------------------------

class ConfigDiff:
    """Compares two ConfigManager instances and reports differences."""

    def __init__(self, left: ConfigManager, right: ConfigManager):
        self._left = left
        self._right = right

    def compute(self) -> dict:
        """Compute the full diff between left and right."""
        left_keys = set(self._left.keys())
        right_keys = set(self._right.keys())

        only_left = left_keys - right_keys
        only_right = right_keys - left_keys
        common = left_keys & right_keys

        changed = {}
        unchanged = set()

        for key in common:
            try:
                left_val = self._left.get(key)
            except ValidationError:
                left_val = "<validation_error>"
            try:
                right_val = self._right.get(key)
            except ValidationError:
                right_val = "<validation_error>"

            if left_val != right_val:
                changed[key] = {"left": left_val, "right": right_val}
            else:
                unchanged.add(key)

        return {
            "only_left": {k: self._safe_get(self._left, k) for k in only_left},
            "only_right": {k: self._safe_get(self._right, k) for k in only_right},
            "changed": changed,
            "unchanged": sorted(unchanged),
            "summary": {
                "only_left": len(only_left),
                "only_right": len(only_right),
                "changed": len(changed),
                "unchanged": len(unchanged),
            }
        }

    def _safe_get(self, manager: ConfigManager, key: str) -> Any:
        """Safely get a value, returning error marker on failure."""
        try:
            return manager.get(key)
        except (ValidationError, KeyError):
            return "<error>"

    def format_report(self) -> str:
        """Generate a human-readable diff report."""
        diff = self.compute()
        lines = ["=== Configuration Diff ==="]

        if diff["only_left"]:
            lines.append("\nOnly in left:")
            for key, value in sorted(diff["only_left"].items()):
                lines.append(f"  - {key}: {value!r}")

        if diff["only_right"]:
            lines.append("\nOnly in right:")
            for key, value in sorted(diff["only_right"].items()):
                lines.append(f"  + {key}: {value!r}")

        if diff["changed"]:
            lines.append("\nChanged:")
            for key, vals in sorted(diff["changed"].items()):
                lines.append(f"  ~ {key}: {vals['left']!r} -> {vals['right']!r}")

        lines.append(f"\nSummary: {diff['summary']}")
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# End of module
# ---------------------------------------------------------------------------
