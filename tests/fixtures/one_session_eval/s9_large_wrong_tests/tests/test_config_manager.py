"""
Tests for config_manager module.

NOTE: Several tests in this file were written assuming EAGER validation
(validate on set). The actual spec and implementation use LAZY validation
(validate on get/save). Tests marked with "# WRONG:" have incorrect
expectations and will FAIL.
"""

import json
import os
import sys
import tempfile
import time
import unittest

# Add the src directory to path so we can import config_manager
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from config_manager import (
    ConfigManager,
    ConfigLayer,
    ValidationError,
    ParseError,
    SchemaEntry,
    ChangeRecord,
    TypeCoercer,
    NamespaceResolver,
    SimpleYamlParser,
    ConfigBuilder,
    ConfigProfile,
    ConfigDumper,
)


class TestSchemaDefinition(unittest.TestCase):
    """Tests for schema definition."""

    def test_define_basic_schema(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        self.assertTrue(mgr.has_schema("host"))

    def test_define_schema_sets_default(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        self.assertEqual(mgr.get("host"), "localhost")

    def test_define_required_schema(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, required=True)
        info = mgr.get_schema_info()
        self.assertTrue(any(e["required"] for e in info if e["key"] == "host"))

    def test_define_schema_with_validator(self):
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080,
                          validator=lambda v: 1 <= v <= 65535)
        self.assertTrue(mgr.has_schema("port"))


class TestSetInvalidTypeRaises(unittest.TestCase):
    """Tests for set() with invalid types."""

    def test_set_invalid_type_raises(self):
        # WRONG: Assumes set() validates eagerly. Spec says lazy validation:
        # set() stores whatever you give it; error surfaces on get().
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080)
        with self.assertRaises(ValidationError):
            mgr.set("port", "not_a_number")

    def test_set_required_to_none_raises(self):
        # WRONG: Assumes set() validates required constraint eagerly.
        # Spec says set() never validates. None is stored silently;
        # error surfaces on get() or save().
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, required=True, default="localhost")
        with self.assertRaises(ValidationError):
            mgr.set("host", None)

    def test_set_with_custom_validator_rejects(self):
        # WRONG: Assumes set() runs the custom validator eagerly.
        # Spec says validation is lazy — set() stores the value,
        # validator runs on get().
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080,
                          validator=lambda v: 1 <= v <= 65535)
        with self.assertRaises(ValidationError):
            mgr.set("port", 99999)

    def test_set_negative_port_raises(self):
        # WRONG: Assumes set() runs the custom validator eagerly.
        # Spec says lazy validation — set() succeeds, get() validates.
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080,
                          validator=lambda v: v > 0)
        with self.assertRaises(ValidationError):
            mgr.set("port", -1)

    def test_set_empty_string_required_raises(self):
        # WRONG: Assumes set("name", "") on a required field raises.
        # Spec says set() never validates. Empty string is stored silently.
        # (Empty string is not None, so it wouldn't even fail required check.)
        mgr = ConfigManager()
        mgr.define_schema("name", type=str, required=True, default="default_name")
        with self.assertRaises(ValidationError):
            mgr.set("name", "")


class TestBulkSetRollback(unittest.TestCase):
    """Tests for bulk set behavior with invalid values."""

    def test_bulk_set_invalid_rolls_back(self):
        # WRONG: Assumes set_many() validates values and rolls back on
        # validation error. Spec says set()/set_many() never validates.
        # All values are stored, no rollback occurs.
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        mgr.define_schema("port", type=int, default=8080,
                          validator=lambda v: 1 <= v <= 65535)
        mgr.define_schema("name", type=str, default="app")

        original_host = mgr.get("host")
        with self.assertRaises(ValidationError):
            mgr.set_many({
                "host": "newhost",
                "port": 99999,  # invalid
                "name": "newapp",
            })
        # Expects rollback — host should be original
        self.assertEqual(mgr.get("host"), original_host)


class TestImportValidation(unittest.TestCase):
    """Tests for import validation."""

    def test_import_invalid_json_validates(self):
        # WRONG: Assumes import_json() validates values against schema.
        # Spec says import loads into OVERRIDE layer without validation
        # (lazy validation). Invalid values are stored silently.
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080,
                          validator=lambda v: 1 <= v <= 65535)

        data = json.dumps({"port": "not_a_number"})
        with self.assertRaises(ValidationError):
            mgr.import_json(data)


class TestLoadEnvValidation(unittest.TestCase):
    """Tests for load_env validation."""

    def test_load_env_validates_types(self):
        # WRONG: Assumes load_env() validates type coercion immediately.
        # Spec says load_env() stores string values in ENVIRONMENT layer
        # without validation. Coercion and validation happen on get().
        mgr = ConfigManager()
        mgr.define_schema("server.port", type=int, default=8080)

        env = {"MYAPP_SERVER_PORT": "not_a_number"}
        with self.assertRaises(ValidationError):
            mgr.load_env("MYAPP", environ=env)


class TestGetValidation(unittest.TestCase):
    """Tests for get() with lazy validation — these are CORRECT."""

    def test_get_invalid_type_raises(self):
        """get() validates lazily and raises on type mismatch."""
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080)
        mgr.set("port", "not_a_number")  # set succeeds
        with self.assertRaises(ValidationError):
            mgr.get("port")  # validation happens here

    def test_get_required_none_raises(self):
        """get() raises for required key with None value."""
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, required=True)
        # Don't set any value — required key is missing
        with self.assertRaises(ValidationError):
            mgr.get("host")

    def test_get_custom_validator_fails(self):
        """get() runs custom validator and raises on failure."""
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080,
                          validator=lambda v: 1 <= v <= 65535)
        mgr.set("port", 99999)  # set succeeds
        with self.assertRaises(ValidationError):
            mgr.get("port")  # validator runs here

    def test_get_with_type_coercion(self):
        """get() coerces string values to the schema type."""
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080)
        mgr.set("port", "3000")  # string, will be coerced
        self.assertEqual(mgr.get("port"), 3000)

    def test_get_coerces_bool(self):
        """get() coerces string to bool."""
        mgr = ConfigManager()
        mgr.define_schema("debug", type=bool, default=False)
        mgr.set("debug", "true")
        self.assertTrue(mgr.get("debug"))

    def test_get_coerces_float(self):
        """get() coerces string to float."""
        mgr = ConfigManager()
        mgr.define_schema("rate", type=float, default=1.0)
        mgr.set("rate", "2.5")
        self.assertAlmostEqual(mgr.get("rate"), 2.5)

    def test_get_default_when_not_set(self):
        """get() returns schema default when key not in any layer."""
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        self.assertEqual(mgr.get("host"), "localhost")

    def test_get_explicit_default(self):
        """get() returns explicit default when key has no schema and no value."""
        mgr = ConfigManager()
        self.assertEqual(mgr.get("unknown", default="fallback"), "fallback")


class TestSaveValidation(unittest.TestCase):
    """Tests for save() validation — these are CORRECT."""

    def test_save_validates_required(self):
        """save() validates required keys before writing."""
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, required=True)
        # No value set for required key
        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        try:
            with self.assertRaises(ValidationError):
                mgr.save(path)
        finally:
            if os.path.exists(path):
                os.unlink(path)

    def test_save_validates_types(self):
        """save() validates types before writing."""
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080)
        mgr.set("port", "not_a_number")  # set succeeds

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        try:
            with self.assertRaises(ValidationError):
                mgr.save(path)  # validation happens here
        finally:
            if os.path.exists(path):
                os.unlink(path)

    def test_save_validates_custom_validator(self):
        """save() runs custom validators."""
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080,
                          validator=lambda v: 1 <= v <= 65535)
        mgr.set("port", 99999)

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        try:
            with self.assertRaises(ValidationError):
                mgr.save(path)
        finally:
            if os.path.exists(path):
                os.unlink(path)

    def test_save_succeeds_when_valid(self):
        """save() writes file when all values are valid."""
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost", required=True)
        mgr.define_schema("port", type=int, default=8080)

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        try:
            self.assertTrue(mgr.save(path))
            self.assertTrue(os.path.exists(path))
            content = json.loads(open(path).read())
            self.assertEqual(content["host"], "localhost")
            self.assertEqual(content["port"], 8080)
        finally:
            if os.path.exists(path):
                os.unlink(path)


class TestLayerResolution(unittest.TestCase):
    """Tests for layered configuration resolution — CORRECT."""

    def test_override_beats_file(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="default_host")
        mgr.set("host", "file_host", layer=ConfigLayer.FILE)
        mgr.set("host", "override_host", layer=ConfigLayer.OVERRIDE)
        self.assertEqual(mgr.get("host"), "override_host")

    def test_env_beats_file(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="default_host")
        mgr.set("host", "file_host", layer=ConfigLayer.FILE)
        mgr.set("host", "env_host", layer=ConfigLayer.ENVIRONMENT)
        self.assertEqual(mgr.get("host"), "env_host")

    def test_file_beats_default(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="default_host")
        mgr.set("host", "file_host", layer=ConfigLayer.FILE)
        self.assertEqual(mgr.get("host"), "file_host")

    def test_override_beats_all(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="default_host")
        mgr.set("host", "file_host", layer=ConfigLayer.FILE)
        mgr.set("host", "env_host", layer=ConfigLayer.ENVIRONMENT)
        mgr.set("host", "override_host", layer=ConfigLayer.OVERRIDE)
        self.assertEqual(mgr.get("host"), "override_host")

    def test_default_used_when_no_other_layer(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="default_host")
        self.assertEqual(mgr.get("host"), "default_host")

    def test_delete_override_reveals_env(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="default_host")
        mgr.set("host", "env_host", layer=ConfigLayer.ENVIRONMENT)
        mgr.set("host", "override_host", layer=ConfigLayer.OVERRIDE)
        self.assertEqual(mgr.get("host"), "override_host")
        mgr.delete("host", layer=ConfigLayer.OVERRIDE)
        self.assertEqual(mgr.get("host"), "env_host")


class TestNamespaceSupport(unittest.TestCase):
    """Tests for dot-separated namespace support — CORRECT."""

    def test_get_namespace(self):
        mgr = ConfigManager()
        mgr.set("database.host", "localhost")
        mgr.set("database.port", 5432)
        mgr.set("database.name", "mydb")
        mgr.set("cache.host", "redis")

        ns = mgr.get_namespace("database")
        self.assertEqual(ns["host"], "localhost")
        self.assertEqual(ns["port"], 5432)
        self.assertEqual(ns["name"], "mydb")
        self.assertNotIn("cache.host", ns)

    def test_nested_namespace(self):
        mgr = ConfigManager()
        mgr.set("database.connection.host", "localhost")
        mgr.set("database.connection.port", 5432)
        mgr.set("database.pool.size", 10)

        ns = mgr.get_namespace("database.connection")
        self.assertEqual(ns["host"], "localhost")
        self.assertEqual(ns["port"], 5432)
        self.assertNotIn("pool.size", ns)

    def test_empty_namespace(self):
        mgr = ConfigManager()
        mgr.set("database.host", "localhost")
        ns = mgr.get_namespace("nonexistent")
        self.assertEqual(ns, {})


class TestChangeTracking(unittest.TestCase):
    """Tests for change tracking — CORRECT."""

    def test_set_records_change(self):
        mgr = ConfigManager()
        mgr.set("host", "localhost")
        changes = mgr.get_changes()
        self.assertIn("host", changes)
        self.assertEqual(changes["host"].new_value, "localhost")

    def test_multiple_changes_tracked(self):
        mgr = ConfigManager()
        mgr.set("host", "localhost")
        mgr.set("port", 8080)
        changes = mgr.get_changes()
        self.assertEqual(len(changes), 2)

    def test_reset_clears_changes(self):
        mgr = ConfigManager()
        mgr.set("host", "localhost")
        self.assertTrue(mgr.has_unsaved_changes())
        mgr.reset()
        self.assertFalse(mgr.has_unsaved_changes())

    def test_save_clears_changes(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        mgr.set("host", "newhost")
        self.assertTrue(mgr.has_unsaved_changes())

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        try:
            mgr.save(path)
            self.assertFalse(mgr.has_unsaved_changes())
        finally:
            if os.path.exists(path):
                os.unlink(path)

    def test_change_record_has_old_and_new(self):
        mgr = ConfigManager()
        mgr.set("host", "first_value")
        mgr.set("host", "second_value")
        changes = mgr.get_changes()
        record = changes["host"]
        self.assertEqual(record.old_value, "first_value")
        self.assertEqual(record.new_value, "second_value")


class TestSnapshotRestore(unittest.TestCase):
    """Tests for snapshot/restore — CORRECT."""

    def test_snapshot_and_restore(self):
        mgr = ConfigManager()
        mgr.set("host", "original")
        sid = mgr.snapshot()

        mgr.set("host", "modified")
        self.assertEqual(mgr.get("host"), "modified")

        mgr.restore(sid)
        self.assertEqual(mgr.get("host"), "original")

    def test_multiple_snapshots(self):
        mgr = ConfigManager()
        mgr.set("host", "v1")
        sid1 = mgr.snapshot()

        mgr.set("host", "v2")
        sid2 = mgr.snapshot()

        mgr.set("host", "v3")

        mgr.restore(sid1)
        self.assertEqual(mgr.get("host"), "v1")

        mgr.restore(sid2)
        self.assertEqual(mgr.get("host"), "v2")

    def test_restore_invalid_id_raises(self):
        mgr = ConfigManager()
        with self.assertRaises(KeyError):
            mgr.restore("nonexistent_id")

    def test_list_snapshots(self):
        mgr = ConfigManager()
        mgr.set("host", "v1")
        mgr.snapshot()
        mgr.set("host", "v2")
        mgr.snapshot()
        snapshots = mgr.list_snapshots()
        self.assertEqual(len(snapshots), 2)


class TestAtomicSave(unittest.TestCase):
    """Tests for atomic save — CORRECT."""

    def test_save_creates_file(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        os.unlink(path)  # Remove so save creates it

        try:
            mgr.save(path)
            self.assertTrue(os.path.exists(path))
        finally:
            if os.path.exists(path):
                os.unlink(path)

    def test_save_content_is_valid_json(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        mgr.define_schema("port", type=int, default=8080)

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        try:
            mgr.save(path)
            with open(path) as f:
                data = json.load(f)
            self.assertIsInstance(data, dict)
            self.assertEqual(data["host"], "localhost")
        finally:
            if os.path.exists(path):
                os.unlink(path)

    def test_save_and_load_roundtrip(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        mgr.define_schema("port", type=int, default=8080)
        mgr.set("host", "myserver")
        mgr.set("port", 3000)

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name
        try:
            mgr.save(path)

            mgr2 = ConfigManager()
            mgr2.define_schema("host", type=str)
            mgr2.define_schema("port", type=int)
            mgr2.load(path)
            self.assertEqual(mgr2.get("host"), "myserver")
            self.assertEqual(mgr2.get("port"), 3000)
        finally:
            if os.path.exists(path):
                os.unlink(path)


class TestJsonExportImport(unittest.TestCase):
    """Tests for JSON export/import with valid data — CORRECT."""

    def test_export_json(self):
        mgr = ConfigManager()
        mgr.set("host", "localhost")
        mgr.set("port", 8080)
        exported = mgr.export_json()
        data = json.loads(exported)
        self.assertEqual(data["host"], "localhost")
        self.assertEqual(data["port"], 8080)

    def test_import_json_valid(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str)
        mgr.define_schema("port", type=int)
        data = json.dumps({"host": "newhost", "port": 3000})
        mgr.import_json(data)
        self.assertEqual(mgr.get("host"), "newhost")
        self.assertEqual(mgr.get("port"), 3000)

    def test_export_import_roundtrip(self):
        mgr = ConfigManager()
        mgr.set("database.host", "localhost")
        mgr.set("database.port", 5432)
        exported = mgr.export_json()

        mgr2 = ConfigManager()
        mgr2.import_json(exported)
        self.assertEqual(mgr2.get("database.host"), "localhost")
        self.assertEqual(mgr2.get("database.port"), 5432)


class TestEnvironmentLoading(unittest.TestCase):
    """Tests for environment variable loading — CORRECT."""

    def test_load_env_basic(self):
        mgr = ConfigManager()
        mgr.define_schema("server.host", type=str, default="localhost")
        mgr.define_schema("server.port", type=int, default=8080)

        env = {
            "MYAPP_SERVER_HOST": "envhost",
            "MYAPP_SERVER_PORT": "3000",
        }
        mgr.load_env("MYAPP", environ=env)

        self.assertEqual(mgr.get("server.host"), "envhost")
        self.assertEqual(mgr.get("server.port"), 3000)  # coerced on get()

    def test_load_env_prefix_stripping(self):
        mgr = ConfigManager()
        env = {"APP_DATABASE_HOST": "dbhost"}
        mgr.load_env("APP", environ=env)
        self.assertEqual(mgr.get("database.host"), "dbhost")

    def test_env_layer_priority(self):
        """Environment layer should beat file but lose to override."""
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="default")
        mgr.set("host", "file_host", layer=ConfigLayer.FILE)

        env = {"MYAPP_HOST": "env_host"}
        mgr.load_env("MYAPP", environ=env)

        self.assertEqual(mgr.get("host"), "env_host")  # env beats file

        mgr.set("host", "override_host")  # override beats env
        self.assertEqual(mgr.get("host"), "override_host")


class TestExplicitValidate(unittest.TestCase):
    """Tests for explicit validate() call — CORRECT."""

    def test_validate_returns_errors(self):
        mgr = ConfigManager()
        mgr.define_schema("port", type=int, default=8080)
        mgr.set("port", "not_a_number")  # set succeeds
        errors = mgr.validate()
        self.assertTrue(len(errors) > 0)
        self.assertEqual(errors[0].key, "port")

    def test_validate_returns_empty_when_valid(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        mgr.define_schema("port", type=int, default=8080)
        errors = mgr.validate()
        self.assertEqual(len(errors), 0)

    def test_is_valid(self):
        mgr = ConfigManager()
        mgr.define_schema("host", type=str, default="localhost")
        self.assertTrue(mgr.is_valid())
        mgr.set("host", 12345)  # wrong type, but set succeeds
        self.assertFalse(mgr.is_valid())  # validate catches it


class TestTypeCoercer(unittest.TestCase):
    """Tests for TypeCoercer utility — CORRECT."""

    def test_coerce_int(self):
        c = TypeCoercer()
        self.assertEqual(c.coerce("42", int), 42)

    def test_coerce_float(self):
        c = TypeCoercer()
        self.assertAlmostEqual(c.coerce("3.14", float), 3.14)

    def test_coerce_bool_true(self):
        c = TypeCoercer()
        self.assertTrue(c.coerce("true", bool))
        self.assertTrue(c.coerce("yes", bool))
        self.assertTrue(c.coerce("1", bool))

    def test_coerce_bool_false(self):
        c = TypeCoercer()
        self.assertFalse(c.coerce("false", bool))
        self.assertFalse(c.coerce("no", bool))
        self.assertFalse(c.coerce("0", bool))

    def test_coerce_list(self):
        c = TypeCoercer()
        result = c.coerce("[1, 2, 3]", list)
        self.assertEqual(result, [1, 2, 3])

    def test_coerce_dict(self):
        c = TypeCoercer()
        result = c.coerce('{"a": 1}', dict)
        self.assertEqual(result, {"a": 1})


class TestNamespaceResolver(unittest.TestCase):
    """Tests for NamespaceResolver utility — CORRECT."""

    def test_split_key(self):
        ns = NamespaceResolver()
        self.assertEqual(ns.split_key("database.host"), ["database", "host"])

    def test_get_namespace(self):
        ns = NamespaceResolver()
        self.assertEqual(ns.get_namespace("database.connection.host"),
                         "database.connection")

    def test_flatten(self):
        ns = NamespaceResolver()
        result = ns.flatten({"database": {"host": "localhost", "port": 5432}})
        self.assertEqual(result["database.host"], "localhost")
        self.assertEqual(result["database.port"], 5432)

    def test_unflatten(self):
        ns = NamespaceResolver()
        result = ns.unflatten({"database.host": "localhost", "database.port": 5432})
        self.assertEqual(result["database"]["host"], "localhost")
        self.assertEqual(result["database"]["port"], 5432)


class TestMethodChaining(unittest.TestCase):
    """Tests for method chaining — CORRECT."""

    def test_set_returns_self(self):
        mgr = ConfigManager()
        result = mgr.set("host", "localhost")
        self.assertIs(result, mgr)

    def test_chain_multiple_sets(self):
        mgr = ConfigManager()
        mgr.set("host", "localhost").set("port", 8080).set("debug", True)
        self.assertEqual(mgr.get("host"), "localhost")
        self.assertEqual(mgr.get("port"), 8080)
        self.assertTrue(mgr.get("debug"))

    def test_define_schema_returns_self(self):
        mgr = ConfigManager()
        result = mgr.define_schema("host", type=str, default="localhost")
        self.assertIs(result, mgr)


if __name__ == "__main__":
    unittest.main()
