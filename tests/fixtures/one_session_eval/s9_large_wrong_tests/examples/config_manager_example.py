"""
Example demonstrating the config_manager module.

Shows:
- Schema definition
- Layered configuration (defaults, file, env, overrides)
- Lazy validation (set never validates, get/save do)
- Type coercion
- Namespace support
- Change tracking
- Snapshot/restore
- JSON export/import
"""

import json
import os
import sys
import tempfile

# Add the src directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from config_manager import (
    ConfigManager,
    ConfigLayer,
    ValidationError,
    ConfigBuilder,
)


def main():
    # ---------------------------------------------------------------
    # 1. Create a ConfigManager and define schema
    # ---------------------------------------------------------------
    print("=== 1. Schema Definition ===")
    mgr = ConfigManager()

    mgr.define_schema("server.host", type=str, default="localhost", required=True,
                      description="Server hostname")
    mgr.define_schema("server.port", type=int, default=8080,
                      validator=lambda v: 1 <= v <= 65535,
                      description="Server port")
    mgr.define_schema("server.debug", type=bool, default=False,
                      description="Debug mode")
    mgr.define_schema("database.host", type=str, default="localhost")
    mgr.define_schema("database.port", type=int, default=5432)
    mgr.define_schema("database.name", type=str, default="myapp")
    mgr.define_schema("cache.ttl", type=int, default=300)

    print(f"Keys defined: {len(mgr.get_schema_info())}")
    print(f"Default host: {mgr.get('server.host')}")
    print(f"Default port: {mgr.get('server.port')}")

    # ---------------------------------------------------------------
    # 2. Lazy validation demo — set() never raises
    # ---------------------------------------------------------------
    print("\n=== 2. Lazy Validation ===")

    # This succeeds even though "not_a_number" is not an int!
    mgr.set("server.port", "not_a_number")
    print("set('server.port', 'not_a_number') succeeded (no validation on set)")

    # The error surfaces when we try to get() the value
    try:
        mgr.get("server.port")
    except ValidationError as e:
        print(f"get('server.port') raised: {e}")

    # Fix it with a valid value
    mgr.set("server.port", 3000)
    print(f"After fix, server.port = {mgr.get('server.port')}")

    # ---------------------------------------------------------------
    # 3. Layered resolution
    # ---------------------------------------------------------------
    print("\n=== 3. Layered Resolution ===")

    mgr.set("server.host", "file-host", layer=ConfigLayer.FILE)
    print(f"After FILE layer set: {mgr.get('server.host')}")

    mgr.set("server.host", "env-host", layer=ConfigLayer.ENVIRONMENT)
    print(f"After ENV layer set: {mgr.get('server.host')}")

    mgr.set("server.host", "override-host", layer=ConfigLayer.OVERRIDE)
    print(f"After OVERRIDE: {mgr.get('server.host')}")

    mgr.delete("server.host", layer=ConfigLayer.OVERRIDE)
    print(f"After delete OVERRIDE: {mgr.get('server.host')}")

    # ---------------------------------------------------------------
    # 4. Environment variable loading
    # ---------------------------------------------------------------
    print("\n=== 4. Environment Variables ===")

    fake_env = {
        "MYAPP_SERVER_HOST": "env-server",
        "MYAPP_SERVER_PORT": "9090",
        "MYAPP_DATABASE_HOST": "env-db",
    }
    mgr.load_env("MYAPP", environ=fake_env)
    print(f"server.host from env: {mgr.get('server.host')}")
    print(f"server.port from env (coerced): {mgr.get('server.port')}")

    # ---------------------------------------------------------------
    # 5. Namespace support
    # ---------------------------------------------------------------
    print("\n=== 5. Namespaces ===")

    db_config = mgr.get_namespace("database")
    print(f"Database namespace: {db_config}")

    server_config = mgr.get_namespace("server")
    print(f"Server namespace: {server_config}")

    # ---------------------------------------------------------------
    # 6. Change tracking
    # ---------------------------------------------------------------
    print("\n=== 6. Change Tracking ===")

    mgr2 = ConfigManager()
    mgr2.define_schema("host", type=str, default="localhost")
    mgr2.set("host", "newhost")
    mgr2.set("port", 3000)

    changes = mgr2.get_changes()
    for key, record in changes.items():
        print(f"  {key}: {record.old_value!r} -> {record.new_value!r}")

    print(f"Has unsaved changes: {mgr2.has_unsaved_changes()}")

    # ---------------------------------------------------------------
    # 7. Snapshot/restore
    # ---------------------------------------------------------------
    print("\n=== 7. Snapshot/Restore ===")

    mgr3 = ConfigManager()
    mgr3.set("version", "1.0")
    sid = mgr3.snapshot()
    print(f"Snapshot created: {sid}")

    mgr3.set("version", "2.0")
    print(f"After update: {mgr3.get('version')}")

    mgr3.restore(sid)
    print(f"After restore: {mgr3.get('version')}")

    # ---------------------------------------------------------------
    # 8. JSON export/import
    # ---------------------------------------------------------------
    print("\n=== 8. JSON Export/Import ===")

    mgr4 = ConfigManager()
    mgr4.set("app.name", "MyApp")
    mgr4.set("app.version", "1.0.0")
    mgr4.set("app.features.auth", True)

    exported = mgr4.export_json()
    print(f"Exported JSON:\n{exported}")

    mgr5 = ConfigManager()
    mgr5.import_json(exported)
    print(f"Imported app.name: {mgr5.get('app.name')}")

    # ---------------------------------------------------------------
    # 9. Atomic save and load
    # ---------------------------------------------------------------
    print("\n=== 9. Save and Load ===")

    mgr6 = ConfigManager()
    mgr6.define_schema("app.name", type=str, default="TestApp", required=True)
    mgr6.define_schema("app.port", type=int, default=8080)

    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
        path = f.name

    try:
        mgr6.save(path)
        print(f"Saved to {path}")

        mgr7 = ConfigManager()
        mgr7.define_schema("app.name", type=str)
        mgr7.define_schema("app.port", type=int)
        mgr7.load(path)
        print(f"Loaded app.name: {mgr7.get('app.name')}")
        print(f"Loaded app.port: {mgr7.get('app.port')}")
    finally:
        os.unlink(path)

    # ---------------------------------------------------------------
    # 10. ConfigBuilder (fluent API)
    # ---------------------------------------------------------------
    print("\n=== 10. ConfigBuilder ===")

    config = (ConfigBuilder()
              .with_schema("host", str, default="localhost", required=True)
              .with_schema("port", int, default=8080)
              .with_schema("debug", bool, default=False)
              .with_override("host", "builder-host")
              .build())

    print(f"Builder host: {config.get('host')}")
    print(f"Builder port: {config.get('port')}")

    print("\n=== Done ===")


if __name__ == "__main__":
    main()
