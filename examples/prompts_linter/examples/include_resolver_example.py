import sys
import os
from pathlib import Path
import shutil

# Add the parent directory to sys.path to import the module
# Assuming this script is in examples/ and the module is in src/backend/core/
current_dir = Path(__file__).resolve().parent
project_root = current_dir.parent  # Adjust based on actual structure
sys.path.append(str(project_root))

# Import the module
# Note: Adjust the import path based on your actual package structure
try:
    from src.backend.core.include_resolver import IncludeResolver, PathSecurityError, FileLoadError
except ImportError:
    # Fallback for flat directory structures or direct testing
    sys.path.append(str(current_dir.parent / "src" / "backend" / "core"))
    try:
        from include_resolver import IncludeResolver, PathSecurityError, FileLoadError
    except ImportError:
        # Mock classes for demonstration if the actual module is not found in the environment
        class PathSecurityError(Exception): pass
        class FileLoadError(Exception): pass
        class IncludeResolver:
            def __init__(self, root_path: Path):
                self.root_path = root_path
            def resolve(self, relative_path: str, current_file_dir: Path) -> Path:
                target = (current_file_dir / relative_path).resolve()
                if not str(target).startswith(str(self.root_path)):
                    raise PathSecurityError(f"Access denied: {target} is outside root {self.root_path}")
                return target
            def read_content(self, path: Path) -> str:
                if not path.exists():
                    raise FileLoadError(f"File not found: {path}")
                return path.read_text(encoding="utf-8")
            def estimate_tokens(self, content: str) -> int:
                return len(content.split())

def create_dummy_files(base_dir: Path) -> None:
    """Helper to create some test files for the example."""
    (base_dir / "safe_file.txt").write_text("This is safe content.", encoding="utf-8")
    (base_dir / "subdir").mkdir(exist_ok=True)
    (base_dir / "subdir" / "nested.txt").write_text("Nested content.", encoding="utf-8")

def main() -> None:
    # 1. Setup: Define a security root
    # We will use a temporary directory as our "project root" for safety
    base_dir = Path("temp_example_root").resolve()
    base_dir.mkdir(exist_ok=True)
    try:
        create_dummy_files(base_dir)

        print(f"--- Initializing Resolver with root: {base_dir} ---")
        
        # Initialize the resolver. Only files inside base_dir can be accessed.
        resolver = IncludeResolver(root_path=base_dir)

        # 2. Example: Resolving and reading a valid file
        print("\n--- 1. Valid File Access ---")
        try:
            # Simulate finding an include tag in a file located at base_dir
            # Tag: <include>safe_file.txt</include>
            relative_path = "safe_file.txt"
            current_file_dir = base_dir 

            resolved_path = resolver.resolve(relative_path, current_file_dir)
            print(f"Resolved path: {resolved_path}")

            content = resolver.read_content(resolved_path)
            print(f"Content: {content}")
            
            tokens = resolver.estimate_tokens(content)
            print(f"Estimated tokens: {tokens}")

        except (PathSecurityError, FileLoadError) as e:
            print(f"Error: {e}")

        # 3. Example: Resolving a nested file
        print("\n--- 2. Nested File Access ---")
        try:
            # Tag: <include>subdir/nested.txt</include>
            relative_path = "subdir/nested.txt"
            
            resolved_path = resolver.resolve(relative_path, base_dir)
            print(f"Resolved path: {resolved_path}")
            print(f"Content: {resolver.read_content(resolved_path)}")

        except Exception as e:
            print(f"Error: {e}")

        # 4. Example: Security Violation (Path Traversal)
        print("\n--- 3. Security Violation Attempt ---")
        try:
            # Attempt to access a file outside the root (e.g., system hosts file or parent dir)
            # Tag: <include>../../../../etc/passwd</include>
            relative_path = "../../../../etc/passwd" 
            
            print(f"Attempting to resolve: {relative_path}")
            resolver.resolve(relative_path, base_dir)
            
        except PathSecurityError as e:
            print(f"Security Blocked: {e}")
        except Exception as e:
            print(f"Unexpected error: {e}")

        # 5. Example: Missing File
        print("\n--- 4. Missing File Handling ---")
        try:
            relative_path = "ghost_file.txt"
            resolved_path = resolver.resolve(relative_path, base_dir)
            # The resolve step usually succeeds if the path is syntactically valid and secure,
            # even if the file doesn't exist. The error happens on read.
            resolver.read_content(resolved_path)
        except FileLoadError as e:
            print(f"Load Error: {e}")

    finally:
        # Cleanup
        if base_dir.exists():
            shutil.rmtree(base_dir)

if __name__ == "__main__":
    main()