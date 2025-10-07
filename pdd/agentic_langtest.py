from __future__ import annotations
import os
import shutil
from pathlib import Path


def detect_language(name_or_path) -> str:
    """
    Returns one of: python, typescript, javascript, java, cpp, kotlin, or 'unknown'.
    Accepts a Path or any string (filename, extension, or full path).
    """
    p = Path(str(name_or_path))
    s = str(name_or_path).strip().lower()

    # If the user passed a bare extension like ".ts" or ".CPP"
    if s.startswith(".") and len(s) <= 6:
        ext = s
    else:
        ext = p.suffix.lower()

    # Map known extensions
    ext_map = {
        ".py": "python",
        ".ts": "typescript",
        ".tsx": "typescript",
        ".js": "javascript",
        ".mjs": "javascript",
        ".cjs": "javascript",
        ".java": "java",
        ".kt": "kotlin",     # harmless to support, even if you don't auto-verify Kotlin
        ".cpp": "cpp",
        ".cc": "cpp",
        ".cxx": "cpp",
        ".hpp": "cpp",
        ".hh": "cpp",
        ".hxx": "cpp",
    }
    return ext_map.get(ext, "unknown")


def _which(cmd: str) -> bool:
    return shutil.which(cmd) is not None

def default_verify_cmd_for(lang: str, project_root: Path, unit_test_file: str) -> str | None:
    """
    Return a conservative shell command (bash -lc) that compiles/tests
    and exits 0 on success. Users can override with PDD_AGENTIC_VERIFY_CMD.
    """
    pr = str(project_root)
    test_rel = unit_test_file

    if lang == "python":
        return f'{os.sys.executable} -m pytest "{test_rel}" -q'

    if lang == "typescript":
        # Determine the example's root directory from the unit test file path
        example_dir = str(Path(unit_test_file).parent.parent)
        return (
            "set -e\n"
            # Change to the example's directory so npm can find the correct package.json
            f'cd "{example_dir}" && '
            "command -v npm >/dev/null 2>&1 || { echo 'npm missing'; exit 127; } && "
            "if [ -f package.json ]; then "
            # Use the standard npm test command, which is configured in package.json
            "  npm test; "
            "else "
            # Fallback to a simple type-check if no package.json is found
            "  echo 'No package.json; falling back to typecheck only'; npx --yes tsc --noEmit; "
            "fi"
        )

    if lang == "javascript":
        example_dir = str(Path(unit_test_file).parent.parent)
        return (
            "set -e\n"
            f'cd "{example_dir}" && '
            "command -v npm >/dev/null 2/dev/null 2>&1 || { echo 'npm missing'; exit 127; } && "
            "if [ -f package.json ]; then "
            "  npm test; "
            "else "
            f'  echo "No package.json in {example_dir}; running test file directly"; '
            f'  node "{unit_test_file}"; '
            "fi"
        )

    if lang == "java":
        # Expect a ConsoleLauncher JAR somewhere in project root.
        return (
            "set -e\n"
            f'cd "{pr}" && '
            'JAR="$(ls -1 *.jar 2>/dev/null | grep -i \"junit.*console\" | head -n1 || true)"; '
            'if [ -z \"$JAR\" ]; then echo \"JUnit Console jar missing\"; exit 127; fi; '
            "mkdir -p build && "
            "javac -d build src/*.java tests/*.java && "
            'java -jar \"$JAR\" --class-path build --scan-class-path'
        )

    if lang == "cpp":
        # very lightweight: if *_test*.c* exists, build & run; otherwise compile sources only
        import shutil
        compiler = shutil.which("g++") or shutil.which("clang++")
        if compiler is None:
            # You can still return a generic command (will be accompanied by missing_tool_hints)
            compiler = "g++"
        # Example: simple build+smoke or test compile; adapt to your scheme
        return (
            'set -e\n'
            f'cd "{project_root}" && '
            'if ls tests/*.cpp >/dev/null 2>&1; then '
            f'mkdir -p build && {compiler} -std=c++17 tests/*.cpp src/*.c* -o build/tests && ./build/tests; '
            'else '
            "echo 'No C++ tests found; building sources only'; "
            f'mkdir -p build && {compiler} -std=c++17 -c src/*.c* -o build/obj.o; '
            'fi'
        )

    return None

def missing_tool_hints(lang: str, verify_cmd: str | None, project_root: Path) -> str | None:
    """
    If a required tool looks missing, return a one-time guidance string.
    We do not install automatically; we just hint.
    """
    if not verify_cmd:
        return None

    need = []
    if lang in ("typescript", "javascript"):
        if not _which("npm"):
            need.append("npm (Node.js)")
    if lang == "java":
        if not _which("javac") or not _which("java"):
            need.append("Java JDK (javac, java)")
        jar_present = any(
            p.name.endswith(".jar") and "junit" in p.name.lower() and "console" in p.name.lower()
            for p in project_root.glob("*.jar")
        )
        if not jar_present:
            need.append("JUnit ConsoleLauncher jar (e.g. junit-platform-console-standalone.jar)")
    if lang == "cpp":
        if not _which("g++"):
            need.append("g++")

    if not need:
        return None

    install_lines = []
    if "npm (Node.js)" in need:
        install_lines += [
            "macOS:  brew install node",
            "Ubuntu: sudo apt-get update && sudo apt-get install -y nodejs npm",
        ]
    if "Java JDK (javac, java)" in need:
        install_lines += [
            "macOS:  brew install openjdk",
            "Ubuntu: sudo apt-get update && sudo apt-get install -y openjdk-17-jdk",
        ]
    if "JUnit ConsoleLauncher jar (e.g. junit-platform-console-standalone.jar)" in need:
        install_lines += [
            "Download the ConsoleLauncher jar from Maven Central and place it in your project root, e.g.:",
            "  curl -LO https://repo1.maven.org/maven2/org/junit/platform/junit-platform-console-standalone/1.10.2/junit-platform-console-standalone-1.10.2.jar",
        ]
    if "g++" in need:
        install_lines += [
            "macOS:  xcode-select --install   # or: brew install gcc",
            "Ubuntu: sudo apt-get update && sudo apt-get install -y build-essential",
        ]

    return (
        "[yellow]Some tools required to run non-Python tests seem missing.[/yellow]\n  - "
        + "\n  - ".join(need)
        + "\n[dim]Suggested installs:\n  "
        + "\n  ".join(install_lines)
        + "[/dim]"
    )
