from __future__ import annotations
import os
import shutil
from pathlib import Path


def _which(cmd: str) -> bool:
    return shutil.which(cmd) is not None

def _find_project_root(start_path: str, boundary: Path | None = None) -> Path:
    """
    Find the project root by searching for common project files.

    Args:
        start_path: The path to start searching from (typically a test file).
        boundary: Optional boundary path that the search will not traverse above.
                  Defaults to the current working directory to prevent escaping
                  into parent projects.

    Returns:
        The path to the project root, or the start_path's parent directory if
        no project root markers are found within the boundary.
    """
    if boundary is None:
        boundary = Path.cwd().resolve()
    else:
        boundary = boundary.resolve()

    p = Path(start_path).resolve()
    start_parent = p.parent  # Fallback if nothing found

    while p != p.parent:
        # Stop if we've reached or passed the boundary
        if p == boundary or boundary not in p.parents:
            # Check boundary itself before giving up
            if any((boundary / f).exists() for f in ["build.gradle", "build.gradle.kts", "pom.xml", "package.json", "jest.config.js"]):
                return boundary
            break

        if any((p / f).exists() for f in ["build.gradle", "build.gradle.kts", "pom.xml", "package.json", "jest.config.js"]):
            return p
        p = p.parent

    return start_parent

def default_verify_cmd_for(lang: str, unit_test_file: str) -> str | None:
    """
    Return a conservative shell command (bash -lc) that compiles/tests
    and exits 0 on success. Users can override with PDD_AGENTIC_VERIFY_CMD.
    """
    test_rel = unit_test_file
    lang = lang.lower()
    if lang == "python":
        return f'{os.sys.executable} -m pytest "{test_rel}" -q'


    if lang == "javascript" or lang == "typescript":
        example_dir = str(_find_project_root(unit_test_file))
        rel_test_path = os.path.relpath(unit_test_file, example_dir)
        return (
            "set -e\n"
            f'cd "{example_dir}" && '
            "command -v npm >/dev/null 2>&1 || { echo 'npm missing'; exit 127; } && "
            "if [ -f package.json ]; then "
            "  npm install && npm test; "
            "else "
            f'  echo "No package.json in {example_dir}; running test file directly"; '
            f'  node -e "try {{ require(\'./{rel_test_path}\'); }} catch (e) {{ console.error(e); process.exit(1); }}"; '
            "fi"
        )

    if lang == "java":
        # detect maven or gradle?
        root_dir = str(_find_project_root(unit_test_file))
        if "pom.xml" in os.listdir(root_dir):
            return (f"cd '{root_dir}' && mvn test")
        elif "build.gradle" in os.listdir(root_dir) or "build.gradle.kts" in os.listdir(root_dir):
            if "gradlew" in os.listdir(root_dir):
                return f"cd '{root_dir}' && ./gradlew test"
            else:
                return f"cd `{root_dir}` gradle test"
        else:
            return None

    # if lang == "cpp":
    #     # very lightweight: if *_test*.c* exists, build & run; otherwise compile sources only
    #     import shutil
    #     compiler = shutil.which("g++") or shutil.which("clang++")
    #     if compiler is None:
    #         # You can still return a generic command (will be accompanied by missing_tool_hints)
    #         compiler = "g++"
    #     # Example: simple build+smoke or test compile; adapt to your scheme
    #     return (
    #         'set -e\n'
    #         f'cd "{current_working_directory}" && '
    #         'if ls tests/*.cpp >/dev/null 2>&1; then '
    #         f'mkdir -p build && {compiler} -std=c++17 tests/*.cpp src/*.c* -o build/tests && ./build/tests; '
    #         'else '
    #         "echo 'No C++ tests found; building sources only'; "
    #         f'mkdir -p build && {compiler} -std=c++17 -c src/*.c* -o build/obj.o; '
    #         'fi'
    #     )

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
