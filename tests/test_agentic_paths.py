from pathlib import Path
from pdd.agentic_paths import normalize_target_path

def test_normalize_target_path_inplace(tmp_path):
    root = tmp_path
    primary = root / "src" / "main.py"
    primary.parent.mkdir(parents=True)
    primary.write_text("print(1)\n")
    t = normalize_target_path("main.py", root, primary, allow_new=False)
    assert t == primary

def test_normalize_target_path_existing_other_file(tmp_path):
    root = tmp_path
    primary = root / "src" / "main.py"
    primary.parent.mkdir(parents=True)
    primary.write_text("print(1)\n")
    other = root / "src" / "util.py"
    other.write_text("# util\n")
    t = normalize_target_path("util.py", root, primary, allow_new=False)
    assert t == other

def test_normalize_target_path_new_when_allowed(tmp_path):
    root = tmp_path
    primary = root / "src" / "main.py"
    primary.parent.mkdir(parents=True)
    primary.write_text("print(1)\n")
    t = normalize_target_path("newfile.py", root, primary, allow_new=True)
    assert t == (root / "newfile.py").resolve()

def test_normalize_target_path_outside_root(tmp_path):
    root = tmp_path
    primary = root / "main.py"
    primary.write_text("print(1)\n")
    t = normalize_target_path("/etc/passwd", root, primary, allow_new=True)
    assert t is None
