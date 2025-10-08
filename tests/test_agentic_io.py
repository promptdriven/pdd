from pathlib import Path
from pdd.agentic_io import apply_file_map

def test_apply_file_map_writes_files(tmp_path):
    root = tmp_path
    primary = root / "src" / "a.py"
    primary.parent.mkdir(parents=True)
    primary.write_text("print(1)\n")
    fmap = {
        str(primary): "print(2)\n",
        "src/b.py": "print('b')\n",
    }
    written = apply_file_map(
        fmap, root, primary, allow_new=True, normalizer=lambda s: s
    )
    assert (root / "src/b.py") in written
    assert primary.read_text() == "print(2)\n"
    assert (root / "src/b.py").read_text() == "print('b')\n"
