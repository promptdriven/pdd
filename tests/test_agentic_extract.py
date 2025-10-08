from pathlib import Path
from pdd.agentic_extract import (
    extract_files_from_output,
    extract_corrected_single,
    normalize_code_text,
)

def test_extract_multi_blocks():
    blob = (
        "<<<BEGIN_FILE:a.py>>>print(1)\n<<<END_FILE:a.py>>>\n"
        "<<<BEGIN_FILE:b.py>>>print(2)\n<<<END_FILE:b.py>>>"
    )
    out = extract_files_from_output(blob)
    assert out["a.py"].startswith("print(1)")
    assert out["b.py"].startswith("print(2)")

def test_extract_single_prefers_exact_path(tmp_path):
    p = tmp_path / "x.py"
    p.write_text("pass\n")
    stdout = f"<<<BEGIN_FILE:{p}>>>print(3)\n<<<END_FILE:{p}>>>"
    body = extract_corrected_single(stdout, "", p)
    assert "print(3)" in body

def test_normalize_code_text():
    assert normalize_code_text("x\n") == "x\n"
    assert normalize_code_text("\nx") == "x\n"
