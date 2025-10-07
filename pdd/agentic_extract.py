from __future__ import annotations
import re
from pathlib import Path
from typing import Dict, List, Optional

from .agentic_logging import print_head, verbose


# put near top, after imports/regexes
_BAD_BODY_PATTERNS = (
    "FULL CORRECTED FILE CONTENT HERE",
    "<begin_marker",  # model echoed your XML-ish control tags
    "</begin_marker",
    "<end_marker",
    "</end_marker",
)

_PLACEHOLDER_PATHS = {
    "/absolute/or/relative/path/to/file",  # template path that some models echo
}

def _is_bad_body(body: str) -> bool:
    b = (body or "").strip().lower()
    if not b:
        return True
    for pat in _BAD_BODY_PATTERNS:
        if pat.lower() in b:
            return True
    # Heuristic: reject tiny tag-only or obviously-not-source outputs
    if b in {"<begin_marker>", "</begin_marker>", "<end_marker>", "</end_marker>"}:
        return True
    return False



def begin_marker(path: Path) -> str:
    return f"<<<BEGIN_FILE:{path}>>>"

def end_marker(path: Path) -> str:
    return f"<<<END_FILE:{path}>>>"

def normalize_code_text(body: str) -> str:
    if body.startswith("\n"):
        body = body[1:]
    body = body.rstrip("\n") + "\n"
    return body

_MULTI_FILE_BLOCK_RE = re.compile(r"<<<BEGIN_FILE:(.*?)>>>(.*?)<<<END_FILE:\1>>>", re.DOTALL)
_CODE_FENCE_RE = re.compile(r"```(?:python)?\s*(.*?)```", re.DOTALL | re.IGNORECASE)

def extract_files_from_output(*blobs: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for blob in blobs:
        if not blob:
            continue
        for m in _MULTI_FILE_BLOCK_RE.finditer(blob):
            path = (m.group(1) or "").strip()
            body = m.group(2) or ""
            if not path or path in _PLACEHOLDER_PATHS:
                continue
            if _is_bad_body(body):
                continue
            out[path] = body
    return out


def extract_corrected_single(stdout: str, stderr: str, code_path: Path) -> Optional[str]:
    resolved = code_path.resolve()
    abs_path = str(resolved)
    real_path = str(Path(abs_path).resolve())
    rel_path = str(code_path)
    just_name = code_path.name

    def _pattern_for(path_str: str) -> re.Pattern:
        begin = re.escape(f"<<<BEGIN_FILE:{path_str}>>>")
        end = re.escape(f"<<<END_FILE:{path_str}>>>")
        return re.compile(begin + r"(.*?)" + end, re.DOTALL)

    candidates = [
        _pattern_for(abs_path),
        _pattern_for(real_path),
        _pattern_for(rel_path),
        _pattern_for(just_name),
    ]

    matches: List[str] = []
    for blob in [stdout or "", stderr or ""]:
        for pat in candidates:
            for m in pat.finditer(blob):
                body = m.group(1) or ""
                if body != "":
                    matches.append(body)

    if not matches:
        return None

    # Drop placeholders/junk; if all junk, return None (do NOT write)
    filtered = [b for b in matches if not _is_bad_body(b)]
    return filtered[-1] if filtered else None


def extract_python_code_block(*blobs: str) -> Optional[str]:
    candidates: List[str] = []
    for blob in blobs:
        if not blob:
            continue
        for match in _CODE_FENCE_RE.findall(blob):
            block = match or ""
            if block != "":
                candidates.append(block)
    if not candidates:
        return None
    block = candidates[-1]
    return block if block.endswith("\n") else (block + "\n")
