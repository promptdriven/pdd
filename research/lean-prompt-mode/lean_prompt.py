"""
Lean PDD prompt mode research harness.

Deterministically prunes non-essential sections from PDD prompt files while
preserving the five required field groups:
  1. Source-truth content  (<contract_rules>, <vocabulary>, <responsibility>, ...)
  2. Output files          (<output_files>, allowed-path declarations)
  3. Verifier command      (<verifier>, test runner specification)
  4. Output delimiters     (machine-parseable begin/end tags)
  5. Safety constraints    (MUST NOT capability rules, <capabilities> block)

Emits two JSON audit artifacts:
  - prompt_policy.json       — pruning decisions and source hashes
  - prompt_token_audit.json  — per-task and aggregate token counts

Usage:
    python lean_prompt.py --mode lean prompts/your_module.prompt
    python lean_prompt.py --mode current prompts/your_module.prompt
    python lean_prompt.py --mode lean --out-dir /tmp/audit prompts/foo.prompt
    python lean_prompt.py --mode lean --model claude-sonnet-4-20250514 prompts/foo.prompt
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Token counting — use pdd/server/token_counter.py when available on sys.path
# ---------------------------------------------------------------------------

def _find_repo_root() -> Optional[Path]:
    """Walk up from this file to find the repo root (contains pdd/ package)."""
    here = Path(__file__).resolve().parent
    for candidate in [here, *here.parents]:
        if (candidate / "pdd" / "server" / "token_counter.py").exists():
            return candidate
    return None


_repo_root = _find_repo_root()
if _repo_root is not None and str(_repo_root) not in sys.path:
    sys.path.insert(0, str(_repo_root))

try:
    from pdd.server.token_counter import count_tokens as _pdd_count_tokens
    _TOKENIZER_SOURCE = "litellm/cl100k_base"
    _APPROXIMATION = True

    def _count_tokens(text: str, model: str) -> int:
        return _pdd_count_tokens(text, model)

except ImportError:
    # Pure tiktoken fallback when running outside the PDD repo
    try:
        import tiktoken
        _enc = tiktoken.get_encoding("cl100k_base")
        _TOKENIZER_SOURCE = "tiktoken/cl100k_base"
        _APPROXIMATION = True

        def _count_tokens(text: str, model: str) -> int:  # type: ignore[misc]
            return len(_enc.encode(text))

    except ImportError:
        _TOKENIZER_SOURCE = "char_approx/4"
        _APPROXIMATION = True

        def _count_tokens(text: str, model: str) -> int:  # type: ignore[misc]
            # Very rough approximation: 1 token ≈ 4 chars
            return max(1, len(text) // 4)


# ---------------------------------------------------------------------------
# Section classification
# ---------------------------------------------------------------------------

# Required XML tag names — sections whose content matches these are NEVER removed.
_REQUIRED_XML_TAGS = frozenset({
    "contract_rules",
    "vocabulary",
    "responsibility",
    "non_responsibilities",
    "capabilities",
    "output_files",
    "verifier",
    "pdd-reason",
    "pdd-interface",
    "pdd-dependency",
})

# Required marker patterns that, if found inside a candidate section, cause it
# to be preserved (contamination check).
_REQUIRED_CONTENT_PATTERNS = [
    re.compile(r"MUST NOT", re.IGNORECASE),
    re.compile(r"<contract_rules>", re.IGNORECASE),
    re.compile(r"<vocabulary>", re.IGNORECASE),
    re.compile(r"<responsibility>", re.IGNORECASE),
    re.compile(r"<non_responsibilities>", re.IGNORECASE),
    re.compile(r"<capabilities>", re.IGNORECASE),
    re.compile(r"<output_files>", re.IGNORECASE),
    re.compile(r"<verifier>", re.IGNORECASE),
    re.compile(r"<pdd-reason>", re.IGNORECASE),
    re.compile(r"<pdd-interface>", re.IGNORECASE),
    re.compile(r"<pdd-dependency>", re.IGNORECASE),
    re.compile(r"^% Requirements", re.MULTILINE | re.IGNORECASE),
    re.compile(r"^% Deliverables", re.MULTILINE | re.IGNORECASE),
]

# Removable %-section headings (case-insensitive prefix match after "% ")
_REMOVABLE_PCT_SECTIONS = {
    "role & scope": "workflow_narrative",
    "role and scope": "workflow_narrative",
    "role": "workflow_narrative",
    "background": "explanatory_boilerplate",
    "context": "explanatory_boilerplate",
    "overview": "explanatory_boilerplate",
    "instructions": "workflow_narrative",
    "steps": "workflow_narrative",
}

# <include> for shared preamble files is removable boilerplate
_PREAMBLE_INCLUDE_RE = re.compile(
    r'<include>[^<]*preamble[^<]*</include>', re.IGNORECASE
)


@dataclass
class Section:
    """Parsed section of a PDD prompt."""
    section_id: str
    content: str
    required: bool
    removal_reason: Optional[str] = None  # set when required=False

    def is_contaminated(self) -> bool:
        """Return True if this section contains required-field markers."""
        for pat in _REQUIRED_CONTENT_PATTERNS:
            if pat.search(self.content):
                return True
        return False


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _parse_sections(prompt_text: str) -> list[Section]:
    """
    Split prompt text into named sections.

    Two conventions are handled:
    1. %-prefixed comment-style headings:  % Role & Scope
    2. XML tag blocks:                     <contract_rules>...</contract_rules>

    Sections are returned in order of appearance.
    """
    sections: list[Section] = []
    remaining = prompt_text

    # We process the text linearly, extracting XML blocks first as anchors,
    # then splitting remaining prose by %-heading boundaries.

    # Regex to match a top-level XML block (non-nested for simplicity)
    xml_block_re = re.compile(
        r'(<(?P<tag>[a-zA-Z][a-zA-Z0-9_-]*)(?:\s[^>]*)?>.*?</(?P=tag)>)',
        re.DOTALL,
    )

    # Split on XML blocks, keeping the blocks
    parts = xml_block_re.split(remaining)
    # xml_block_re.split produces: [text, full_match, tag_name, text, ...]
    # We need to re-join properly using finditer instead.
    sections = _parse_sections_impl(prompt_text)
    return sections


def _parse_sections_impl(prompt_text: str) -> list[Section]:
    """Implementation: iterate through prompt extracting sections."""
    sections: list[Section] = []

    # Find all XML block spans
    xml_block_re = re.compile(
        r'<(?P<tag>[a-zA-Z][a-zA-Z0-9_-]*)(?:\s[^>]*)?>.*?</(?P=tag)>',
        re.DOTALL,
    )

    # Find all %-heading spans (lines starting with "% <Word>")
    pct_heading_re = re.compile(r'^% .+', re.MULTILINE)

    pos = 0
    length = len(prompt_text)
    used_ids: dict[str, int] = {}

    def _make_id(base: str) -> str:
        base = re.sub(r'[^a-z0-9]+', '_', base.lower()).strip('_')
        n = used_ids.get(base, 0)
        used_ids[base] = n + 1
        return base if n == 0 else f"{base}_{n}"

    def _flush_prose(prose: str, section_id: str) -> None:
        """Add a prose section, checking for preamble includes."""
        if not prose.strip():
            return
        # Check for preamble include line
        if _PREAMBLE_INCLUDE_RE.search(prose):
            # Split off the preamble include as its own removable section
            lines = prose.split('\n')
            buffer = []
            for line in lines:
                if _PREAMBLE_INCLUDE_RE.search(line):
                    if buffer:
                        s_id = _make_id(section_id + "_pre")
                        sections.append(Section(
                            section_id=s_id,
                            content='\n'.join(buffer),
                            required=True,
                        ))
                        buffer = []
                    inc_id = _make_id("include_preamble")
                    sections.append(Section(
                        section_id=inc_id,
                        content=line,
                        required=False,
                        removal_reason="shared_preamble_boilerplate",
                    ))
                else:
                    buffer.append(line)
            if buffer:
                s_id = _make_id(section_id + "_post")
                _add_prose_section('\n'.join(buffer), s_id)
        else:
            _add_prose_section(prose, section_id)

    def _add_prose_section(prose: str, section_id: str) -> None:
        """Parse prose for %-headings and add sub-sections."""
        # Find %-heading boundaries
        pct_matches = list(pct_heading_re.finditer(prose))
        if not pct_matches:
            if prose.strip():
                sections.append(Section(
                    section_id=_make_id(section_id),
                    content=prose,
                    required=True,
                ))
            return

        # Text before first heading
        pre = prose[:pct_matches[0].start()]
        if pre.strip():
            sections.append(Section(
                section_id=_make_id("preamble_text"),
                content=pre,
                required=True,
            ))

        for i, match in enumerate(pct_matches):
            heading = match.group(0)
            heading_text = heading[2:].strip()  # strip "% "
            start = match.end()
            end = pct_matches[i + 1].start() if i + 1 < len(pct_matches) else len(prose)
            body = prose[start:end]
            full_content = heading + body

            # Classify the section
            heading_lower = heading_text.lower()
            removal_reason = _REMOVABLE_PCT_SECTIONS.get(heading_lower)
            s_id = _make_id("pct_" + re.sub(r'[^a-z0-9]+', '_', heading_lower))

            if removal_reason:
                sec = Section(
                    section_id=s_id,
                    content=full_content,
                    required=False,
                    removal_reason=removal_reason,
                )
                # Contamination check
                if sec.is_contaminated():
                    sec.required = True
                    sec.removal_reason = None
            else:
                sec = Section(
                    section_id=s_id,
                    content=full_content,
                    required=True,
                )
            sections.append(sec)

    # Main pass: walk through prompt, extracting XML blocks and prose
    prose_start = 0
    xml_iter = xml_block_re.finditer(prompt_text)

    for xml_match in xml_iter:
        # Flush prose before this XML block
        prose = prompt_text[prose_start:xml_match.start()]
        if prose.strip():
            _flush_prose(prose, "prose")

        tag = xml_match.group('tag')
        content = xml_match.group(0)
        s_id = _make_id(f"xml_{tag}")
        tag_norm = tag.lower().replace('-', '_')
        if tag_norm in {t.replace('-', '_') for t in _REQUIRED_XML_TAGS}:
            required = True
            removal_reason_xml = None
        elif tag.lower() == "include" and _PREAMBLE_INCLUDE_RE.search(content):
            # Preamble <include> is boilerplate we can drop
            required = False
            removal_reason_xml = "shared_preamble_boilerplate"
            s_id = _make_id("include_preamble")
        else:
            # Unknown XML tags are preserved by default
            required = True
            removal_reason_xml = None
        sections.append(Section(
            section_id=s_id,
            content=content,
            required=required,
            removal_reason=removal_reason_xml,
        ))
        prose_start = xml_match.end()

    # Flush remaining prose
    prose = prompt_text[prose_start:]
    if prose.strip():
        _flush_prose(prose, "prose_tail")

    return sections


# ---------------------------------------------------------------------------
# Pruner
# ---------------------------------------------------------------------------

@dataclass
class PruneResult:
    lean_text: str
    removed_sections: list[dict]
    preserved_contract_fields: list[str]


def _prune(sections: list[Section]) -> PruneResult:
    """Apply lean pruning policy to parsed sections."""
    kept: list[str] = []
    removed: list[dict] = []
    preserved_fields: set[str] = set()

    for sec in sections:
        if sec.required:
            kept.append(sec.content)
            # Record which contract field groups are present
            for tag in _REQUIRED_XML_TAGS:
                tag_norm = tag.replace('-', '_')
                if re.search(rf'<{re.escape(tag)}[\s>]', sec.content, re.IGNORECASE):
                    preserved_fields.add(tag_norm)
        else:
            removed.append({
                "section_id": sec.section_id,
                "reason": sec.removal_reason,
                "token_delta": 0,  # filled in later by caller
            })

    lean_text = '\n'.join(kept)
    return PruneResult(
        lean_text=lean_text,
        removed_sections=removed,
        preserved_contract_fields=sorted(preserved_fields),
    )


def _compute_structural_floor(sections: list[Section], model: str) -> int:
    """Compute minimum token count keeping only the five required field groups."""
    required_tags = _REQUIRED_XML_TAGS
    floor_parts: list[str] = []
    for sec in sections:
        for tag in required_tags:
            if re.search(rf'<{re.escape(tag)}[\s>]', sec.content, re.IGNORECASE):
                floor_parts.append(sec.content)
                break
    floor_text = '\n'.join(floor_parts)
    return _count_tokens(floor_text, model)


# ---------------------------------------------------------------------------
# Artifact emitters
# ---------------------------------------------------------------------------

def _emit_policy(
    mode: str,
    removed_sections: list[dict],
    preserved_contract_fields: list[str],
    source_path: Path,
    source_sha256: str,
    out_dir: Path,
) -> Path:
    policy = {
        "schema_version": "1.0",
        "mode": mode,
        "compression_method": "deterministic_section_pruning",
        "policy_version": "1.0",
        "removed_sections": removed_sections,
        "preserved_contract_fields": preserved_contract_fields,
        "source_inputs": [
            {
                "path": str(source_path),
                "sha256": source_sha256,
            }
        ],
    }
    out = out_dir / "prompt_policy.json"
    out.write_text(json.dumps(policy, indent=2), encoding="utf-8")
    return out


def _emit_audit(
    tokenizer: str,
    approximation: bool,
    model: str,
    task_id: str,
    current_tokens: int,
    lean_tokens: int,
    floor_tokens: int,
    out_dir: Path,
) -> Path:
    ratio = lean_tokens / current_tokens if current_tokens else 0.0
    floor_ratio = floor_tokens / current_tokens if current_tokens else 0.0
    audit = {
        "schema_version": "1.0",
        "tokenizer": tokenizer,
        "approximation": approximation,
        "model": model,
        "tasks": [
            {
                "task_id": task_id,
                "current_tokens": current_tokens,
                "lean_tokens": lean_tokens,
                "ratio": round(ratio, 6),
            }
        ],
        "aggregate": {
            "total_current_tokens": current_tokens,
            "total_lean_tokens": lean_tokens,
            "aggregate_ratio": round(ratio, 6),
            "structural_floor_tokens": floor_tokens,
            "structural_floor_ratio": round(floor_ratio, 6),
        },
    }
    out = out_dir / "prompt_token_audit.json"
    out.write_text(json.dumps(audit, indent=2), encoding="utf-8")
    return out


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Lean PDD prompt mode research harness.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "prompt_file",
        type=Path,
        help="Path to the PDD prompt file to process.",
    )
    parser.add_argument(
        "--mode",
        choices=["current", "lean"],
        default="current",
        help="Processing mode. 'current' (default) leaves the prompt unchanged; "
             "'lean' deterministically prunes non-essential sections.",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("."),
        help="Directory for output artifacts (default: current directory).",
    )
    parser.add_argument(
        "--model",
        default="claude-sonnet-4-20250514",
        help="Model name for token counting (default: claude-sonnet-4-20250514).",
    )
    return parser.parse_args(argv)


def run(
    prompt_file: Path,
    mode: str = "current",
    out_dir: Path = Path("."),
    model: str = "claude-sonnet-4-20250514",
) -> dict:
    """
    Run the lean prompt harness.

    Args:
        prompt_file: Path to the PDD prompt file.
        mode: 'current' or 'lean'.
        out_dir: Output directory for artifacts.
        model: Model name for token counting.

    Returns:
        Dict with keys: lean_text, policy_path, audit_path, audit.
    """
    prompt_text = prompt_file.read_text(encoding="utf-8")
    source_sha256 = _sha256(prompt_text)
    task_id = prompt_file.stem
    out_dir.mkdir(parents=True, exist_ok=True)

    current_tokens = _count_tokens(prompt_text, model)

    if mode == "current":
        lean_text = prompt_text
        removed_sections: list[dict] = []
        preserved_fields: list[str] = []
        lean_tokens = current_tokens
        floor_tokens = current_tokens
    else:
        sections = _parse_sections(prompt_text)
        result = _prune(sections)
        lean_text = result.lean_text
        lean_tokens = _count_tokens(lean_text, model)
        floor_tokens = _compute_structural_floor(sections, model)
        preserved_fields = result.preserved_contract_fields

        # Fill in token_delta for removed sections
        removed_sections = []
        for entry in result.removed_sections:
            # Approximate delta: sum up section token counts
            # We stored section content in PruneResult but not individually here;
            # use the section list to find the delta.
            removed_sections.append(entry)

        # Recompute token deltas from sections
        section_map = {
            sec.section_id: _count_tokens(sec.content, model)
            for sec in _parse_sections(prompt_text)
            if not sec.required
        }
        for entry in removed_sections:
            entry["token_delta"] = section_map.get(entry["section_id"], 0)

        # Anomaly: warn if lean >= current
        if lean_tokens >= current_tokens and current_tokens > 0:
            print(
                f"WARNING: lean_tokens ({lean_tokens}) >= current_tokens ({current_tokens}). "
                "No reduction achieved; check policy rules.",
                file=sys.stderr,
            )

    # Write lean prompt output
    lean_stem = prompt_file.stem
    lean_out = out_dir / f"{lean_stem}_lean.txt"
    lean_out.write_text(lean_text, encoding="utf-8")

    policy_path = _emit_policy(
        mode=mode,
        removed_sections=removed_sections,
        preserved_contract_fields=preserved_fields,
        source_path=prompt_file,
        source_sha256=source_sha256,
        out_dir=out_dir,
    )

    audit_path = _emit_audit(
        tokenizer=_TOKENIZER_SOURCE,
        approximation=_APPROXIMATION,
        model=model,
        task_id=task_id,
        current_tokens=current_tokens,
        lean_tokens=lean_tokens,
        floor_tokens=floor_tokens,
        out_dir=out_dir,
    )

    ratio = lean_tokens / current_tokens if current_tokens else 0.0
    audit = {
        "current_tokens": current_tokens,
        "lean_tokens": lean_tokens,
        "ratio": ratio,
        "structural_floor_tokens": floor_tokens,
    }

    return {
        "lean_text": lean_text,
        "lean_out": lean_out,
        "policy_path": policy_path,
        "audit_path": audit_path,
        "audit": audit,
    }


def main(argv: Optional[list[str]] = None) -> None:
    args = _parse_args(argv)
    result = run(
        prompt_file=args.prompt_file,
        mode=args.mode,
        out_dir=args.out_dir,
        model=args.model,
    )
    audit = result["audit"]
    print(
        f"mode={args.mode}  "
        f"current={audit['current_tokens']} tokens  "
        f"lean={audit['lean_tokens']} tokens  "
        f"ratio={audit['ratio']:.3f}  "
        f"floor={audit['structural_floor_tokens']} tokens"
    )
    print(f"lean prompt → {result['lean_out']}")
    print(f"policy      → {result['policy_path']}")
    print(f"audit       → {result['audit_path']}")


if __name__ == "__main__":
    main()
