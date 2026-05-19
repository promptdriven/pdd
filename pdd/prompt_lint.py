# pylint: disable=duplicate-code
"""
Prompt and user-story lint engine.

Detects vague/ambiguous terms in <contract_rules>, <requirements>,
<acceptance_tests>, and user-story acceptance criteria. Optionally runs an
LLM pass to suggest vocabulary definitions.

Public API
----------
scan_prompt(path, *, strict=False) -> LintResult
scan_stories(stories_dir, *, strict=False) -> list[LintResult]
apply_suggestions(path, issues) -> int
append_vocabulary_definitions(path, suggestions) -> int
run_llm_ambiguity_pass(path, strength, temperature, time, verbose) -> list[LintIssue]
run_llm_guidance_pass(path, strength, temperature, time, verbose) -> dict
"""
from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Vocabulary of known vague terms
# ---------------------------------------------------------------------------

# Core vague terms: genuinely ambiguous in behavioral contracts; always checked.
VAGUE_TERMS: frozenset[str] = frozenset({
    "valid",
    "invalid",
    "safe",
    "unsafe",
    "active",
    "inactive",
    "recent",
    "duplicate",
    "graceful",
    "reasonable",
    "authorized",
    "unauthorized",
    "trusted",
    "untrusted",
    "complete",
    "successful",
})

# Extended vague terms: common English words that are only meaningfully ambiguous
# in tightly scoped contract text.  Only checked in --strict mode to avoid noise
# in LLM instruction prompts and general requirements prose.
VAGUE_TERMS_STRICT: frozenset[str] = frozenset({
    "incomplete",
    "proper",
    "correct",
    "incorrect",
    "appropriate",
    "normal",
    "expected",
    "unexpected",
    "sufficient",
    "necessary",
})

# Verbs that signal an observable, measurable outcome
OBSERVABLE_VERBS: frozenset[str] = frozenset({
    "return", "returns", "returned",
    "raise", "raises", "raised",
    "write", "writes", "wrote",
    "emit", "emits", "emitted",
    "log", "logs", "logged",
    "exit", "exits", "exited",
    "reject", "rejects", "rejected",
    "produce", "produces", "produced",
    "store", "stores", "stored",
    "increment", "increments", "incremented",
    "decrement", "decrements", "decremented",
    "set", "sets",
    "clear", "clears", "cleared",
    "yield", "yields", "yielded",
    "throw", "throws", "threw",
    "save", "saves", "saved",
    "delete", "deletes", "deleted",
    "output", "outputs", "outputted",
    "append", "appends", "appended",
    "insert", "inserts", "inserted",
    "update", "updates", "updated",
    "remove", "removes", "removed",
    "send", "sends", "sent",
    "publish", "publishes", "published",
})

# Pre-compiled patterns: core terms (always) and extended terms (--strict only)
_VAGUE_PATTERN = re.compile(
    r"\b(" + "|".join(re.escape(t) for t in sorted(VAGUE_TERMS)) + r")\b",
    re.IGNORECASE,
)
_VAGUE_PATTERN_STRICT = re.compile(
    r"\b(" + "|".join(re.escape(t) for t in sorted(VAGUE_TERMS | VAGUE_TERMS_STRICT)) + r")\b",
    re.IGNORECASE,
)

# Observable-outcome verb pattern
_OBSERVABLE_PATTERN = re.compile(
    r"\b(" + "|".join(re.escape(v) for v in sorted(OBSERVABLE_VERBS)) + r")\b",
    re.IGNORECASE,
)

# XML-style section extractor: captures content between <tag> … </tag>
_XML_SECTION_RE = re.compile(
    r"<(?P<tag>[a-z_][a-z0-9_]*)>(?P<body>.*?)</(?P=tag)>",
    re.IGNORECASE | re.DOTALL,
)

# Markdown heading (up to ###)
_MD_HEADING_RE = re.compile(r"^(#{1,3})\s+(.+)$", re.MULTILINE)


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class LintIssue:
    """A single lint finding."""

    level: str                                          # "warn" or "error"
    term: str                                           # matched vague term
    section: str                                        # section where found
    line: str                                           # original line text
    message: str                                        # human-readable description
    suggestion: str = ""                                # proposed <vocabulary> entry
    interpretations: list[str] = field(default_factory=list)  # LLM-sourced readings

    def as_dict(self) -> dict:
        """Serialise this issue to a JSON-safe dictionary."""
        return {
            "level": self.level,
            "term": self.term,
            "section": self.section,
            "line": self.line,
            "message": self.message,
            "suggestion": self.suggestion,
            "interpretations": self.interpretations,
        }


@dataclass
class LintResult:
    """Aggregated lint findings for one file."""

    path: Path
    issues: list[LintIssue] = field(default_factory=list)

    @property
    def warn_count(self) -> int:
        """Count of warning-level issues."""
        return sum(1 for i in self.issues if i.level == "warn")

    @property
    def error_count(self) -> int:
        """Count of error-level issues."""
        return sum(1 for i in self.issues if i.level == "error")

    def as_dict(self) -> dict:
        """Serialise this result to a JSON-safe dictionary."""
        return {
            "path": str(self.path),
            "warn_count": self.warn_count,
            "error_count": self.error_count,
            "issues": [i.as_dict() for i in self.issues],
        }


# ---------------------------------------------------------------------------
# Section extraction helpers
# ---------------------------------------------------------------------------

def _extract_xml_sections(text: str) -> dict[str, str]:
    """Return tag-name → inner text for all XML-style sections found."""
    sections: dict[str, str] = {}
    for section_match in _XML_SECTION_RE.finditer(text):
        tag = section_match.group("tag").lower()
        body = section_match.group("body")
        # Last occurrence wins for duplicate tags
        sections[tag] = body
    return sections


def _extract_markdown_sections(text: str) -> dict[str, str]:
    """Return lowered-heading → body for all markdown ## / ### headings."""
    headings = list(_MD_HEADING_RE.finditer(text))
    sections: dict[str, str] = {}
    for idx, match in enumerate(headings):
        heading_text = match.group(2).strip().lower()
        start = match.end()
        end = headings[idx + 1].start() if idx + 1 < len(headings) else len(text)
        sections[heading_text] = text[start:end].strip()
    return sections


def _extract_prose_lines(text: str) -> str:
    """Return text from lines that use the PDD % comment convention."""
    return "\n".join(
        line.lstrip()[1:].strip()
        for line in text.splitlines()
        if line.lstrip().startswith("%")
    )


def _extract_sections(text: str) -> dict[str, str]:
    """
    Extract all scannable sections from prompt or story text.

    Recognised section names (keys in returned dict):
      contract_rules, requirements, acceptance_tests, vocabulary  (XML tags)
      acceptance criteria, glossary, definitions, covers          (Markdown headings)
      prose                                                        (% lines)
    """
    sections: dict[str, str] = {}
    sections.update(_extract_xml_sections(text))
    sections.update(_extract_markdown_sections(text))
    prose = _extract_prose_lines(text)
    if prose:
        sections["prose"] = prose
    return sections


_SCANNABLE_SECTIONS: frozenset[str] = frozenset({
    "contract_rules",
    "requirements",
    "acceptance_tests",
    "acceptance criteria",
    "prose",
})

# Architecture metadata and structural sections whose content is NOT contract text
# and must never be scanned for vague terms.
_NON_SCANNABLE_SECTIONS: frozenset[str] = frozenset({
    "pdd-reason",
    "pdd-interface",
    "pdd-dependency",
    "waivers",
    "deliverables",
    "dependencies",
})

_VOCABULARY_SECTIONS: frozenset[str] = frozenset({
    "vocabulary",
    "glossary",
    "definitions",
    "covers",
})

# Sections where we additionally check for observable-outcome verbs
_OBSERVABLE_CHECK_SECTIONS: frozenset[str] = frozenset({
    "contract_rules",
    "acceptance_tests",
    "acceptance criteria",
})


def _extract_vocabulary_terms(vocab_text: str) -> set[str]:
    """
    Extract defined term names from a vocabulary/glossary/covers block.

    Heuristic: a line whose leading token (after optional bullet) is followed
    by `:` or ` - ` is treated as a definition. Both the full phrase AND each
    individual word in the phrase are added as known terms, so that "valid
    response" in vocabulary suppresses the warning for the word "valid".

    Also handles the cross-module ## Covers format:
        - prompts/payment_python.prompt#R3: No provider call before validation
    The descriptive text after the colon is treated as a known term phrase.
    """
    terms: set[str] = set()
    for line in vocab_text.splitlines():
        stripped = line.strip()

        # Cross-module Covers: - prompts/foo.prompt#R3: term phrase
        cross = re.match(
            r"^[-*]?\s*[\w./\-]+\.prompt#[A-Za-z0-9\-]+\s*:\s*(.+)$",
            stripped,
        )
        if cross:
            phrase = cross.group(1).strip().lower()
            terms.add(phrase)
            for word in re.split(r"[\s_-]+", phrase):
                if word:
                    terms.add(word)
            continue

        # Standard: "term: ..." or "- term: ..." or "* term: ..." or "term - ..."
        term_match = re.match(
            r"^[-*]?\s*([A-Za-z][A-Za-z0-9 _-]*?)\s*(?::\s|\s+-\s)",
            stripped,
        )
        if term_match:
            phrase = term_match.group(1).strip().lower()
            terms.add(phrase)
            # Also add each individual word so "valid response" covers "valid"
            for word in re.split(r"[\s_-]+", phrase):
                if word:
                    terms.add(word)
    return terms


# ---------------------------------------------------------------------------
# Core scan logic
# ---------------------------------------------------------------------------

def _scan_section(
    section_name: str,
    section_text: str,
    vocab_terms: set[str],
    *,
    strict: bool,
    check_observable: bool,
) -> list[LintIssue]:
    """Scan one section for vague terms and (optionally) observable-outcome gaps."""
    issues: list[LintIssue] = []
    pattern = _VAGUE_PATTERN_STRICT if strict else _VAGUE_PATTERN
    for line in section_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue

        # Strip angle-bracket placeholder tokens (e.g. <expected outcome>, <role>)
        # before scanning so template scaffolds don't produce false positives.
        scan_text = re.sub(r"<[^>]+>", "", stripped)

        matched_terms = {m.lower() for m in pattern.findall(scan_text)}
        undefined_terms = matched_terms - vocab_terms

        for term in sorted(undefined_terms):
            level = "error" if strict else "warn"
            issues.append(LintIssue(
                level=level,
                term=term,
                section=section_name,
                line=stripped,
                message=(
                    f'Vague term "{term}" used in [{section_name}] without a '
                    f"<vocabulary> definition."
                ),
                suggestion=f"{term}: <add a precise, observable definition here>",
            ))

        # Observable-outcome check: only fires when at least one vague term on
        # this line is UNDEFINED (not already covered by the vocabulary).
        if check_observable and undefined_terms and not _OBSERVABLE_PATTERN.search(scan_text):
            level = "error" if strict else "warn"
            issues.append(LintIssue(
                level=level,
                term="(no observable outcome)",
                section=section_name,
                line=stripped,
                message=(
                    "Rule or criterion contains a vague term but no observable "
                    "outcome verb (returns/raises/writes/emits/rejects/…)."
                ),
            ))

    return issues


def scan_prompt(path: Path, *, strict: bool = False) -> LintResult:
    """
    Deterministic lint scan of a single prompt file.

    Prompts with no recognised sections produce zero issues (legacy safety
    guarantee). Pass strict=True to escalate all warnings to errors.
    """
    result = LintResult(path=path)
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        result.issues.append(LintIssue(
            level="error",
            term="",
            section="file",
            line="",
            message=f"Cannot read file: {exc}",
        ))
        return result

    sections = _extract_sections(text)

    # Collect vocabulary terms from all vocabulary-source sections
    vocab_terms: set[str] = set()
    for vocab_key in _VOCABULARY_SECTIONS:
        if vocab_key in sections:
            vocab_terms |= _extract_vocabulary_terms(sections[vocab_key])

    # Prose (% lines) is only meaningful contract text when the file also has at
    # least one structured contract section.  Without this gate, LLM instruction
    # prompts that use % for their body text produce hundreds of false positives.
    contract_sections = frozenset({
        "contract_rules", "requirements", "acceptance_tests", "acceptance criteria"
    })
    has_contract_section = any(k in sections for k in contract_sections)

    # Scan recognised content sections only (skip architecture metadata)
    found_any_section = False
    for section_name, section_text in sections.items():
        if section_name in _NON_SCANNABLE_SECTIONS:
            continue
        if section_name not in _SCANNABLE_SECTIONS:
            continue
        if section_name == "prose" and not has_contract_section:
            continue
        found_any_section = True
        result.issues.extend(
            _scan_section(
                section_name,
                section_text,
                vocab_terms,
                strict=strict,
                check_observable=(section_name in _OBSERVABLE_CHECK_SECTIONS),
            )
        )

    if not found_any_section:
        logger.debug("prompt_lint: no recognised sections in %s — skipping", path)

    return result


def scan_stories(stories_dir: Path, *, strict: bool = False) -> list[LintResult]:
    """
    Scan all story__*.md files under stories_dir for vague acceptance criteria.

    Each story's ## Glossary / ## Definitions / ## Covers section supplies
    the vocabulary. Missing sections produce zero issues.
    """
    if not stories_dir.is_dir():
        return []
    return [
        scan_prompt(story_path, strict=strict)
        for story_path in sorted(stories_dir.rglob("story__*.md"))
    ]


# ---------------------------------------------------------------------------
# Apply suggestions (--apply write-back)
# ---------------------------------------------------------------------------

_VOCABULARY_OPEN = "<vocabulary>"
_VOCABULARY_CLOSE = "</vocabulary>"


def apply_suggestions(path: Path, issues: list[LintIssue]) -> int:
    """
    Append non-placeholder suggestion strings to the prompt's <vocabulary> block.

    Creates the block at the end of the file if absent.
    Returns the number of new entries written.
    Never called unless the caller explicitly passes --apply.
    """
    suggestions = [
        i.suggestion
        for i in issues
        if i.suggestion and "<add a precise" not in i.suggestion
    ]
    if not suggestions:
        return 0

    return append_vocabulary_definitions(path, suggestions)


def append_vocabulary_definitions(path: Path, suggestions: list[str]) -> int:
    """
    Append concrete vocabulary definitions to a prompt file.

    Creates a <vocabulary> block when absent. Duplicate definition lines are
    skipped. Returns the number of new entries written.
    """
    cleaned = [s.strip().lstrip("- ").strip() for s in suggestions if s.strip()]
    if not cleaned:
        return 0

    text = path.read_text(encoding="utf-8")
    existing = set()
    sections = _extract_sections(text)
    if "vocabulary" in sections:
        for line in sections["vocabulary"].splitlines():
            stripped = line.strip().lstrip("- ").strip()
            if stripped:
                existing.add(stripped)

    new_suggestions = [s for s in cleaned if s not in existing]
    if not new_suggestions:
        return 0

    new_entries = "\n".join(f"- {s}" for s in new_suggestions)

    if _VOCABULARY_OPEN in text and _VOCABULARY_CLOSE in text:
        text = text.replace(
            _VOCABULARY_CLOSE,
            f"{new_entries}\n{_VOCABULARY_CLOSE}",
        )
    else:
        text = text.rstrip() + (
            f"\n\n{_VOCABULARY_OPEN}\n{new_entries}\n{_VOCABULARY_CLOSE}\n"
        )

    path.write_text(text, encoding="utf-8")
    return len(new_suggestions)


# ---------------------------------------------------------------------------
# Optional LLM ambiguity pass
# ---------------------------------------------------------------------------

def run_llm_ambiguity_pass(  # pylint: disable=too-many-locals
    path: Path,
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = None,
    verbose: bool = False,
) -> list[LintIssue]:
    """
    Run the LLM-backed ambiguity analysis for a single prompt file.

    Loads pdd/prompts/prompt_lint_LLM.prompt, calls llm_invoke, and parses the
    JSON response into LintIssue entries (level="warn").

    Safe to call: always returns [] on any error so CI never breaks on LLM failure.
    """
    try:
        from .llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel
        from .preprocess import preprocess  # pylint: disable=import-outside-toplevel

        template_path = Path(__file__).parent / "prompts" / "prompt_lint_LLM.prompt"
        if not template_path.exists():
            logger.warning("prompt_lint_LLM.prompt not found; skipping LLM pass")
            return []

        prompt_content = path.read_text(encoding="utf-8", errors="replace")
        vague_terms_list = ", ".join(sorted(VAGUE_TERMS))

        template = template_path.read_text(encoding="utf-8")
        filled = template.replace("{prompt_content}", prompt_content).replace(
            "{vague_terms_list}", vague_terms_list
        )
        filled = preprocess(filled, recursive=False, double_curly_brackets=False)

        result = llm_invoke(
            messages=[{"role": "user", "content": filled}],
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            use_cloud=False,
        )
        response_text = result["result"]

        # Strip optional markdown code fences
        json_match = re.search(r"```(?:json)?\s*(\[.*?\])\s*```", response_text, re.DOTALL)
        raw_json = json_match.group(1) if json_match else response_text.strip()
        items = json.loads(raw_json)

        issues: list[LintIssue] = []
        for item in items:
            if not isinstance(item, dict):
                continue
            issues.append(LintIssue(
                level="warn",
                term=str(item.get("term", "")),
                section=str(item.get("section", "llm")),
                line="",
                message=f'LLM flagged "{item.get("term", "")}" as potentially ambiguous.',
                suggestion=str(item.get("suggestion", "")),
                interpretations=[str(x) for x in item.get("interpretations", [])],
            ))
        return issues

    except Exception as exc:  # noqa: BLE001  # pylint: disable=broad-exception-caught
        logger.warning("prompt_lint LLM pass failed: %s", exc)
        return []


def run_llm_guidance_pass(  # pylint: disable=too-many-locals
    path: Path,
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = None,
    verbose: bool = False,
) -> dict:
    """
    Run the LLM-backed prompt coaching pass for one prompt file.

    This is advisory author guidance, not a CI gate. It returns a structured
    dictionary with vocabulary suggestions, rule rewrites, acceptance-criteria
    improvements, and formalization notes. Failures return an error payload
    rather than raising.
    """
    try:
        from .llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel
        from .preprocess import preprocess  # pylint: disable=import-outside-toplevel

        template_path = Path(__file__).parent / "prompts" / "prompt_guidance_LLM.prompt"
        if not template_path.exists():
            return _empty_guidance(path, "prompt_guidance_LLM.prompt not found")

        prompt_content = path.read_text(encoding="utf-8", errors="replace")
        vague_terms_list = ", ".join(sorted(VAGUE_TERMS | VAGUE_TERMS_STRICT))

        template = template_path.read_text(encoding="utf-8")
        filled = template.replace("{prompt_content}", prompt_content).replace(
            "{vague_terms_list}", vague_terms_list
        )
        filled = preprocess(filled, recursive=False, double_curly_brackets=False)

        result = llm_invoke(
            messages=[{"role": "user", "content": filled}],
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            use_cloud=False,
        )
        response_text = result["result"]
        json_match = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", response_text, re.DOTALL)
        raw_json = json_match.group(1) if json_match else response_text.strip()
        parsed = json.loads(raw_json)
        if not isinstance(parsed, dict):
            return _empty_guidance(path, "LLM guidance response was not a JSON object")
        return _normalize_guidance(path, parsed)

    except Exception as exc:  # noqa: BLE001  # pylint: disable=broad-exception-caught
        logger.warning("prompt guidance LLM pass failed: %s", exc)
        return _empty_guidance(path, str(exc))


def _empty_guidance(path: Path, error: str = "") -> dict:
    """Return an empty guidance payload."""
    return {
        "path": str(path),
        "summary": "",
        "vocabulary_suggestions": [],
        "rule_rewrites": [],
        "acceptance_criteria_improvements": [],
        "formalization_notes": [],
        "error": error,
    }


def _normalize_guidance(path: Path, payload: dict) -> dict:
    """Normalize an LLM guidance response into the public schema."""
    result = _empty_guidance(path)
    result["summary"] = str(payload.get("summary", ""))
    for key in (
        "vocabulary_suggestions",
        "rule_rewrites",
        "acceptance_criteria_improvements",
        "formalization_notes",
    ):
        value = payload.get(key, [])
        result[key] = value if isinstance(value, list) else []
    if payload.get("error"):
        result["error"] = str(payload["error"])
    return result
