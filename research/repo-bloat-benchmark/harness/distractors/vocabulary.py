"""Vocabulary harvesting from the scenario core (design.md §5.0.1).

`mutate` and `template` modes must produce files in the project's own
vocabulary (definition condition 3). This module extracts that vocabulary
deterministically from the core's Python sources: identifiers, their word
pieces, and frequency ranks.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

_CAMEL = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
_NON_WORD = re.compile(r"[^A-Za-z]+")

# Words too generic to characterize a project's vocabulary.
_STOPWORDS = frozenset(
    "the a an and or of in to for is not none true false self cls def return "
    "get set is has add new init main test data value item items key keys "
    "args kwargs obj result results".split()
)


def split_identifier(identifier: str) -> list[str]:
    """``formatLedgerTotals`` / ``format_ledger_totals`` → [format, ledger, totals]."""
    words: list[str] = []
    for chunk in _NON_WORD.split(identifier):
        for piece in _CAMEL.sub(" ", chunk).split():
            piece = piece.lower()
            if len(piece) >= 3 and piece not in _STOPWORDS:
                words.append(piece)
    return words


@dataclass
class Vocabulary:
    """Deterministic core vocabulary: identifiers and their word pieces."""

    identifiers: dict[str, int] = field(default_factory=dict)
    words: dict[str, int] = field(default_factory=dict)

    def top_words(self, n: int) -> list[str]:
        return [
            w
            for w, _ in sorted(self.words.items(), key=lambda kv: (-kv[1], kv[0]))[:n]
        ]

    def overlap_fraction(self, candidate_identifiers: Iterable[str]) -> float:
        """Fraction of the candidate's word pieces that appear in this vocabulary."""
        pieces: list[str] = []
        for identifier in candidate_identifiers:
            pieces.extend(split_identifier(identifier))
        if not pieces:
            return 0.0
        hits = sum(1 for piece in pieces if piece in self.words)
        return hits / len(pieces)


class _IdentifierCollector(ast.NodeVisitor):
    def __init__(self) -> None:
        self.identifiers: list[str] = []

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # noqa: N802
        self.identifiers.append(node.name)
        self.generic_visit(node)

    visit_AsyncFunctionDef = visit_FunctionDef  # type: ignore[assignment]

    def visit_ClassDef(self, node: ast.ClassDef) -> None:  # noqa: N802
        self.identifiers.append(node.name)
        self.generic_visit(node)

    def visit_Name(self, node: ast.Name) -> None:  # noqa: N802
        self.identifiers.append(node.id)

    def visit_Attribute(self, node: ast.Attribute) -> None:  # noqa: N802
        self.identifiers.append(node.attr)
        self.generic_visit(node)

    def visit_arg(self, node: ast.arg) -> None:  # noqa: N802
        self.identifiers.append(node.arg)


def collect_identifiers(source: str) -> list[str]:
    """All identifiers in a Python source (empty list if unparseable)."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    collector = _IdentifierCollector()
    collector.visit(tree)
    return collector.identifiers


def harvest_vocabulary(core_root: str | Path) -> Vocabulary:
    """Harvest the deterministic vocabulary of a core tree (Python files)."""
    vocabulary = Vocabulary()
    for path in sorted(Path(core_root).rglob("*.py")):
        try:
            source = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for identifier in collect_identifiers(source):
            vocabulary.identifiers[identifier] = (
                vocabulary.identifiers.get(identifier, 0) + 1
            )
            for word in split_identifier(identifier):
                vocabulary.words[word] = vocabulary.words.get(word, 0) + 1
    return vocabulary
