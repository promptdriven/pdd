"""Machine checks for the distractor-file definition (DEFINITION.md, design §5.0).

Every file the generator admits — whatever its mode — passes through
``DefinitionChecker.check``. A non-empty violation list rejects the file.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from pathlib import PurePosixPath
from typing import Iterable

# Condition 2: basenames with ambient side effects (test collection, import
# hooks, packaging) can change behavior by existing. Never admissible.
FORBIDDEN_BASENAMES = frozenset(
    {
        "conftest.py",
        "sitecustomize.py",
        "usercustomize.py",
        "setup.py",
        "setup.cfg",
        "pyproject.toml",
        "tox.ini",
        "pytest.ini",
        "__main__.py",
    }
)

# Condition 5: markers that would label a file as benchmark filler.
TELL_MARKERS = ("distractor", "filler", "synthetic", "decoy", "padding", "noise_file")

# Condition 2 red flags: constructs whose presence needs manual review because
# they can act at import/collection time even without being imported by core.
_DYNAMIC_RED_FLAGS = (
    re.compile(r"\bimportlib\.(?:import_module|reload)\b"),
    re.compile(r"\b__import__\s*\("),
    re.compile(r"\bsys\.path\.(?:insert|append)\b"),
    re.compile(r"\bpkg_resources\b"),
    re.compile(r"entry_points"),
)

_IMPORT_RE = re.compile(r"^\s*(?:from\s+([\w\.]+)\s+import|import\s+([\w\.]+))", re.M)


def module_names_for(path: str) -> set[str]:
    """Dotted-module candidates a Python file can be imported as.

    ``src/pkg/mod.py`` → {``src.pkg.mod``, ``pkg.mod``, ``mod``} — suffixes are
    included because the import root is unknown statically.
    """
    pure = PurePosixPath(path)
    if pure.suffix != ".py":
        return set()
    parts = list(pure.with_suffix("").parts)
    if parts and parts[-1] == "__init__":
        parts = parts[:-1]
    return {".".join(parts[i:]) for i in range(len(parts))} if parts else set()


def imported_modules(source: str) -> set[str]:
    """Statically imported dotted names (regex-based, comment-tolerant)."""
    names: set[str] = set()
    for match in _IMPORT_RE.finditer(source):
        name = match.group(1) or match.group(2)
        if name:
            names.add(name)
            # `import a.b.c` also makes `a` and `a.b` load.
            pieces = name.split(".")
            for i in range(1, len(pieces)):
                names.add(".".join(pieces[:i]))
    return names


@dataclass
class Violation:
    condition: int  # 1..5, per DEFINITION.md
    message: str

    def __str__(self) -> str:  # pragma: no cover - convenience
        return f"[condition {self.condition}] {self.message}"


@dataclass
class CandidateFile:
    """A file proposed for admission, before definition checks."""

    destination_path: str  # where it would be materialized (tree-relative)
    content: str
    mode: str  # regrow | mutate | template
    source_path: str | None = None  # provenance for regrow/mutate
    tier: str = "cross-cutting"


@dataclass
class DefinitionChecker:
    """Holds the scenario facts the checks are made against."""

    core_files: set[str]
    target_files: set[str]
    core_import_names: set[str]  # every module name any core file imports
    leak_denylist: tuple[str, ...] = ()
    vocabulary_floor: float = 0.02
    core_vocabulary: "object | None" = None  # Vocabulary; optional

    @classmethod
    def from_core(
        cls,
        core_files: Iterable[str],
        core_sources: dict[str, str],
        target_files: Iterable[str] = (),
        leak_denylist: Iterable[str] = (),
        vocabulary_floor: float = 0.02,
        core_vocabulary: "object | None" = None,
    ) -> "DefinitionChecker":
        import_names: set[str] = set()
        for source in core_sources.values():
            import_names |= imported_modules(source)
        return cls(
            core_files={p.replace("\\", "/") for p in core_files},
            target_files={p.replace("\\", "/") for p in target_files},
            core_import_names=import_names,
            leak_denylist=tuple(leak_denylist),
            vocabulary_floor=vocabulary_floor,
            core_vocabulary=core_vocabulary,
        )

    # -- the five conditions -------------------------------------------------

    def check(self, candidate: CandidateFile) -> list[Violation]:
        violations: list[Violation] = []
        dest = candidate.destination_path.replace("\\", "/")

        # 1. Structural irrelevance
        if dest in self.core_files:
            violations.append(Violation(1, f"{dest} is a core file"))
        if dest in self.target_files:
            violations.append(Violation(1, f"{dest} is a target file"))
        if module_names_for(dest) & self.core_import_names:
            violations.append(
                Violation(1, f"{dest} is importable by a core import statement")
            )

        # 2. Behavior neutrality
        basename = PurePosixPath(dest).name
        if basename in FORBIDDEN_BASENAMES:
            violations.append(
                Violation(2, f"{basename} has ambient side effects (forbidden basename)")
            )
        shadowed = self._shadows_core_module(dest)
        if shadowed:
            violations.append(Violation(2, f"{dest} would shadow core module {shadowed}"))
        for pattern in _DYNAMIC_RED_FLAGS:
            if pattern.search(candidate.content):
                violations.append(
                    Violation(
                        2,
                        f"dynamic-import red flag `{pattern.pattern}` in {dest} "
                        "(needs manual clearance; rejected by default)",
                    )
                )
                break

        # 3. Plausibility (hard gate for generated files)
        if dest.endswith(".py"):
            try:
                ast.parse(candidate.content)
            except SyntaxError as exc:
                violations.append(Violation(3, f"{dest} does not parse: {exc}"))
            else:
                if candidate.mode != "regrow" and self.core_vocabulary is not None:
                    from .vocabulary import collect_identifiers

                    overlap = self.core_vocabulary.overlap_fraction(
                        collect_identifiers(candidate.content)
                    )
                    if overlap < self.vocabulary_floor:
                        violations.append(
                            Violation(
                                3,
                                f"{dest} vocabulary overlap {overlap:.3f} below "
                                f"floor {self.vocabulary_floor:.3f}",
                            )
                        )

        # 4. No leakage
        for needle in self.leak_denylist:
            if needle and needle in candidate.content:
                violations.append(
                    Violation(4, f"{dest} contains denylisted hidden-assertion text")
                )
                break

        # 5. No tell. Path markers are always forbidden; content markers only
        # gate *generated* files — an organic occurrence of a word like
        # "noise" in a verbatim project file is not a benchmark artifact.
        lowered_dest = dest.lower()
        for marker in TELL_MARKERS:
            if marker in lowered_dest:
                violations.append(Violation(5, f"path {dest} carries marker '{marker}'"))
                break
        if candidate.mode != "regrow":
            lowered_content = candidate.content.lower()
            for marker in TELL_MARKERS:
                if marker in lowered_content:
                    violations.append(
                        Violation(5, f"{dest} content carries marker '{marker}'")
                    )
                    break

        return violations

    def _shadows_core_module(self, dest: str) -> str | None:
        dest_names = module_names_for(dest)
        if not dest_names:
            return None
        for core_path in self.core_files:
            if module_names_for(core_path) & dest_names:
                return core_path
        return None
