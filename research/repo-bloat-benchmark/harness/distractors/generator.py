"""Deterministic distractor generation (design.md §5.0.1, §5.1, §5.3).

Fills a per-(scenario, size) token budget with files that pass the
``DefinitionChecker`` contract, using the fixed source cascade:

1. ``regrow``  — verbatim pool files (``snapshot ∖ core``), admitted in
   dependency-closed import groups, ordered by (tier, stable hash);
2. ``mutate``  — seeded identifier/docstring derivations of pool files at
   non-colliding sibling paths, once the pool is exhausted;
3. ``template`` — synthetic size-tunable modules from core vocabulary, as the
   terminal filler so any budget (50x, breakdown probe) converges.

Given the same inputs and seed, output is byte-identical — manifests are
committed before any model run (freeze-before-runs).
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Callable

from .definition import CandidateFile, DefinitionChecker, imported_modules, module_names_for
from .vocabulary import Vocabulary, harvest_vocabulary

SIZE_LADDER = (1, 2, 5, 10, 20, 50)
TIER_ORDER = {"same-package": 0, "same-layer": 1, "cross-cutting": 2}


def estimate_tokens(text: str) -> int:
    """Deterministic on-disk token-dose estimate (~4 chars/token, design §5.1)."""
    return max(1, round(len(text) / 4))


def stable_hash(*parts: object) -> str:
    return hashlib.sha256("|".join(str(p) for p in parts).encode()).hexdigest()


def tier_for(destination: str, target_file: str) -> str:
    """Tier from layout distance to the target (design §5.2)."""
    dest_dir = PurePosixPath(destination).parent
    target_dir = PurePosixPath(target_file).parent
    if dest_dir == target_dir:
        return "same-package"
    if dest_dir.parent == target_dir.parent:
        return "same-layer"
    return "cross-cutting"


@dataclass
class GenerationConfig:
    scenario_id: str
    core_root: Path
    target_file: str  # core-relative path of the seeded target
    pool_root: Path | None = None  # snapshot ∖ core; None ⇒ generated-only
    selection_seed: int = 1209
    tolerance_pct: float = 2.0
    leak_denylist: tuple[str, ...] = ()
    vocabulary_floor: float = 0.02
    token_estimator: Callable[[str], int] = estimate_tokens
    max_mutants_per_source: int = 20
    template_file_tokens: int = 800

    def __post_init__(self) -> None:
        self.core_root = Path(self.core_root)
        if self.pool_root is not None:
            self.pool_root = Path(self.pool_root)


@dataclass
class _Admitted:
    destination: str
    content: str
    mode: str
    tier: str
    import_group: str
    source_path: str | None
    tokens: int


def _read_tree(root: Path, extensions: tuple[str, ...] = (".py",)) -> dict[str, str]:
    files: dict[str, str] = {}
    for path in sorted(root.rglob("*")):
        if path.is_file() and path.suffix in extensions:
            files[path.relative_to(root).as_posix()] = path.read_text(
                encoding="utf-8", errors="replace"
            )
    return files


# --------------------------------------------------------------------------
# regrow
# --------------------------------------------------------------------------


def _pool_import_groups(pool: dict[str, str]) -> dict[str, list[str]]:
    """Map each pool file to its dependency-closed group within the pool."""
    name_to_path: dict[str, str] = {}
    for path in pool:
        for name in module_names_for(path):
            name_to_path.setdefault(name, path)
    groups: dict[str, list[str]] = {}
    for path, source in pool.items():
        closure: set[str] = set()
        frontier = [path]
        while frontier:
            current = frontier.pop()
            if current in closure:
                continue
            closure.add(current)
            for imported in imported_modules(pool.get(current, "")):
                resolved = name_to_path.get(imported)
                if resolved and resolved not in closure:
                    frontier.append(resolved)
        groups[path] = sorted(closure)
    return groups


def _regrow_candidates(
    config: GenerationConfig, pool: dict[str, str]
) -> list[tuple[str, list[str]]]:
    """Deterministically ordered (path, dependency_group) admission list."""
    groups = _pool_import_groups(pool)
    ordered = sorted(
        pool,
        key=lambda p: (
            TIER_ORDER[tier_for(p, config.target_file)],
            stable_hash(config.selection_seed, p),
        ),
    )
    return [(path, groups[path]) for path in ordered]


# --------------------------------------------------------------------------
# mutate
# --------------------------------------------------------------------------

_DEF_RE = re.compile(r"^(\s*(?:def|class)\s+)([A-Za-z_]\w*)", re.M)


def _mutate_source(
    source: str, source_path: str, vocabulary: Vocabulary, seed_material: str
) -> tuple[str, str]:
    """Seeded, semantics-preserving derivation of a pool file.

    Renames top-level def/class identifiers with vocabulary-derived suffixes
    and rewrites the module docstring; returns (destination_path, content).
    Never imported by anything (definition condition 1 holds regardless), so
    internal consistency — not runtime equivalence — is what matters.
    """
    words = vocabulary.top_words(64) or ["module"]
    digest = stable_hash(seed_material, source_path)
    word = words[int(digest[:8], 16) % len(words)]
    suffix = f"_{word}"

    renames: dict[str, str] = {}
    for match in _DEF_RE.finditer(source):
        name = match.group(2)
        if not name.startswith("__"):
            renames[name] = name + suffix
    mutated = source
    for old, new in sorted(renames.items(), key=lambda kv: -len(kv[0])):
        mutated = re.sub(rf"\b{re.escape(old)}\b", new, mutated)

    header = (
        f'"""Support variant for the {word} pathway.\n\n'
        f"Derived interface kept in sync with its sibling module.\n"
        f'"""\n\n'
    )
    if not mutated.lstrip().startswith(('"""', "'''")):
        mutated = header + mutated

    pure = PurePosixPath(source_path)
    destination = str(pure.with_name(f"{pure.stem}{suffix}{pure.suffix}"))
    return destination, mutated


# --------------------------------------------------------------------------
# template
# --------------------------------------------------------------------------

_TEMPLATE_SHAPES = ("service", "handler", "helpers", "adapters", "validation")


def _template_module(
    vocabulary: Vocabulary, seed_material: str, index: int, target_tokens: int
) -> tuple[str, str]:
    """Synthesize one self-contained module from core vocabulary."""
    words = vocabulary.top_words(48) or ["record", "value", "config"]

    def pick(n: int) -> str:
        return words[int(stable_hash(seed_material, index, n)[:8], 16) % len(words)]

    shape = _TEMPLATE_SHAPES[index % len(_TEMPLATE_SHAPES)]
    noun, verb, aux = pick(1), pick(2), pick(3)
    module_name = f"{noun}_{shape}"
    lines = [
        f'"""{shape.capitalize()} utilities for {noun} {aux} processing."""',
        "",
        "from dataclasses import dataclass",
        "",
        "",
        "@dataclass",
        f"class {noun.capitalize()}{shape.capitalize()}Config:",
        f"    {aux}_limit: int = 100",
        f"    strict_{verb}: bool = False",
        "",
    ]
    body_index = 0
    content = "\n".join(lines)
    while estimate_tokens(content) < target_tokens:
        a, b = pick(10 + body_index), pick(11 + body_index)
        lines += [
            "",
            f"def {verb}_{a}_{b}_{body_index}(records, config):",
            f'    """Apply the {a} {b} policy to incoming records."""',
            "    selected = []",
            "    for record in records:",
            f"        if getattr(record, '{a}_flag', False) and config.strict_{verb}:",
            "            continue",
            f"        if len(selected) >= config.{aux}_limit:",
            "            break",
            "        selected.append(record)",
            "    return selected",
        ]
        body_index += 1
        content = "\n".join(lines)
    destination = f"src/{shape}/{module_name}_{index}.py"
    return destination, content + "\n"


# --------------------------------------------------------------------------
# budget filling
# --------------------------------------------------------------------------


def generate_manifest(config: GenerationConfig, size: int) -> dict:
    """Build the per-(scenario, size) manifest dict (design §5.5 + mode field).

    Returned manifest includes a ``generated_contents`` map (destination →
    content) for ``mutate``/``template`` files; ``ManifestWriter`` persists it.
    """
    core = _read_tree(config.core_root)
    core_tokens = sum(config.token_estimator(text) for text in core.values())
    core_loc = sum(text.count("\n") + 1 for text in core.values())
    target_tokens = (size - 1) * core_tokens
    tolerance = config.tolerance_pct / 100.0
    lower = target_tokens * (1 - tolerance)
    upper = target_tokens * (1 + tolerance)

    vocabulary = harvest_vocabulary(config.core_root)
    checker = DefinitionChecker.from_core(
        core_files=core.keys(),
        core_sources=core,
        target_files=[config.target_file],
        leak_denylist=config.leak_denylist,
        vocabulary_floor=config.vocabulary_floor,
        core_vocabulary=vocabulary,
    )

    pool = _read_tree(config.pool_root) if config.pool_root else {}
    admitted: list[_Admitted] = []
    taken: set[str] = set(core.keys())
    total = 0
    rejected: list[dict] = []

    def try_admit(candidate: CandidateFile, group: str) -> bool:
        nonlocal total
        if candidate.destination_path in taken:
            return False
        tokens = config.token_estimator(candidate.content)
        if total + tokens > upper:
            return False
        violations = checker.check(candidate)
        if violations:
            rejected.append(
                {
                    "destination_path": candidate.destination_path,
                    "mode": candidate.mode,
                    "violations": [str(v) for v in violations],
                }
            )
            return False
        admitted.append(
            _Admitted(
                destination=candidate.destination_path,
                content=candidate.content,
                mode=candidate.mode,
                tier=candidate.tier,
                import_group=group,
                source_path=candidate.source_path,
                tokens=tokens,
            )
        )
        taken.add(candidate.destination_path)
        total += tokens
        return True

    # 1. regrow — dependency-closed groups.
    if size > 1:
        for path, group_paths in _regrow_candidates(config, pool):
            if total >= lower:
                break
            if path in taken:
                continue
            group_id = "g" + stable_hash(config.selection_seed, *group_paths)[:8]
            for member in group_paths:
                if member in taken:
                    continue
                try_admit(
                    CandidateFile(
                        destination_path=member,
                        content=pool[member],
                        mode="regrow",
                        source_path=member,
                        tier=tier_for(member, config.target_file),
                    ),
                    group=group_id,
                )

        # 2. mutate — cycle the pool with increasing mutation indices.
        mutation_round = 0
        pool_order = [p for p, _ in _regrow_candidates(config, pool)]
        while total < lower and pool_order and mutation_round < config.max_mutants_per_source:
            for source_path in pool_order:
                if total >= lower:
                    break
                destination, content = _mutate_source(
                    pool[source_path],
                    source_path,
                    vocabulary,
                    seed_material=f"{config.selection_seed}.{mutation_round}",
                )
                try_admit(
                    CandidateFile(
                        destination_path=destination,
                        content=content,
                        mode="mutate",
                        source_path=source_path,
                        tier=tier_for(destination, config.target_file),
                    ),
                    group="g-mutate",
                )
            mutation_round += 1

        # 3. template — terminal filler; size-tuned so the budget converges.
        template_index = 0
        while total < lower and template_index < 100_000:
            remaining = int(lower - total)
            destination, content = _template_module(
                vocabulary,
                seed_material=str(config.selection_seed),
                index=template_index,
                target_tokens=min(config.template_file_tokens, max(remaining, 50)),
            )
            try_admit(
                CandidateFile(
                    destination_path=destination,
                    content=content,
                    mode="template",
                    tier=tier_for(destination, config.target_file),
                ),
                group="g-template",
            )
            template_index += 1

    files = [
        {
            "upstream_path": item.destination,
            "tokens": item.tokens,
            "loc": item.content.count("\n") + 1,
            "sha256": hashlib.sha256(item.content.encode()).hexdigest(),
            "tier": item.tier,
            "mode": item.mode,
            "import_group": item.import_group,
            "source_path": item.source_path,
        }
        for item in admitted
    ]
    manifest = {
        "schema_version": 3,
        "scenario_id": config.scenario_id,
        "size": f"{size}x",
        "selection_seed": config.selection_seed,
        "tokenizer": "chars/4-v1",
        "core_tokens": core_tokens,
        "core_loc": core_loc,
        "size_token_target": target_tokens,
        "size_token_tolerance_pct": config.tolerance_pct,
        "distractor_tokens_on_disk": total,
        "distractor_loc": sum(f["loc"] for f in files),
        "realized_total_tokens": core_tokens + total,
        "budget_met": total >= lower or size == 1,
        "mode_counts": {
            mode: sum(1 for f in files if f["mode"] == mode)
            for mode in ("regrow", "mutate", "template")
        },
        "files": files,
        "rejected": rejected,
    }
    generated = {
        item.destination: item.content for item in admitted if item.mode != "regrow"
    }
    manifest["generated_contents"] = generated
    return manifest


def generate_ladder(
    config: GenerationConfig, sizes: tuple[int, ...] = SIZE_LADDER
) -> dict[int, dict]:
    """Generate manifests for every ladder step (including the 1x control)."""
    return {size: generate_manifest(config, size) for size in sizes}
