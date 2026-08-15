"""Generate deterministic pytest regression tests from a user story contract."""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from .user_story_tests import _contract_path_for_story, _story_content_hash, story_id


_HEADING_RE = re.compile(r"^##\s+(?P<heading>.+?)\s*$", re.MULTILINE)
_COVER_RE = re.compile(r"\b(R\d+)\b", re.IGNORECASE)


@dataclass(frozen=True)
class StoryTestSpec:
    """Parsed executable contract details for one story."""

    story_path: Path
    contract_path: Path
    story_id: str
    story_hash: str
    module: str
    callable_name: str
    args: str = "[]"
    kwargs: str = "{}"
    seams: tuple[tuple[str, str], ...] = ()
    rule_ids: tuple[str, ...] = ()
    oracle_assertions: tuple[str, ...] = ()
    negative_assertions: tuple[str, ...] = ()


@dataclass(frozen=True)
class StoryTestGenerationResult:
    """Result of generating a story regression test file."""

    output_path: Path
    test_count: int
    story_id: str
    story_hash: str


def _sections(markdown: str) -> dict[str, str]:
    matches = list(_HEADING_RE.finditer(markdown))
    result: dict[str, str] = {}
    for index, match in enumerate(matches):
        start = match.end()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(markdown)
        result[match.group("heading").strip().lower()] = markdown[start:end].strip()
    return result


def _bullet_lines(text: str) -> list[str]:
    bullets: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line.startswith(("-", "*")):
            continue
        item = line[1:].strip()
        if item:
            bullets.append(item)
    return bullets


def _key_values(section: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for item in _bullet_lines(section):
        if ":" in item:
            key, value = item.split(":", 1)
        elif "=" in item:
            key, value = item.split("=", 1)
        else:
            continue
        values[key.strip().lower().replace(" ", "_")] = value.strip()
    if not values and section.strip() and ":" in section.strip() and "\n" not in section.strip():
        module, callable_name = section.strip().split(":", 1)
        values["module"] = module.strip()
        values["callable"] = callable_name.strip()
    return values


# Assertion bullets are issue/LLM-derived text that gets spliced verbatim into
# `assert {expr}` in a generated pytest file the story-regression CI lane
# executes -- and that file also has `importlib` and `module` in module scope
# (see `render_story_test`), so a permissive allowlist doesn't just risk
# builtins like `__import__('os').system(...)`; a bare name check alone lets
# `importlib.import_module("os").system(...)` and `module.os.system(...)`
# through too. Syntax validity alone does not make an expression safe, so this
# allowlist constrains bullets to a read-only "compare/inspect `result`" DSL:
# - only `result` and a small set of pure builtins may appear as bare names
# - every attribute/subscript chain must be rooted at `result` (not at
#   `module`, `importlib`, or any other name in the generated test's scope)
# - a call is either one of the safe builtins, or a read-only method looked up
#   on `result` (never a mutator like `result.clear()`)
_SAFE_ASSERTION_CALL_NAMES = frozenset(
    {
        "len", "isinstance", "str", "int", "float", "bool", "abs", "round",
        "sorted", "min", "max", "sum", "any", "all", "repr", "type",
        "dict", "list", "tuple", "set",
    }
)
_SAFE_RESULT_METHOD_NAMES = frozenset(
    {
        "get", "keys", "values", "items", "count", "index",
        "lower", "upper", "strip", "lstrip", "rstrip",
        "startswith", "endswith", "split", "splitlines", "join",
        "isdigit", "isalpha", "isalnum", "isupper", "islower", "isspace",
        "copy",
    }
)
_SAFE_ASSERTION_NAMES = frozenset({"result"}) | _SAFE_ASSERTION_CALL_NAMES
_SAFE_ASSERTION_NODE_TYPES = (
    ast.Expression, ast.BoolOp, ast.UnaryOp, ast.BinOp, ast.Compare, ast.Call,
    ast.Name, ast.Load, ast.Constant, ast.Attribute, ast.Subscript, ast.Slice,
    ast.List, ast.Tuple, ast.Dict, ast.Set,
    ast.And, ast.Or, ast.Not, ast.Invert, ast.UAdd, ast.USub,
    ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow,
    ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Is, ast.IsNot,
    ast.In, ast.NotIn,
)


def _chain_root(node: ast.AST) -> ast.AST:
    """Walk down an Attribute/Subscript chain to the value it's rooted at."""
    while isinstance(node, (ast.Attribute, ast.Subscript)):
        node = node.value
    return node


def _is_rooted_at_result(node: ast.AST) -> bool:
    root = _chain_root(node)
    return isinstance(root, ast.Name) and root.id == "result"


def _ensure_safe_assertion(tree: ast.AST, bullet: str) -> None:
    """Reject any assertion expression outside the safe result-inspection DSL."""
    for node in ast.walk(tree):
        if not isinstance(node, _SAFE_ASSERTION_NODE_TYPES):
            raise ValueError(
                "Story assertion bullets may only compare/inspect `result` "
                f"(unsupported construct {type(node).__name__}): {bullet!r}"
            )
        if isinstance(node, ast.Name) and node.id not in _SAFE_ASSERTION_NAMES:
            raise ValueError(
                "Story assertion bullet references a name other than `result` "
                f"or a safe helper: {bullet!r}"
            )
        if isinstance(node, ast.Attribute):
            if node.attr.startswith("_"):
                raise ValueError(
                    f"Story assertion bullet accesses a private/dunder attribute: {bullet!r}"
                )
            if not _is_rooted_at_result(node):
                raise ValueError(
                    "Story assertion bullet accesses an attribute not rooted at "
                    f"`result`: {bullet!r}"
                )
        if isinstance(node, ast.Subscript) and not _is_rooted_at_result(node):
            raise ValueError(
                f"Story assertion bullet subscripts something other than `result`: {bullet!r}"
            )
        if isinstance(node, ast.Call):
            func = node.func
            if isinstance(func, ast.Name):
                if func.id not in _SAFE_ASSERTION_CALL_NAMES:
                    raise ValueError(
                        f"Story assertion bullet calls disallowed function {func.id!r}; "
                        f"only {sorted(_SAFE_ASSERTION_CALL_NAMES)} are permitted: {bullet!r}"
                    )
            elif isinstance(func, ast.Attribute):
                if not _is_rooted_at_result(func):
                    raise ValueError(
                        "Story assertion bullet calls a method not rooted at "
                        f"`result`: {bullet!r}"
                    )
                if func.attr not in _SAFE_RESULT_METHOD_NAMES:
                    raise ValueError(
                        f"Story assertion bullet calls disallowed `result` method "
                        f"{func.attr!r}; only read-only methods "
                        f"{sorted(_SAFE_RESULT_METHOD_NAMES)} are permitted: {bullet!r}"
                    )
            else:
                raise ValueError(f"Story assertion bullet has an unsupported call target: {bullet!r}")


def _assertion_from_bullet(bullet: str) -> str:
    text = bullet.strip()
    if text.startswith("assert "):
        expr = text[len("assert "):].strip()
    else:
        expr = text
    if not expr:
        raise ValueError("Story assertion bullet is empty.")
    try:
        tree = ast.parse(expr, mode="eval")
    except SyntaxError as exc:
        raise ValueError(
            "Story test generation requires Oracle/Negative Cases bullets to be "
            f"Python assertion expressions over `result`; got: {bullet!r}"
        ) from exc
    _ensure_safe_assertion(tree, bullet)
    return expr


def _literal_source(value: str, *, fallback: str) -> str:
    text = value.strip() if value else fallback
    try:
        ast.literal_eval(text)
    except (SyntaxError, ValueError):
        raise ValueError(f"Expected a Python literal, got: {value!r}") from None
    return text


def _parse_seams(section: str) -> tuple[tuple[str, str], ...]:
    seams: list[tuple[str, str]] = []
    for item in _bullet_lines(section):
        if "=" not in item:
            continue
        target, value = item.split("=", 1)
        target = target.strip()
        value = value.strip()
        if not target:
            continue
        _literal_source(value, fallback="None")
        seams.append((target, value))
    return tuple(seams)


def parse_story_test_spec(story_path: Path) -> StoryTestSpec:
    """Parse a story and its sibling contract into an executable test spec."""
    story_path = Path(story_path)
    if not story_path.is_file():
        raise FileNotFoundError(f"Story file not found: {story_path}")

    contract_path = _contract_path_for_story(story_path)
    if not contract_path.is_file():
        raise FileNotFoundError(f"Story contract not found: {contract_path}")

    story_text = story_path.read_text(encoding="utf-8")
    contract_text = contract_path.read_text(encoding="utf-8")
    sections = _sections(contract_text)

    entry = _key_values(sections.get("entry point", ""))
    module = entry.get("module")
    callable_name = entry.get("callable") or entry.get("function")
    if not module or not callable_name:
        raise ValueError(
            "Story contract must include ## Entry Point with '- module: ...' "
            "and '- callable: ...' before deterministic tests can be generated."
        )

    args = _literal_source(entry.get("args", "[]"), fallback="[]")
    kwargs = _literal_source(entry.get("kwargs", "{}"), fallback="{}")
    if not isinstance(ast.literal_eval(args), list):
        raise ValueError("Entry Point args must be a list literal.")
    if not isinstance(ast.literal_eval(kwargs), dict):
        raise ValueError("Entry Point kwargs must be a dict literal.")

    oracle = tuple(_assertion_from_bullet(item) for item in _bullet_lines(sections.get("oracle", "")))
    negative = tuple(
        _assertion_from_bullet(item) for item in _bullet_lines(sections.get("negative cases", ""))
    )
    if not oracle and not negative:
        raise ValueError("Story contract must include assertion bullets under ## Oracle or ## Negative Cases.")

    covers = tuple(dict.fromkeys(match.group(1).upper() for match in _COVER_RE.finditer(sections.get("covers", ""))))
    return StoryTestSpec(
        story_path=story_path,
        contract_path=contract_path,
        story_id=story_id(story_path),
        story_hash=_story_content_hash(story_text),
        module=module,
        callable_name=callable_name,
        args=args,
        kwargs=kwargs,
        seams=_parse_seams(sections.get("seams", "")),
        rule_ids=covers,
        oracle_assertions=oracle,
        negative_assertions=negative,
    )


def _safe_name(text: str) -> str:
    name = re.sub(r"[^a-zA-Z0-9]+", "_", text).strip("_").lower()
    return name or "assertion"


def render_story_test(spec: StoryTestSpec) -> str:
    """Render deterministic pytest source for *spec*."""
    seams_source = "[" + ", ".join(
        f"({target!r}, {value})" for target, value in spec.seams
    ) + "]"
    lines: list[str] = [
        '"""Generated story regression tests. Do not hand-edit."""',
        "from __future__ import annotations",
        "",
        "import importlib",
        "import pytest",
        "",
        f"STORY_ID = {spec.story_id!r}",
        f"STORY_HASH = {spec.story_hash!r}",
        f"ENTRY_MODULE = {spec.module!r}",
        f"ENTRY_CALLABLE = {spec.callable_name!r}",
        f"ENTRY_ARGS = {spec.args}",
        f"ENTRY_KWARGS = {spec.kwargs}",
        f"SEAMS = {seams_source}",
        "",
        "",
        "@pytest.fixture()",
        "def story_result(monkeypatch):",
        "    for target, value in SEAMS:",
        "        monkeypatch.setattr(target, value)",
        "    module = importlib.import_module(ENTRY_MODULE)",
        "    entry = getattr(module, ENTRY_CALLABLE)",
        "    return entry(*ENTRY_ARGS, **ENTRY_KWARGS)",
        "",
    ]

    assertions = [("oracle", item) for item in spec.oracle_assertions]
    assertions.extend(("negative", item) for item in spec.negative_assertions)
    for index, (kind, expr) in enumerate(assertions, 1):
        rule = spec.rule_ids[min(index - 1, len(spec.rule_ids) - 1)] if spec.rule_ids else f"R{index}"
        fn_name = f"test_story_{_safe_name(spec.story_id)}_{rule}_{kind}_{index}"
        lines.extend(
            [
                f"@pytest.mark.story(story_id=STORY_ID, story_hash=STORY_HASH)",
                f"def {fn_name}(story_result):",
                "    result = story_result",
                f"    assert {expr}",
                "",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def generate_story_test(story_path: Path, output: Optional[Path] = None) -> StoryTestGenerationResult:
    """Generate a deterministic pytest file for *story_path*."""
    spec = parse_story_test_spec(Path(story_path))
    if output is None:
        output_dir = Path("tests") / "story_regression"
        output_dir.mkdir(parents=True, exist_ok=True)
        output = output_dir / f"test_story_{_safe_name(spec.story_id)}.py"
    else:
        output = Path(output)
        if output.is_dir():
            output = output / f"test_story_{_safe_name(spec.story_id)}.py"
        output.parent.mkdir(parents=True, exist_ok=True)

    source = render_story_test(spec)
    if output.exists() and output.read_text(encoding="utf-8") == source:
        test_count = len(spec.oracle_assertions) + len(spec.negative_assertions)
        return StoryTestGenerationResult(output, test_count, spec.story_id, spec.story_hash)

    output.write_text(source, encoding="utf-8")
    test_count = len(spec.oracle_assertions) + len(spec.negative_assertions)
    return StoryTestGenerationResult(output, test_count, spec.story_id, spec.story_hash)
