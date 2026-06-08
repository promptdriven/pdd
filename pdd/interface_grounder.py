"""Interface grounding module: AST-based real interface inspection (issue #1466).

Extracts interface facts (function signatures, class definitions, config keys)
from real Python source files using the stdlib ast module. All extraction is
deterministic — no LLM calls.
"""
from __future__ import annotations

import ast
import hashlib
import logging
from pathlib import Path
from typing import Optional

from pdd.generation_source_contract import (
    GenerationSourceContract,
    InterfaceFact,
)

logger = logging.getLogger(__name__)


def _sha256_file(path: Path) -> str:
    """Return the SHA-256 hex digest of a file's contents."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _sha256_text(text: str) -> str:
    """Return the SHA-256 hex digest of a text string."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class _InterfaceVisitor(ast.NodeVisitor):
    """AST NodeVisitor that collects function and class interface facts."""

    def __init__(self, source_sha256: str, module_path: str) -> None:
        self.source_sha256 = source_sha256
        self.module_path = module_path
        self.facts: list[InterfaceFact] = []

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # noqa: N802
        # Build a simple signature string
        args = [a.arg for a in node.args.args]
        sig = f"{node.name}({', '.join(args)})"
        if node.returns:
            sig += f" -> {ast.unparse(node.returns)}"

        self.facts.append(
            InterfaceFact(
                fact_kind="function_signature",
                name=node.name,
                signature=sig,
                source_sha256=self.source_sha256,
                module_path=self.module_path,
            )
        )
        self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:  # noqa: N802
        args = [a.arg for a in node.args.args]
        sig = f"async {node.name}({', '.join(args)})"
        if node.returns:
            sig += f" -> {ast.unparse(node.returns)}"

        self.facts.append(
            InterfaceFact(
                fact_kind="function_signature",
                name=node.name,
                signature=sig,
                source_sha256=self.source_sha256,
                module_path=self.module_path,
            )
        )
        self.generic_visit(node)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:  # noqa: N802
        # Record the class itself
        self.facts.append(
            InterfaceFact(
                fact_kind="class_fields",
                name=node.name,
                signature=node.name,
                source_sha256=self.source_sha256,
                module_path=self.module_path,
            )
        )
        self.generic_visit(node)


def extract_python_interfaces(path: Path) -> list[InterfaceFact]:
    """Parse a Python source file with ast and return a list of InterfaceFacts.

    Returns an empty list (rather than raising) if the file does not exist,
    cannot be read, or contains a syntax error.
    """
    if not path.exists():
        logger.warning("extract_python_interfaces: file not found: %s", path)
        return []

    try:
        source = path.read_text(encoding="utf-8")
    except OSError as exc:
        logger.warning("extract_python_interfaces: cannot read %s: %s", path, exc)
        return []

    try:
        tree = ast.parse(source, filename=str(path))
    except SyntaxError as exc:
        logger.warning("extract_python_interfaces: syntax error in %s: %s", path, exc)
        return []

    sha256 = _sha256_text(source)
    visitor = _InterfaceVisitor(source_sha256=sha256, module_path=str(path))
    visitor.visit(tree)
    return visitor.facts


def extract_config_keys(path: Path) -> list[InterfaceFact]:
    """Extract config keys from a YAML/TOML config file.

    Returns an empty list for non-existent or non-parseable files.
    """
    if not path.exists():
        return []

    try:
        import yaml  # type: ignore[import-untyped]
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except Exception as exc:
        logger.warning("extract_config_keys: cannot parse %s: %s", path, exc)
        return []

    if not isinstance(data, dict):
        return []

    sha256 = _sha256_file(path)
    facts: list[InterfaceFact] = []

    def _flatten(obj: object, prefix: str = "") -> None:
        if isinstance(obj, dict):
            for k, v in obj.items():
                key = f"{prefix}.{k}" if prefix else k
                _flatten(v, key)
        else:
            facts.append(
                InterfaceFact(
                    fact_kind="config_key",
                    name=prefix,
                    source_sha256=sha256,
                    module_path=str(path),
                )
            )

    _flatten(data)
    return facts


def ground_interfaces(
    contract: GenerationSourceContract,
    project_root: Path,
) -> GenerationSourceContract:
    """Populate interface_facts on the contract by scanning Python source files.

    Scans all .py files under project_root and extracts interface facts.
    Returns the mutated contract (same object).
    """
    all_facts: list[InterfaceFact] = []

    for py_file in sorted(project_root.rglob("*.py")):
        # Skip __pycache__ and hidden directories
        if any(part.startswith((".", "__")) for part in py_file.parts):
            continue
        facts = extract_python_interfaces(py_file)
        all_facts.extend(facts)
        if facts:
            logger.debug(
                "ground_interfaces: extracted %d facts from %s", len(facts), py_file
            )

    contract.interface_facts = all_facts
    logger.info(
        "ground_interfaces: run_id=%s, total_facts=%d",
        contract.run_id,
        len(all_facts),
    )
    return contract
