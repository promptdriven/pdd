"""Core logic for scanning Python code for policy violations using AST-based static analysis."""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from .contract_ir import Capability, PromptContractIR, extract_capabilities, parse_prompt_contracts

# Substrings matched against lowercased capability bullet text (v1 heuristic).
_NETWORK_KEYWORDS = (
    "network",
    "api",
    "http",
    "https",
    "endpoint",
    "url",
    "fetch",
    "request",
    "provider",
    "socket",
)
_SHELL_KEYWORDS = ("shell", "command", "subprocess", "exec", "spawn", "system")
_FILE_KEYWORDS = ("file", "write", "delete", "filesystem", "disk", "persist", "storage")
_ENV_KEYWORDS = ("env", "environment", "environ", "configuration", "config")
_EMAIL_KEYWORDS = ("email", "mail", "smtp")

NETWORK_LIBS = {
    "urllib3",
    "paramiko",
    "httpx",
    "requests",
    "aiohttp",
    "socket",
    "ftplib",
    "telnetlib",
    "smtplib",
    "email",
}

SHELL_LIBS = {"subprocess", "os", "shutil", "pty"}

SENSITIVE_KEYS = frozenset(
    {"token", "secret", "password", "api_key", "cvv", "pan", "bearer"}
)
_SENSITIVE_WORD_RE = re.compile(
    r"\b(" + "|".join(re.escape(k) for k in sorted(SENSITIVE_KEYS, key=len, reverse=True)) + r")\b",
    re.IGNORECASE,
)

SHELL_METHODS = frozenset({"system", "popen", "spawnl", "spawnv", "spawnlp", "spawnvp"})
FILE_WRITE_METHODS = frozenset(
    {"remove", "unlink", "chmod", "rmtree", "mkdir", "rename", "replace", "write", "write_text"}
)
ENV_METHODS = frozenset({"getenv", "putenv"})
_WRITE_OPEN_MODES = frozenset({"w", "a", "x", "+"})


@dataclass
class PolicyIssue:
    category: str
    message: str
    line: int
    col: int
    severity: str = "error"


@dataclass
class PolicyResult:
    target_path: Path
    issues: list[PolicyIssue] = field(default_factory=list)
    passed: bool = True
    capabilities: list[Capability] = field(default_factory=list)


def _capability_allows(capabilities: list[Capability], keywords: tuple[str, ...]) -> bool:
    """Return True when a MAY/SHOULD capability mentions any keyword; False on MUST NOT."""
    lowered_keywords = tuple(kw.lower() for kw in keywords)
    for cap in capabilities:
        text = cap.text.lower()
        if cap.is_must_not and any(kw in text for kw in lowered_keywords):
            return False
    for cap in capabilities:
        if cap.is_must_not:
            continue
        if any(kw in cap.text.lower() for kw in lowered_keywords):
            return True
    return False


class PolicyVisitor(ast.NodeVisitor):
    def __init__(
        self,
        capabilities: list[Capability],
        *,
        strict: bool = False,
        source_lines: Optional[list[str]] = None,
        prompt_ir: Optional[PromptContractIR] = None,
    ) -> None:
        self.capabilities = capabilities
        self.strict = strict
        self.source_lines = source_lines or []
        self.prompt_ir = prompt_ir
        self.issues: list[PolicyIssue] = []
        self.imported_names: dict[str, str] = {}

        self.has_capabilities = len(capabilities) > 0
        self.should_check = self.strict or self.has_capabilities

        self.allowed_network = _capability_allows(capabilities, _NETWORK_KEYWORDS)
        self.allowed_shell = _capability_allows(capabilities, _SHELL_KEYWORDS)
        self.allowed_file = _capability_allows(capabilities, _FILE_KEYWORDS)
        self.allowed_env = _capability_allows(capabilities, _ENV_KEYWORDS)
        self.allowed_email = _capability_allows(capabilities, _EMAIL_KEYWORDS)

    def _is_waived(self, node: ast.AST, category: str, message: str) -> bool:
        if hasattr(node, "lineno") and node.lineno <= len(self.source_lines):
            line_text = self.source_lines[node.lineno - 1]
            if "# pdd-policy-ignore" in line_text:
                return True
            if node.lineno > 1 and "# pdd-policy-ignore" in self.source_lines[node.lineno - 2]:
                return True

        if self.prompt_ir and self.prompt_ir.waivers:
            for waiver in self.prompt_ir.waivers:
                block = f"{waiver.raw_block}\n{waiver.reason}".lower()
                if category.lower() in block and message.lower() in block:
                    return True
        return False

    def _add_issue(self, node: ast.AST, category: str, message: str) -> None:
        if not self.should_check or self._is_waived(node, category, message):
            return
        lineno = getattr(node, "lineno", 0) or 0
        col = getattr(node, "col_offset", 0) or 0
        self.issues.append(PolicyIssue(category, message, lineno, col))

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            self._check_import(alias.name, node)
            self.imported_names[alias.asname or alias.name] = alias.name
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        if node.module:
            self._check_import(node.module, node)
            for alias in node.names:
                self.imported_names[alias.asname or alias.name] = node.module
        self.generic_visit(node)

    def _check_import(self, module: str, node: ast.AST) -> None:
        base_module = module.split(".")[0]
        if base_module in NETWORK_LIBS and not self.allowed_network:
            self._add_issue(node, "network", f"Unauthorized network library import: {module}")
        if base_module in {"smtplib", "email"} and not self.allowed_email:
            self._add_issue(node, "email", f"Unauthorized email library import: {module}")
        if base_module in SHELL_LIBS and not self.allowed_shell and base_module != "os":
            self._add_issue(node, "shell", f"Unauthorized shell library import: {module}")

    def _open_looks_like_write(self, node: ast.Call) -> bool:
        mode: Optional[str] = None
        if len(node.args) >= 2 and isinstance(node.args[1], ast.Constant):
            value = node.args[1].value
            if isinstance(value, str):
                mode = value
        for keyword in node.keywords:
            if keyword.arg == "mode" and isinstance(keyword.value, ast.Constant):
                value = keyword.value.value
                if isinstance(value, str):
                    mode = value
        if mode is None:
            return False
        return any(flag in mode for flag in _WRITE_OPEN_MODES)

    def visit_Call(self, node: ast.Call) -> None:
        func_name = ""
        module_name = ""

        if isinstance(node.func, ast.Attribute):
            if isinstance(node.func.value, ast.Name):
                module_name = node.func.value.id
                func_name = node.func.attr
            elif isinstance(node.func.value, ast.Attribute) and isinstance(
                node.func.value.value, ast.Name
            ):
                module_name = f"{node.func.value.value.id}.{node.func.value.attr}"
                func_name = node.func.attr
        elif isinstance(node.func, ast.Name):
            func_name = node.func.id
            module_name = self.imported_names.get(func_name, "")

        if (module_name == "os" and func_name in SHELL_METHODS) or (
            module_name == "subprocess"
        ) or (func_name == "system" and not module_name):
            if not self.allowed_shell:
                label = f"{module_name}.{func_name}" if module_name else func_name
                self._add_issue(node, "shell", f"Unauthorized shell execution: {label}")

        if (module_name == "os" and func_name in FILE_WRITE_METHODS) or (
            module_name == "shutil" and func_name in FILE_WRITE_METHODS
        ) or (module_name == "pathlib" and func_name in {"write_text", "write_bytes"}):
            if not self.allowed_file:
                label = f"{module_name}.{func_name}" if module_name else func_name
                self._add_issue(node, "file", f"Unauthorized file operation: {label}")
        elif func_name == "open" and not module_name and self._open_looks_like_write(node):
            if not self.allowed_file:
                self._add_issue(node, "file", "Unauthorized file write via open()")

        if (module_name == "os" and func_name in ENV_METHODS) or (
            func_name in ENV_METHODS
            and not module_name
            and self.imported_names.get(func_name) == "os"
        ):
            if not self.allowed_env:
                label = f"{module_name}.{func_name}" if module_name else func_name
                self._add_issue(node, "env", f"Unauthorized environment access: {label}")

        if func_name in {"debug", "info", "warning", "error", "critical", "log", "print"}:
            self._check_sensitive_args(list(node.args), node)
            for keyword in node.keywords:
                self._check_sensitive_args([keyword.value], node)

        if isinstance(node.func, ast.Attribute) and func_name == "format":
            self._check_sensitive_args(list(node.args) + [kw.value for kw in node.keywords], node)

        if isinstance(node.func, ast.Attribute) and func_name in {"Mod", "mod"}:
            self._check_sensitive_args(list(node.args), node)

        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> None:
        if isinstance(node.value, ast.Name) and node.value.id == "os" and node.attr in {
            "environ",
            "environb",
        }:
            if not self.allowed_env:
                self._add_issue(node, "env", f"Unauthorized environment access: os.{node.attr}")
        self.generic_visit(node)

    def visit_BinOp(self, node: ast.BinOp) -> None:
        if isinstance(node.op, ast.Mod):
            self._check_sensitive_args([node.left, node.right], node)
        self.generic_visit(node)

    def _name_is_sensitive(self, name: str) -> bool:
        lowered = name.lower()
        if _SENSITIVE_WORD_RE.search(lowered):
            return True
        return any(key in lowered for key in SENSITIVE_KEYS)

    def _check_sensitive_args(self, args: list[ast.AST], node: ast.AST) -> None:
        for arg in args:
            if isinstance(arg, ast.Name) and self._name_is_sensitive(arg.id):
                self._add_issue(node, "leakage", f"Potential sensitive data leakage: {arg.id}")
            elif isinstance(arg, ast.Attribute) and self._name_is_sensitive(arg.attr):
                self._add_issue(node, "leakage", f"Potential sensitive data leakage: {arg.attr}")
            elif isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                if self._name_is_sensitive(arg.value) and ("=" in arg.value or ":" in arg.value):
                    self._add_issue(
                        node,
                        "leakage",
                        f"Potential sensitive data in string: {arg.value[:20]}...",
                    )
            elif isinstance(arg, ast.JoinedStr):
                for value in arg.values:
                    if isinstance(value, ast.FormattedValue):
                        self._check_sensitive_args([value.value], node)


def run_policy_check(
    target_path: Path,
    prompt_path: Optional[Path] = None,
    *,
    strict: bool = False,
) -> PolicyResult:
    """Run policy check on a file."""
    try:
        content = target_path.read_text(encoding="utf-8")
        source_lines = content.splitlines()
        tree = ast.parse(content)
    except (OSError, UnicodeDecodeError, SyntaxError) as exc:
        return PolicyResult(
            target_path,
            [PolicyIssue("system", f"Failed to parse or read file: {exc}", 0, 0)],
            passed=False,
        )

    capabilities: list[Capability] = []
    prompt_ir: Optional[PromptContractIR] = None
    if prompt_path and prompt_path.exists():
        prompt_ir = parse_prompt_contracts(prompt_path)
        if "capabilities" in prompt_ir.sections:
            capabilities = extract_capabilities(prompt_ir.sections["capabilities"])

    visitor = PolicyVisitor(
        capabilities,
        strict=strict,
        source_lines=source_lines,
        prompt_ir=prompt_ir,
    )
    visitor.visit(tree)
    passed = len(visitor.issues) == 0
    return PolicyResult(target_path, visitor.issues, passed=passed, capabilities=capabilities)


def prompt_has_capabilities(prompt_path: Path) -> bool:
    """Return True when ``prompt_path`` defines a non-empty ``<capabilities>`` section."""
    if not prompt_path.is_file():
        return False
    ir = parse_prompt_contracts(prompt_path)
    if "capabilities" not in ir.sections:
        return False
    return bool(extract_capabilities(ir.sections["capabilities"]))


def resolve_policy_prompt_for_code(worktree: Path, code_rel: str) -> Optional[Path]:
    """Best-effort prompt path for a changed Python file inside ``worktree``."""
    stem = Path(code_rel).stem
    candidates = [
        worktree / "prompts" / f"{stem}_python.prompt",
        worktree / "pdd" / "prompts" / f"{stem}_python.prompt",
    ]
    prompts_root = worktree / "prompts"
    if prompts_root.is_dir():
        matches = list(prompts_root.rglob(f"{stem}_python.prompt"))
        if len(matches) == 1:
            candidates.append(matches[0])
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    return None
