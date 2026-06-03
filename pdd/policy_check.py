"""Core logic for scanning Python code for policy violations using AST-based static analysis."""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from .contract_ir import Capability, PromptContractIR, extract_capabilities, parse_prompt_contracts

# Internal effect categories used for conservative mapping (not user-facing syntax).
_EFFECT_FILESYSTEM_WRITE = "filesystem_write"
_EFFECT_FILESYSTEM_READ = "filesystem_read"
_EFFECT_NETWORK = "network"
_EFFECT_SHELL = "shell"
_EFFECT_ENV_READ = "env_read"
_EFFECT_EMAIL = "email"
_EFFECT_SENSITIVE_LOGGING = "sensitive_logging"
_EFFECT_DOMAIN = "domain_records"

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
# Filesystem allowance requires explicit storage wording — not bare "write" in domain
# bullets such as "MAY write refund records".
_FILESYSTEM_CAPABILITY_KEYWORDS = (
    "file",
    "files",
    "filesystem",
    "disk",
    "storage",
    "directory",
    "pathlib",
)
_FILESYSTEM_WRITE_PHRASES = (
    "write file",
    "write files",
    "write to disk",
    "write to the filesystem",
    "files to disk",
    "on disk",
)
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

_STDLIB_NETWORK_CALLS = frozenset(
    {
        "urlopen",
        "urlretrieve",
        "URLopener",
        "FancyURLopener",
        "HTTPConnection",
        "HTTPSConnection",
        "request",
    }
)


def _is_network_module(module: str) -> bool:
    """Return True for third-party and stdlib modules that perform network I/O."""
    if not module:
        return False
    root = module.split(".")[0]
    if root in NETWORK_LIBS:
        return True
    if root == "urllib" or module.startswith("urllib."):
        return True
    if module == "http.client" or module.startswith("http.client"):
        return True
    return False

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
    {
        "remove",
        "unlink",
        "chmod",
        "rmtree",
        "mkdir",
        "rename",
        "replace",
        "write",
        "write_text",
        "write_bytes",
        "touch",
    }
)
PATHLIB_WRITE_METHODS = frozenset(
    {
        "write_text",
        "write_bytes",
        "unlink",
        "rmdir",
        "chmod",
        "touch",
        "mkdir",
        "rename",
        "replace",
    }
)
ENV_METHODS = frozenset({"getenv", "putenv"})
_WRITE_OPEN_MODES = frozenset({"w", "a", "x", "+"})


@dataclass
class PolicyWarning:
    """Authoring-time diagnostic for an unclear capability bullet."""

    message: str
    capability: str
    suggestions: list[str] = field(default_factory=list)
    severity: str = "warning"
    source: str = "capability_parser"
    kind: str = "unmapped_capability"
    line: int = 0


@dataclass
class PolicyIssue:
    category: str
    message: str
    line: int
    col: int
    severity: str = "error"
    kind: str = ""
    source: str = "enforcement"
    effect: str = ""
    suggestions: list[str] = field(default_factory=list)


@dataclass
class PolicyResult:
    target_path: Path
    issues: list[PolicyIssue] = field(default_factory=list)
    capability_warnings: list[PolicyWarning] = field(default_factory=list)
    passed: bool = True
    capabilities: list[Capability] = field(default_factory=list)


@dataclass
class _CapabilityAllowances:
    allowed_network: bool = False
    allowed_shell: bool = False
    allowed_file: bool = False
    allowed_env: bool = False
    allowed_email: bool = False
    may_network_bullets: list[str] = field(default_factory=list)
    block_network_bullets: list[str] = field(default_factory=list)
    may_shell_bullets: list[str] = field(default_factory=list)
    block_shell_bullets: list[str] = field(default_factory=list)
    may_file_bullets: list[str] = field(default_factory=list)
    block_file_bullets: list[str] = field(default_factory=list)
    may_env_bullets: list[str] = field(default_factory=list)
    block_env_bullets: list[str] = field(default_factory=list)
    may_email_bullets: list[str] = field(default_factory=list)
    block_email_bullets: list[str] = field(default_factory=list)
    warnings: list[PolicyWarning] = field(default_factory=list)


_CAPABILITY_SUGGESTIONS: dict[str, list[str]] = {
    _EFFECT_FILESYSTEM_WRITE: [
        "MAY write audit files to disk.",
        "MAY write generated output files to disk.",
    ],
    _EFFECT_FILESYSTEM_READ: [
        "MAY read required local input files.",
        "MAY read configuration files from disk.",
    ],
    _EFFECT_NETWORK: [
        "MAY call the Stripe refund API.",
        "MAY call required external APIs.",
    ],
    _EFFECT_ENV_READ: [
        "MAY read required environment variables.",
    ],
    _EFFECT_EMAIL: [
        "MAY send transactional email notifications.",
    ],
    _EFFECT_SENSITIVE_LOGGING: [
        "MAY log non-sensitive audit events.",
    ],
    "unmapped_capability": [
        "MAY write audit files to disk.",
        "MAY write audit records to the database.",
        "MAY log non-sensitive audit events.",
    ],
}


def suggest_capability_phrases(effect: str) -> list[str]:
    """Return example capability bullets for a supported effect category."""
    return list(_CAPABILITY_SUGGESTIONS.get(effect, _CAPABILITY_SUGGESTIONS["unmapped_capability"]))


def _effect_action_phrase(effect: str) -> str:
    """Short phrase describing what the generated code did for an effect category."""
    phrases = {
        _EFFECT_FILESYSTEM_WRITE: "writes to the filesystem",
        _EFFECT_NETWORK: "makes an external network or API call",
        _EFFECT_ENV_READ: "reads environment variables",
        _EFFECT_SHELL: "runs a shell command",
        _EFFECT_EMAIL: "uses email functionality",
        _EFFECT_SENSITIVE_LOGGING: "may log sensitive values",
    }
    return phrases.get(effect, f"performs a {effect.replace('_', ' ')} side effect")


def _missing_capability_message(effect: str) -> tuple[str, list[str]]:
    """Plain-language denial when code performs an effect with no recognized allowance."""
    suggestions = suggest_capability_phrases(effect)
    action = _effect_action_phrase(effect)
    if effect == _EFFECT_SENSITIVE_LOGGING:
        return (
            "Generated code may log sensitive values, but the capability contract "
            "does not allow logging secrets. If logging is intended, use a clearer "
            "capability such as \"MAY log non-sensitive audit events\"; do not allow "
            "secret logging unless explicitly intended.",
            suggestions,
        )
    return (
        f"Generated code {action}, but no capability allowing this was recognized.",
        suggestions,
    )


def _blocked_by_must_not_remediation() -> list[str]:
    return [
        "Narrow or remove the conflicting MUST NOT capability bullet.",
        "Split the side effect into another module with a clearer capability contract.",
        "Add an inline `# pdd-policy-ignore` or prompt waiver with justification if review accepts the risk.",
    ]


def _denied_effect_diagnostic(
    effect: str,
    *,
    may_bullets: list[str],
    block_bullets: list[str],
) -> tuple[str, str, list[str]]:
    """Return message, issue kind, and remediation suggestions for a denied effect."""
    action = _effect_action_phrase(effect)
    if block_bullets and may_bullets:
        must_not = block_bullets[0]
        may = may_bullets[0]
        message = (
            f"Generated code {action}, but the capability contract blocks this category "
            f'via MUST NOT: "{must_not}". A MAY capability is also present ("{may}") but '
            "does not apply while the MUST NOT blocks this category (deny-wins)."
        )
        return message, "blocked_by_must_not", _blocked_by_must_not_remediation()
    if block_bullets:
        must_not = block_bullets[0]
        message = (
            f"Generated code {action}, but a MUST NOT capability forbids it: "
            f'"{must_not}".'
        )
        return message, "blocked_by_must_not", _blocked_by_must_not_remediation()
    message, suggestions = _missing_capability_message(effect)
    return message, "missing_capability", suggestions


def _may_block_bullets_for_effect(
    allowances: _CapabilityAllowances,
    effect: str,
) -> tuple[list[str], list[str]]:
    """Return (may_bullets, block_bullets) recorded for an effect category."""
    if effect == _EFFECT_NETWORK:
        return allowances.may_network_bullets, allowances.block_network_bullets
    if effect == _EFFECT_SHELL:
        return allowances.may_shell_bullets, allowances.block_shell_bullets
    if effect == _EFFECT_FILESYSTEM_WRITE:
        return allowances.may_file_bullets, allowances.block_file_bullets
    if effect == _EFFECT_ENV_READ:
        return allowances.may_env_bullets, allowances.block_env_bullets
    if effect == _EFFECT_EMAIL:
        return allowances.may_email_bullets, allowances.block_email_bullets
    return [], []


def _unmapped_capability_warning(cap: Capability) -> PolicyWarning:
    text = cap.text.strip()
    suggestions = suggest_capability_phrases("unmapped_capability")
    message = (
        f'Capability bullet could not be mapped to a supported effect category: "{text}".'
    )
    if "persist" in text.lower():
        message += (
            ' "Persist" could mean writing to disk, writing to a database, logging, '
            "or sending to another service."
        )
    message += " Try a clearer phrase such as " + " or ".join(f'"{s}"' for s in suggestions[:2]) + "."
    return PolicyWarning(
        message=message,
        capability=text,
        suggestions=suggestions,
        line=cap.line,
    )


def _bullet_effect_categories(text: str, *, is_must_not: bool) -> frozenset[str]:
    """Map one capability bullet to internal effect categories (conservative)."""
    lower = text.lower()
    categories: set[str] = set()

    if any(kw in lower for kw in _NETWORK_KEYWORDS):
        categories.add(_EFFECT_NETWORK)
    if any(kw in lower for kw in _SHELL_KEYWORDS):
        categories.add(_EFFECT_SHELL)
    if any(kw in lower for kw in _ENV_KEYWORDS):
        categories.add(_EFFECT_ENV_READ)
    if any(kw in lower for kw in _EMAIL_KEYWORDS):
        categories.add(_EFFECT_EMAIL)

    if any(kw in lower for kw in _FILESYSTEM_CAPABILITY_KEYWORDS) or any(
        phrase in lower for phrase in _FILESYSTEM_WRITE_PHRASES
    ):
        categories.add(_EFFECT_FILESYSTEM_WRITE)
    elif "write" in lower and any(
        fs in lower for fs in ("file", "files", "disk", "filesystem", "storage")
    ):
        categories.add(_EFFECT_FILESYSTEM_WRITE)
    if "read" in lower and any(
        fs in lower for fs in ("file", "files", "disk", "filesystem", "path")
    ):
        categories.add(_EFFECT_FILESYSTEM_READ)

    if is_must_not and any(
        word in lower for word in ("secret", "token", "password", "cvv", "pan", "bearer")
    ):
        if "log" in lower or "print" in lower or "leak" in lower:
            categories.add(_EFFECT_SENSITIVE_LOGGING)

    if any(word in lower for word in ("payment", "refund", "record", "customer", "profile")):
        categories.add(_EFFECT_DOMAIN)

    return frozenset(categories)


def _bullet_is_ambiguous(text: str, categories: frozenset[str], *, is_must_not: bool) -> bool:
    """Return True when a bullet's intent is too vague for conservative enforcement."""
    if is_must_not:
        return False
    lower = text.lower()
    if not categories:
        return True

    qualifiers = (
        "file",
        "files",
        "disk",
        "filesystem",
        "database",
        "db",
        "api",
        "http",
        "endpoint",
        "env",
        "environment",
        "email",
        "log",
    )
    for verb in ("persist", "store", "stash", "save", "cache"):
        if verb in lower and not any(q in lower for q in qualifiers):
            return True

    if categories == {_EFFECT_DOMAIN} and any(
        verb in lower for verb in ("persist", "store", "stash", "save")
    ):
        return True

    return False


def analyze_capability_allowances(capabilities: list[Capability]) -> _CapabilityAllowances:
    """Derive conservative allowances and authoring warnings from capability bullets.

    For each effect category, an unambiguous ``MUST NOT`` blocks the category even when a
    later ``MAY`` bullet would otherwise allow it (deny-wins, order-independent).
    """
    allowances = _CapabilityAllowances()
    may_network = False
    may_shell = False
    may_file = False
    may_env = False
    may_email = False
    block_network = False
    block_shell = False
    block_file = False
    block_env = False
    block_email = False

    for cap in capabilities:
        categories = _bullet_effect_categories(cap.text, is_must_not=cap.is_must_not)
        if _bullet_is_ambiguous(cap.text, categories, is_must_not=cap.is_must_not):
            allowances.warnings.append(_unmapped_capability_warning(cap))
            continue

        bullet = cap.text.strip()
        if cap.is_must_not:
            if _EFFECT_NETWORK in categories:
                block_network = True
                allowances.block_network_bullets.append(bullet)
            if _EFFECT_SHELL in categories:
                block_shell = True
                allowances.block_shell_bullets.append(bullet)
            if _EFFECT_FILESYSTEM_WRITE in categories:
                block_file = True
                allowances.block_file_bullets.append(bullet)
            if _EFFECT_ENV_READ in categories:
                block_env = True
                allowances.block_env_bullets.append(bullet)
            if _EFFECT_EMAIL in categories:
                block_email = True
                allowances.block_email_bullets.append(bullet)
            continue

        if _EFFECT_NETWORK in categories:
            may_network = True
            allowances.may_network_bullets.append(bullet)
        if _EFFECT_SHELL in categories:
            may_shell = True
            allowances.may_shell_bullets.append(bullet)
        if _EFFECT_FILESYSTEM_WRITE in categories:
            may_file = True
            allowances.may_file_bullets.append(bullet)
        if _EFFECT_ENV_READ in categories:
            may_env = True
            allowances.may_env_bullets.append(bullet)
        if _EFFECT_EMAIL in categories:
            may_email = True
            allowances.may_email_bullets.append(bullet)

    allowances.allowed_network = may_network and not block_network
    allowances.allowed_shell = may_shell and not block_shell
    allowances.allowed_file = may_file and not block_file
    allowances.allowed_env = may_env and not block_env
    allowances.allowed_email = may_email and not block_email
    return allowances


class PolicyVisitor(ast.NodeVisitor):
    def __init__(
        self,
        capabilities: list[Capability],
        *,
        allowances: Optional[_CapabilityAllowances] = None,
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
        self.path_instance_names: set[str] = set()

        self.has_capabilities = len(capabilities) > 0
        self.should_check = self.strict or self.has_capabilities

        resolved = allowances or analyze_capability_allowances(capabilities)
        self.allowances = resolved
        self.allowed_network = resolved.allowed_network
        self.allowed_shell = resolved.allowed_shell
        self.allowed_file = resolved.allowed_file
        self.allowed_env = resolved.allowed_env
        self.allowed_email = resolved.allowed_email

    def _prompt_waiver_matches(
        self,
        category: str,
        message: str,
        *,
        kind: str = "",
        effect: str = "",
    ) -> bool:
        if not self.prompt_ir or not self.prompt_ir.waivers:
            return False
        cat = category.lower()
        msg = message.lower()
        kind_lower = kind.lower()
        effect_phrase = effect.replace("_", " ").lower()
        legacy_phrases = {
            "network": (
                "unauthorized network",
                "network library",
                "external call",
                "blocked_by_must_not",
            ),
            "file": ("unauthorized file", "filesystem", "file operation", "file writes"),
            "env": ("unauthorized environment", "environment access", "environ"),
            "shell": ("unauthorized shell", "shell execution"),
            "email": ("unauthorized email", "email library"),
            "leakage": ("sensitive data", "logging secrets", "leakage"),
        }
        for waiver in self.prompt_ir.waivers:
            block = f"{waiver.raw_block}\n{waiver.reason}".lower()
            if cat not in block:
                continue
            if msg in block or (kind_lower and kind_lower in block):
                return True
            if effect_phrase and effect_phrase in block:
                return True
            if any(phrase in block for phrase in legacy_phrases.get(cat, ())):
                return True
        return False

    def _is_waived(
        self,
        node: ast.AST,
        category: str,
        message: str,
        *,
        kind: str = "",
        effect: str = "",
    ) -> bool:
        if hasattr(node, "lineno") and node.lineno <= len(self.source_lines):
            line_text = self.source_lines[node.lineno - 1]
            if "# pdd-policy-ignore" in line_text:
                return True
            if node.lineno > 1 and "# pdd-policy-ignore" in self.source_lines[node.lineno - 2]:
                return True

        return self._prompt_waiver_matches(category, message, kind=kind, effect=effect)

    def _add_issue(
        self,
        node: ast.AST,
        category: str,
        message: str,
        *,
        effect: str = "",
        suggestions: Optional[list[str]] = None,
        kind: str = "",
    ) -> None:
        if not self.should_check or self._is_waived(
            node, category, message, kind=kind, effect=effect
        ):
            return
        lineno = getattr(node, "lineno", 0) or 0
        col = getattr(node, "col_offset", 0) or 0
        self.issues.append(
            PolicyIssue(
                category=category,
                message=message,
                line=lineno,
                col=col,
                kind=kind or ("missing_capability" if effect else ""),
                effect=effect,
                suggestions=list(suggestions or []),
            )
        )

    def _add_missing_capability(self, node: ast.AST, category: str, effect: str) -> None:
        may_bullets, block_bullets = _may_block_bullets_for_effect(self.allowances, effect)
        message, kind, suggestions = _denied_effect_diagnostic(
            effect,
            may_bullets=may_bullets,
            block_bullets=block_bullets,
        )
        self._add_issue(
            node,
            category,
            message,
            effect=effect,
            suggestions=suggestions,
            kind=kind,
        )

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            self._check_import(alias.name, node)
            self.imported_names[alias.asname or alias.name] = alias.name
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        if node.module:
            self._check_import(node.module, node)
            for alias in node.names:
                local = alias.asname or alias.name
                if node.module == "os" and alias.name in {"environ", "environb"}:
                    self.imported_names[local] = f"os.{alias.name}"
                elif node.module == "pathlib" and alias.name == "Path":
                    self.imported_names[local] = "pathlib"
                else:
                    self.imported_names[local] = node.module
        self.generic_visit(node)

    def _check_import(self, module: str, node: ast.AST) -> None:
        base_module = module.split(".")[0]
        if _is_network_module(module) and not self.allowed_network:
            self._add_missing_capability(node, "network", _EFFECT_NETWORK)
        if base_module in {"smtplib", "email"} and not self.allowed_email:
            self._add_missing_capability(node, "email", _EFFECT_EMAIL)
        if base_module in SHELL_LIBS and not self.allowed_shell and base_module != "os":
            self._add_missing_capability(node, "shell", _EFFECT_SHELL)

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

    def _pathlib_open_single_arg_is_write_mode(self, node: ast.Call) -> bool:
        if len(node.args) != 1 or not isinstance(node.args[0], ast.Constant):
            return False
        value = node.args[0].value
        if not isinstance(value, str):
            return False
        return any(flag in value for flag in _WRITE_OPEN_MODES)

    def _resolve_bound_module(self, name: str) -> str:
        """Map a local name to its imported module root (e.g. ``Path`` -> ``pathlib``)."""
        bound = self.imported_names.get(name, name)
        if bound in {"pathlib", "os"}:
            return bound
        if bound.startswith("os."):
            return "os"
        return bound.split(".")[0]

    def _pathlib_constructor_call(self, call_node: ast.Call) -> bool:
        func = call_node.func
        if isinstance(func, ast.Name):
            return self._resolve_bound_module(func.id) == "pathlib"
        if (
            isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and self._resolve_bound_module(func.value.id) == "pathlib"
            and func.attr == "Path"
        ):
            return True
        return False

    def _name_is_path_instance(self, name: str) -> bool:
        return name in self.path_instance_names

    def _check_path_instance_call(self, node: ast.Call, *, var_name: str, func_name: str) -> None:
        if func_name in PATHLIB_WRITE_METHODS:
            self._check_file_operation(node, label=f"{var_name}.{func_name}")
        elif func_name == "open" and (
            self._open_looks_like_write(node) or self._pathlib_open_single_arg_is_write_mode(node)
        ):
            self._check_file_operation(node, label=f"{var_name}.open()")

    def visit_Assign(self, node: ast.Assign) -> None:
        if isinstance(node.value, ast.Call) and self._pathlib_constructor_call(node.value):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    self.path_instance_names.add(target.id)
        self.generic_visit(node)

    def _check_file_operation(
        self,
        node: ast.Call,
        *,
        label: str,
    ) -> None:
        if not self.allowed_file:
            self._add_missing_capability(node, "file", _EFFECT_FILESYSTEM_WRITE)

    def _call_module_root(self, module_name: str) -> str:
        """Resolve a call's module prefix through import aliases (e.g. ``o`` -> ``os``)."""
        if not module_name:
            return ""
        return self._resolve_bound_module(module_name.split(".")[0])

    def visit_Call(self, node: ast.Call) -> None:
        func_name = ""
        module_name = ""
        resolved_module = ""

        if isinstance(node.func, ast.Attribute):
            if isinstance(node.func.value, ast.Name):
                module_name = node.func.value.id
                func_name = node.func.attr
            elif isinstance(node.func.value, ast.Call):
                func_name = node.func.attr
            elif isinstance(node.func.value, ast.Attribute) and isinstance(
                node.func.value.value, ast.Name
            ):
                module_name = f"{node.func.value.value.id}.{node.func.value.attr}"
                func_name = node.func.attr
        elif isinstance(node.func, ast.Name):
            func_name = node.func.id
            module_name = self.imported_names.get(func_name, "")

        resolved_module = self._call_module_root(module_name)

        if not self.allowed_network:
            bound_module = self.imported_names.get(func_name, module_name)
            if _is_network_module(bound_module) or _is_network_module(module_name):
                if func_name in _STDLIB_NETWORK_CALLS or func_name == "urlopen":
                    self._add_missing_capability(node, "network", _EFFECT_NETWORK)

        if (resolved_module == "os" and func_name in SHELL_METHODS) or (
            resolved_module == "subprocess"
        ) or (func_name == "system" and not resolved_module):
            if not self.allowed_shell:
                self._add_missing_capability(node, "shell", _EFFECT_SHELL)

        if (resolved_module == "os" and func_name in FILE_WRITE_METHODS) or (
            resolved_module == "shutil" and func_name in FILE_WRITE_METHODS
        ):
            label = f"{module_name}.{func_name}" if module_name else func_name
            self._check_file_operation(node, label=label)
        elif func_name == "open":
            is_pathlib_open = (
                isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Call)
                and self._pathlib_constructor_call(node.func.value)
            )
            if is_pathlib_open and (
                self._open_looks_like_write(node)
                or self._pathlib_open_single_arg_is_write_mode(node)
            ):
                self._check_file_operation(node, label="Path(...).open()")
            elif isinstance(node.func, ast.Name) and self._open_looks_like_write(node):
                self._check_file_operation(node, label="open() write mode")
        elif (
            isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Call)
            and self._pathlib_constructor_call(node.func.value)
            and (
                func_name in PATHLIB_WRITE_METHODS
                or (
                    func_name == "open"
                    and (
                        self._open_looks_like_write(node)
                        or self._pathlib_open_single_arg_is_write_mode(node)
                    )
                )
            )
        ):
            self._check_file_operation(node, label=f"Path(...).{func_name}")
        elif (
            isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and self._resolve_bound_module(node.func.value.id) == "pathlib"
            and func_name in PATHLIB_WRITE_METHODS
        ):
            label = f"{node.func.value.id}.{func_name}"
            self._check_file_operation(node, label=label)
        elif (
            isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and self._name_is_path_instance(node.func.value.id)
        ):
            self._check_path_instance_call(
                node,
                var_name=node.func.value.id,
                func_name=func_name,
            )

        if (resolved_module == "os" and func_name in ENV_METHODS) or (
            func_name in ENV_METHODS
            and not resolved_module
            and self._call_module_root(self.imported_names.get(func_name, "")) == "os"
        ):
            if not self.allowed_env:
                self._add_missing_capability(node, "env", _EFFECT_ENV_READ)

        if func_name in {"debug", "info", "warning", "error", "critical", "log", "print"}:
            self._check_sensitive_args(list(node.args), node)
            for keyword in node.keywords:
                self._check_sensitive_args([keyword.value], node)

        if isinstance(node.func, ast.Attribute) and func_name == "format":
            self._check_sensitive_args(list(node.args) + [kw.value for kw in node.keywords], node)

        if isinstance(node.func, ast.Attribute) and func_name in {"Mod", "mod"}:
            self._check_sensitive_args(list(node.args), node)

        self.generic_visit(node)

    def _env_access_label(self, node: ast.Attribute) -> Optional[str]:
        if node.attr not in {"environ", "environb"}:
            return None
        if isinstance(node.value, ast.Name):
            root = self._resolve_bound_module(node.value.id)
            if root == "os":
                return f"{node.value.id}.{node.attr}"
        return None

    def visit_Attribute(self, node: ast.Attribute) -> None:
        env_label = self._env_access_label(node)
        if env_label and not self.allowed_env:
            self._add_missing_capability(node, "env", _EFFECT_ENV_READ)
        self.generic_visit(node)

    def visit_Subscript(self, node: ast.Subscript) -> None:
        if isinstance(node.value, ast.Name):
            bound = self.imported_names.get(node.value.id, "")
            if bound in {"os.environ", "os.environb"} and not self.allowed_env:
                self._add_missing_capability(node, "env", _EFFECT_ENV_READ)
        elif isinstance(node.value, ast.Attribute):
            env_label = self._env_access_label(node.value)
            if env_label and not self.allowed_env:
                self._add_missing_capability(node, "env", _EFFECT_ENV_READ)
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
                self._add_missing_capability(node, "leakage", _EFFECT_SENSITIVE_LOGGING)
            elif isinstance(arg, ast.Attribute) and self._name_is_sensitive(arg.attr):
                self._add_missing_capability(node, "leakage", _EFFECT_SENSITIVE_LOGGING)
            elif isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                if self._name_is_sensitive(arg.value) and ("=" in arg.value or ":" in arg.value):
                    self._add_missing_capability(node, "leakage", _EFFECT_SENSITIVE_LOGGING)
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

    allowances = (
        analyze_capability_allowances(capabilities) if capabilities else _CapabilityAllowances()
    )
    visitor = PolicyVisitor(
        capabilities,
        allowances=allowances,
        strict=strict,
        source_lines=source_lines,
        prompt_ir=prompt_ir,
    )
    visitor.visit(tree)
    passed = len(visitor.issues) == 0
    return PolicyResult(
        target_path,
        visitor.issues,
        capability_warnings=allowances.warnings,
        passed=passed,
        capabilities=capabilities,
    )


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
