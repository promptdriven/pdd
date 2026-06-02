"""Core logic for scanning Python code for policy violations using AST-based static analysis."""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Set, Any

from .contract_ir import Capability, PromptContractIR, extract_capabilities, parse_prompt_contracts

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
    issues: List[PolicyIssue] = field(default_factory=list)
    passed: bool = True
    capabilities: List[Capability] = field(default_factory=list)

NETWORK_LIBS = {
    "urllib3", "paramiko", "httpx", "requests", "aiohttp", "socket", "ftplib",
    "telnetlib", "smtplib"
}

SHELL_LIBS = {"subprocess", "os", "shutil", "pty"}

SENSITIVE_KEYS = {
    "token", "secret", "password", "api_key", "cvv", "pan", "bearer"
}

# Detection patterns for Requirement 5 & 6
SHELL_METHODS = {"system", "popen", "spawnl", "spawnv", "spawnlp", "spawnvp"}
FILE_WRITE_METHODS = {"remove", "unlink", "chmod", "rmtree", "mkdir", "rename", "replace"}
ENV_METHODS = {"getenv", "putenv"}

class PolicyVisitor(ast.NodeVisitor):
    def __init__(self, capabilities: List[Capability], strict: bool = False, source_lines: List[str] = None, prompt_ir: Optional[PromptContractIR] = None):
        self.capabilities = capabilities
        self.strict = strict
        self.source_lines = source_lines or []
        self.prompt_ir = prompt_ir
        self.issues: List[PolicyIssue] = []
        self.imported_names: dict[str, str] = {}  # name -> module_name
        
        # Check if we should even run checks
        self.has_capabilities = len(capabilities) > 0
        self.should_check = self.strict or self.has_capabilities

        # Conflicting modal handling: MUST NOT takes absolute precedence
        def is_allowed(category_keywords: List[str]) -> bool:
            # Check for MUST NOT first
            for c in capabilities:
                if c.is_must_not and any(kw in c.text.lower() for kw in category_keywords):
                    return False
            # Check for MAY/SHOULD
            for c in capabilities:
                if not c.is_must_not and any(kw in c.text.lower() for kw in category_keywords):
                    return True
            return False

        self.allowed_network = is_allowed(["network", "api"])
        self.allowed_shell = is_allowed(["shell", "command"])
        self.allowed_file = is_allowed(["file", "write", "delete"])
        self.allowed_env = is_allowed(["env", "environment"])

    def _is_waived(self, node: ast.AST, category: str, message: str) -> bool:
        # 1. Inline waivers (Requirement 9)
        if node.lineno <= len(self.source_lines):
            line_text = self.source_lines[node.lineno - 1]
            if "# pdd-policy-ignore" in line_text:
                return True
            # Check previous line for waiver too
            if node.lineno > 1:
                prev_line = self.source_lines[node.lineno - 2]
                if "# pdd-policy-ignore" in prev_line:
                    return True

        # 2. Prompt-level waivers (Requirement 10)
        if self.prompt_ir and self.prompt_ir.waivers:
            for waiver in self.prompt_ir.waivers:
                # Simple heuristic: if the waiver reason or block contains the message or category
                if category.lower() in waiver.raw_block.lower() or category.lower() in waiver.reason.lower():
                    return True
        
        return False

    def _add_issue(self, node: ast.AST, category: str, message: str):
        if not self.should_check:
            return
        if self._is_waived(node, category, message):
            return
        self.issues.append(PolicyIssue(category, message, node.lineno, node.col_offset))

    def visit_Import(self, node: ast.Import):
        for alias in node.names:
            self._check_import(alias.name, node)
            # Track top-level module name
            self.imported_names[alias.asname or alias.name] = alias.name
        self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom):
        if node.module:
            self._check_import(node.module, node)
            for alias in node.names:
                # Track imported name -> module
                self.imported_names[alias.asname or alias.name] = node.module
        self.generic_visit(node)

    def _check_import(self, module: str, node: ast.AST):
        base_module = module.split('.')[0]
        if base_module in NETWORK_LIBS and not self.allowed_network:
            self._add_issue(node, "network", f"Unauthorized network library import: {module}")
        if base_module in SHELL_LIBS and not self.allowed_shell and base_module != "os":
            self._add_issue(node, "shell", f"Unauthorized shell library import: {module}")

    def visit_Call(self, node: ast.Call):
        # Detect function calls (Requirement 5, 6, 7)
        func_name = ""
        module_name = ""

        if isinstance(node.func, ast.Attribute):
            if isinstance(node.func.value, ast.Name):
                module_name = node.func.value.id
                func_name = node.func.attr
            elif isinstance(node.func.value, ast.Attribute):
                # Handle nested attributes like os.path.join
                if isinstance(node.func.value.value, ast.Name):
                    module_name = f"{node.func.value.value.id}.{node.func.value.attr}"
                    func_name = node.func.attr
        elif isinstance(node.func, ast.Name):
            func_name = node.func.id
            module_name = self.imported_names.get(func_name, "")

        # Shell execution (Requirement 5)
        is_shell = (
            (module_name == "os" and func_name in SHELL_METHODS) or
            (module_name == "subprocess") or
            (func_name == "system" and not module_name) or
            (module_name == "os.path" and func_name == "join" and not self.allowed_file) # os.path.join is usually fine but can be part of file ops
        )
        # Refined shell check
        if (module_name == "os" and func_name in SHELL_METHODS) or \
           (module_name == "subprocess") or \
           (func_name == "system" and not module_name):
            if not self.allowed_shell:
                self._add_issue(node, "shell", f"Unauthorized shell execution: {module_name}.{func_name}" if module_name else f"Unauthorized shell execution: {func_name}")

        # File operations (Requirement 5)
        if (module_name == "os" and func_name in FILE_WRITE_METHODS) or \
           (module_name == "shutil" and func_name in FILE_WRITE_METHODS) or \
           (func_name == "open" and not module_name):
            if not self.allowed_file:
                self._add_issue(node, "file", f"Unauthorized file operation: {module_name}.{func_name}" if module_name else f"Unauthorized file operation: {func_name}")

        # Environment access (Requirement 6)
        if (module_name == "os" and func_name in ENV_METHODS) or \
           (func_name in ENV_METHODS and not module_name and self.imported_names.get(func_name) == "os"):
            if not self.allowed_env:
                self._add_issue(node, "env", f"Unauthorized environment access: {module_name}.{func_name}" if module_name else f"Unauthorized environment access: {func_name}")

        # Logging/Print leaks (Requirement 7)
        is_logging = func_name in {"debug", "info", "warning", "error", "critical", "log", "print"}
        if is_logging:
            self._check_sensitive_args(node.args, node)
            for keyword in node.keywords:
                self._check_sensitive_args([keyword.value], node)

        self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute):
        # Detect os.environ access (Requirement 6)
        module_name = ""
        if isinstance(node.value, ast.Name):
            module_name = node.value.id
        
        if module_name == "os" and node.attr in {"environ", "environb"}:
            if not self.allowed_env:
                self._add_issue(node, "env", f"Unauthorized environment access: os.{node.attr}")
        self.generic_visit(node)

    def _check_sensitive_args(self, args: List[ast.AST], node: ast.AST):
        for arg in args:
            # Check variable names
            if isinstance(arg, ast.Name):
                if any(key in arg.id.lower() for key in SENSITIVE_KEYS):
                    self._add_issue(node, "leakage", f"Potential sensitive data leakage: {arg.id}")
            
            # Check attribute access (e.g., user.token)
            elif isinstance(arg, ast.Attribute):
                if any(key in arg.attr.lower() for key in SENSITIVE_KEYS):
                    self._add_issue(node, "leakage", f"Potential sensitive data leakage: {arg.attr}")

            # Check string literals (f-strings, etc.)
            elif isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                if any(key in arg.value.lower() for key in SENSITIVE_KEYS):
                    # Only flag if it looks like it might contain a secret value, e.g. "token=..."
                    if "=" in arg.value or ":" in arg.value:
                        self._add_issue(node, "leakage", f"Potential sensitive data in string: {arg.value[:20]}...")
            
            elif isinstance(arg, ast.JoinedStr): # f-strings
                for value in arg.values:
                    if isinstance(value, ast.FormattedValue):
                        # Recursively check the expression within the f-string
                        self._check_sensitive_args([value.value], node)

def run_policy_check(target_path: Path, prompt_path: Optional[Path] = None, strict: bool = False) -> PolicyResult:
    """Run policy check on a file."""
    try:
        content = target_path.read_text(encoding="utf-8")
        source_lines = content.splitlines()
        tree = ast.parse(content)
    except Exception as e:
        return PolicyResult(
            target_path,
            [PolicyIssue("system", f"Failed to parse or read file: {e}", 0, 0)],
            passed=False,
        )

    capabilities = []
    prompt_ir = None
    if prompt_path and prompt_path.exists():
        prompt_ir = parse_prompt_contracts(prompt_path)
        if "capabilities" in prompt_ir.sections:
            capabilities = extract_capabilities(prompt_ir.sections["capabilities"])

    visitor = PolicyVisitor(capabilities, strict=strict, source_lines=source_lines, prompt_ir=prompt_ir)
    visitor.visit(tree)
    
    passed = len(visitor.issues) == 0
    return PolicyResult(target_path, visitor.issues, passed=passed, capabilities=capabilities)
