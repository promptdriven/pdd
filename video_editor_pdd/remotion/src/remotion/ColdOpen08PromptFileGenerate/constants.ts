// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const PANEL_BG = "#11111B";
export const PANEL_BORDER = "#2D2D3D";
export const TEXT_PRIMARY = "#CDD6F4";
export const TEXT_MUTED = "#94A3B8";
export const TEXT_DIM = "#6C7086";
export const ACCENT_BLUE = "#89B4FA";
export const ACCENT_GREEN = "#A6E3A1";
export const BRIGHT_GREEN = "#22C55E";

// ── Syntax highlight colors ─────────────────────────────────────────
export const SYN_KEYWORD = "#CBA6F7"; // purple for def, class, import, return, etc.
export const SYN_STRING = "#A6E3A1"; // green for strings
export const SYN_COMMENT = "#6C7086"; // dim for comments
export const SYN_BUILTIN = "#89B4FA"; // blue for built-in names
export const SYN_DECORATOR = "#F9E2AF"; // yellow for decorators
export const SYN_NUMBER = "#FAB387"; // orange for numbers
export const SYN_OPERATOR = "#89DCEB"; // teal for operators
export const SYN_DEFAULT = "#CDD6F4"; // default text

// ── Layout ──────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const PROMPT_PANEL = { x: 100, y: 80, width: 760, height: 520 };
export const TERMINAL_PANEL = { x: 900, y: 80, width: 920, height: 920 };
export const ARROW_POS = { x: 860, y: 340 };

// ── Font ────────────────────────────────────────────────────────────
export const MONO_FONT = "'JetBrains Mono', 'Fira Code', 'Cascadia Code', monospace";
export const SANS_FONT = "'Inter', -apple-system, sans-serif";

// ── Timing (frames) ────────────────────────────────────────────────
export const TOTAL_FRAMES = 150;
export const PROMPT_FADE_END = 20;
export const ARROW_START = 20;
export const ARROW_FADE_END = 30;
export const TERMINAL_START = 25;
export const TERMINAL_FADE_END = 35;
export const CMD_START = 40;
export const CMD_TEXT = "$ pdd generate email_validator";
export const CMD_FRAMES_PER_CHAR = 2;
export const CODE_STREAM_START = 50;
export const CODE_STREAM_END = 130;
export const RESULT_START = 130;
export const TOTAL_CODE_LINES = 200;

// ── Prompt file content ─────────────────────────────────────────────
export const PROMPT_LINES: { text: string; highlighted: boolean }[] = [
  { text: "# email_validator.prompt", highlighted: false },
  { text: "", highlighted: false },
  { text: "Validate email format using RFC 5322", highlighted: true },
  { text: "Support international domain names (IDN)", highlighted: true },
  { text: "Handle plus-addressing (user+tag@domain)", highlighted: true },
  { text: "", highlighted: false },
  { text: "Return detailed error messages including:", highlighted: true },
  { text: "  - Missing @ symbol", highlighted: false },
  { text: "  - Invalid domain format", highlighted: false },
  { text: "  - Exceeds 254 character limit", highlighted: false },
  { text: "", highlighted: false },
  { text: "Check DNS MX records for domain verification", highlighted: true },
  { text: "Support batch validation from CSV input", highlighted: true },
  { text: "Output results as structured JSON", highlighted: true },
  { text: "Include confidence score per validation", highlighted: true },
];

// ── Python code lines (representative ~200 lines) ────────────────
function generatePythonCode(): string[] {
  const lines: string[] = [
    '"""Email Validator — RFC 5322 compliant."""',
    "",
    "import re",
    "import dns.resolver",
    "import json",
    "import csv",
    "import sys",
    "from dataclasses import dataclass, field",
    "from typing import Optional, List, Dict",
    "from pathlib import Path",
    "",
    "",
    "@dataclass",
    "class ValidationResult:",
    '    """Result of a single email validation."""',
    "    email: str",
    "    is_valid: bool",
    "    confidence: float",
    '    errors: List[str] = field(default_factory=list)',
    '    warnings: List[str] = field(default_factory=list)',
    "",
    "    def to_dict(self) -> Dict:",
    "        return {",
    '            "email": self.email,',
    '            "is_valid": self.is_valid,',
    '            "confidence": self.confidence,',
    '            "errors": self.errors,',
    '            "warnings": self.warnings,',
    "        }",
    "",
    "",
    "# RFC 5322 compliant pattern",
    "RFC_5322_PATTERN = re.compile(",
    "    r\"^[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+\"",
    '    r"@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}"',
    '    r"[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9]"',
    '    r"(?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$"',
    ")",
    "",
    "MAX_EMAIL_LENGTH = 254",
    "MAX_LOCAL_LENGTH = 64",
    "MAX_DOMAIN_LENGTH = 253",
    "",
    "",
    "class EmailValidator:",
    '    """Full-featured email validator with IDN support."""',
    "",
    "    def __init__(self, check_dns: bool = True):",
    "        self.check_dns = check_dns",
    "        self._dns_cache: Dict[str, bool] = {}",
    "",
    "    def validate(self, email: str) -> ValidationResult:",
    '        """Validate a single email address."""',
    "        errors: List[str] = []",
    "        warnings: List[str] = []",
    "        confidence = 1.0",
    "",
    "        # Check length constraints",
    "        if len(email) > MAX_EMAIL_LENGTH:",
    "            errors.append(",
    '                f"Email exceeds {MAX_EMAIL_LENGTH} character limit"',
    "            )",
    "            confidence = 0.0",
    "",
    '        # Check for @ symbol',
    '        if "@" not in email:',
    "            errors.append(\"Missing @ symbol\")",
    "            return ValidationResult(",
    "                email=email,",
    "                is_valid=False,",
    "                confidence=0.0,",
    "                errors=errors,",
    "            )",
    "",
    '        local, domain = email.rsplit("@", 1)',
    "",
    "        # Validate local part",
    "        if len(local) > MAX_LOCAL_LENGTH:",
    "            errors.append(",
    '                f"Local part exceeds {MAX_LOCAL_LENGTH} chars"',
    "            )",
    "            confidence *= 0.3",
    "",
    "        # Handle plus-addressing",
    '        if "+" in local:',
    '            base_local = local.split("+")[0]',
    "            if not base_local:",
    '                errors.append("Empty local part before +")',
    "",
    "        # Validate domain",
    "        if len(domain) > MAX_DOMAIN_LENGTH:",
    "            errors.append(",
    '                f"Domain exceeds {MAX_DOMAIN_LENGTH} chars"',
    "            )",
    "",
    "        # IDN support — encode to ASCII",
    "        try:",
    '            ascii_domain = domain.encode("idna").decode("ascii")',
    "        except (UnicodeError, UnicodeDecodeError):",
    '            errors.append("Invalid international domain")',
    "            ascii_domain = domain",
    "            confidence *= 0.5",
    "",
    "        # RFC 5322 pattern check",
    '        test_email = f"{local}@{ascii_domain}"',
    "        if not RFC_5322_PATTERN.match(test_email):",
    '            errors.append("Does not match RFC 5322 format")',
    "            confidence *= 0.2",
    "",
    "        # DNS MX record check",
    "        if self.check_dns and not errors:",
    "            has_mx = self._check_mx(ascii_domain)",
    "            if not has_mx:",
    "                warnings.append(",
    '                    "No MX records found for domain"',
    "                )",
    "                confidence *= 0.6",
    "",
    "        is_valid = len(errors) == 0",
    "        return ValidationResult(",
    "            email=email,",
    "            is_valid=is_valid,",
    "            confidence=round(confidence, 2),",
    "            errors=errors,",
    "            warnings=warnings,",
    "        )",
    "",
    "    def _check_mx(self, domain: str) -> bool:",
    '        """Check DNS MX records with caching."""',
    "        if domain in self._dns_cache:",
    "            return self._dns_cache[domain]",
    "        try:",
    '            records = dns.resolver.resolve(domain, "MX")',
    "            has_mx = len(records) > 0",
    "        except (dns.resolver.NXDOMAIN,",
    "                dns.resolver.NoAnswer,",
    "                dns.resolver.NoNameservers):",
    "            has_mx = False",
    "        self._dns_cache[domain] = has_mx",
    "        return has_mx",
    "",
    "    def validate_batch(",
    "        self, emails: List[str]",
    "    ) -> List[ValidationResult]:",
    '        """Validate a list of emails."""',
    "        return [self.validate(e) for e in emails]",
    "",
    "",
    "def load_from_csv(filepath: str) -> List[str]:",
    '    """Load emails from CSV file."""',
    "    emails: List[str] = []",
    '    with open(filepath, "r") as f:',
    "        reader = csv.reader(f)",
    "        for row in reader:",
    "            if row and row[0].strip():",
    "                emails.append(row[0].strip())",
    "    return emails",
    "",
    "",
    "def output_json(",
    "    results: List[ValidationResult],",
    "    pretty: bool = True,",
    ") -> str:",
    '    """Format results as JSON output."""',
    "    data = {",
    '        "total": len(results),',
    '        "valid": sum(1 for r in results if r.is_valid),',
    '        "invalid": sum(',
    "            1 for r in results if not r.is_valid",
    "        ),",
    '        "results": [r.to_dict() for r in results],',
    "    }",
    "    return json.dumps(",
    "        data, indent=2 if pretty else None",
    "    )",
    "",
    "",
    'def main() -> None:',
    '    """CLI entry point."""',
    "    validator = EmailValidator(check_dns=True)",
    "",
    "    if len(sys.argv) > 1:",
    "        filepath = Path(sys.argv[1])",
    "        if filepath.suffix == \".csv\":",
    "            emails = load_from_csv(str(filepath))",
    "        else:",
    "            emails = [sys.argv[1]]",
    "    else:",
    "        emails = [",
    '            "user@example.com",',
    '            "test+tag@domain.org",',
    '            "invalid@",',
    '            "user@münchen.de",',
    '            "a" * 255 + "@test.com",',
    "        ]",
    "",
    "    results = validator.validate_batch(emails)",
    "    print(output_json(results))",
    "",
    "    # Summary",
    "    valid = sum(1 for r in results if r.is_valid)",
    '    print(f"\\n--- Summary ---")',
    '    print(f"Total: {len(results)}")',
    '    print(f"Valid: {valid}")',
    '    print(f"Invalid: {len(results) - valid}")',
    "",
    "",
    'if __name__ == "__main__":',
    "    main()",
  ];

  // Pad to 200 lines
  while (lines.length < 200) {
    lines.push("");
  }
  return lines.slice(0, 200);
}

export const PYTHON_CODE_LINES = generatePythonCode();
