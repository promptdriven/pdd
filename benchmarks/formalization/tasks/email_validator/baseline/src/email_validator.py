"""Reference implementation for email_validator benchmark task (A2 baseline)."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional


@dataclass
class ValidationResult:
    """Result of email validation."""

    is_valid: bool
    normalized_email: str
    error_message: Optional[str] = None


class EmailValidator:
    """Validates email addresses per the benchmark specification."""

    def validate_email(self, email: str) -> ValidationResult:
        if email is None:
            raise TypeError("email cannot be None")

        normalized = email.strip().lower()
        if not normalized:
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized,
                error_message="Email cannot be empty",
            )
        if ".." in normalized:
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized,
                error_message="Email cannot contain consecutive dots",
            )
        if normalized.count("@") != 1:
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized,
                error_message="Email must contain exactly one @ symbol",
            )
        local, domain = normalized.split("@", 1)
        if not local:
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized,
                error_message="Local part cannot be empty",
            )
        if "." not in domain:
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized,
                error_message="Domain must contain at least one dot",
            )
        return ValidationResult(
            is_valid=True,
            normalized_email=normalized,
            error_message=None,
        )
