from dataclasses import dataclass
from typing import Optional
import re


@dataclass
class ValidationResult:
    """
    Result of an email validation operation.

    Attributes:
        is_valid: Whether the email is valid according to the rules.
        normalized_email: The lowercase, whitespace-stripped version of the input email.
        error_message: Description of the error if invalid, None if valid.
    """
    is_valid: bool
    normalized_email: str
    error_message: Optional[str] = None


class EmailValidator:
    """
    A validator for email addresses enforcing specific structural rules.

    Internal implementation details (not part of public API):
        - EMAIL_PATTERN: Compiled regex for basic structure validation
        - _normalize(): Strips whitespace and lowercases
        - _check_local_part(): Validates the part before @
        - _check_domain(): Validates the part after @
        - _has_consecutive_dots(): Checks for .. pattern
    """

    # Internal: regex pattern for basic email structure
    EMAIL_PATTERN = re.compile(r'^[^@\s]+@[^@\s]+\.[^@\s]+$')

    def validate_email(self, email: str) -> ValidationResult:
        """
        Validates an email address and returns a ValidationResult.

        Args:
            email: The email address to validate.

        Returns:
            ValidationResult with validation status and normalized email.

        Raises:
            TypeError: If email is None.
        """
        if email is None:
            raise TypeError("email cannot be None")

        normalized_email = self._normalize(email)

        # Edge case: Empty string (after stripping)
        if not normalized_email:
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized_email,
                error_message="Email cannot be empty"
            )

        # Check for consecutive dots
        if self._has_consecutive_dots(normalized_email):
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized_email,
                error_message="Email cannot contain consecutive dots"
            )

        # Must contain exactly one @ symbol
        at_count = normalized_email.count("@")
        if at_count != 1:
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized_email,
                error_message="Email must contain exactly one @ symbol"
            )

        # Split into local and domain parts
        local_part, domain_part = normalized_email.split("@")

        # Validate local part
        if not self._check_local_part(local_part):
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized_email,
                error_message="Local part cannot be empty"
            )

        # Validate domain part
        if not self._check_domain(domain_part):
            return ValidationResult(
                is_valid=False,
                normalized_email=normalized_email,
                error_message="Domain must contain at least one dot"
            )

        # If all checks pass
        return ValidationResult(
            is_valid=True,
            normalized_email=normalized_email,
            error_message=None
        )

    def _normalize(self, email: str) -> str:
        """Internal: Normalize email by stripping whitespace and lowercasing."""
        return email.strip().lower()

    def _check_local_part(self, local_part: str) -> bool:
        """Internal: Check if the local part (before @) is valid."""
        return len(local_part) > 0

    def _check_domain(self, domain_part: str) -> bool:
        """Internal: Check if the domain part (after @) has at least one dot."""
        return "." in domain_part

    def _has_consecutive_dots(self, email: str) -> bool:
        """Internal: Check if email contains consecutive dots."""
        return ".." in email