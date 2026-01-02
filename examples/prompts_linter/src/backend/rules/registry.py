"""
src/backend/rules/registry.py

This module serves as the central catalog for all Prompt-Driven Development (PDD)
linting rules. It defines the standard interface that all rules must implement
and provides a registry mechanism to manage rule registration, retrieval, and
validation.
"""

import abc
import inspect
from typing import Any, Dict, List, Type, Optional, Union, Callable
from src.backend.models.findings import Finding

# Allowed severity levels for validation
ALLOWED_SEVERITIES = {"error", "warn", "info"}


class LintRule(abc.ABC):
    """
    Abstract base class that all PDD linting rules must implement.

    Attributes:
        rule_id (str): Unique identifier for the rule (e.g., "PDD001").
        severity (str): Default severity level ("error", "warn", "info").
        title (str): Short descriptive title of the rule.
    """

    rule_id: str
    severity: str
    title: str

    def __init__(self):
        self._validate_metadata()

    def _validate_metadata(self):
        """Validates the rule metadata upon instantiation."""
        if not hasattr(self, 'rule_id') or not self.rule_id:
            # Skip validation for functional wrappers if they don't set it immediately
            if self.__class__.__name__ == "FunctionalRule": return
            raise ValueError(f"Rule class {self.__class__.__name__} must define a 'rule_id'.")
        
        if not hasattr(self, 'severity') or self.severity not in ALLOWED_SEVERITIES:
             if self.__class__.__name__ == "FunctionalRule": return
             raise ValueError(
                f"Rule {self.rule_id} has invalid severity '{getattr(self, 'severity', None)}'. "
                f"Allowed: {ALLOWED_SEVERITIES}"
            )

    @abc.abstractmethod
    def analyze(self, prompt_structure: Any) -> List[Finding]:
        """
        Analyzes the parsed prompt structure to identify rule violations.
        """
        pass

    # Alias for compatibility with lint_engine
    def check(self, prompt_structure: Any) -> List[Finding]:
        return self.analyze(prompt_structure)
    
    @property
    def id(self):
        return self.rule_id


class FunctionalRule(LintRule):
    """Adapter to wrap a function as a LintRule."""
    def __init__(self, func: Callable):
        self.func = func
        self.rule_id = "UNKNOWN"
        self.severity = "info"
        self.title = func.__name__
        
        # Try to extract ID from name (e.g. check_pdd001_role)
        parts = func.__name__.split('_')
        for part in parts:
            if part.upper().startswith("PDD"):
                self.rule_id = part.upper()
                break
        
        # We don't call super().__init__ to skip strict metadata validation 
        # because functions might not define severity/title declaratively.

    def analyze(self, prompt_structure: Any) -> List[Finding]:
        return self.func(prompt_structure)


class RuleRegistry:
    """
    Manages the registration and retrieval of LintRules.
    """

    def __init__(self):
        self._rules: Dict[str, LintRule] = {}

    def register_rule(self, rule_obj: Union[Type[LintRule], Callable]) -> Union[Type[LintRule], Callable]:
        """
        Registers a rule class or function.
        """
        instance = None
        
        if inspect.isclass(rule_obj) and issubclass(rule_obj, LintRule):
            # Class-based rule
            try:
                instance = rule_obj()
            except TypeError as e:
                raise TypeError(f"Cannot instantiate rule {rule_obj.__name__}: {e}")
        elif callable(rule_obj):
            # Function-based rule
            instance = FunctionalRule(rule_obj)
        else:
            raise TypeError(f"Object {rule_obj} must be a LintRule subclass or callable.")

        if instance.rule_id in self._rules:
            # Allow overwriting or raise error? 
            # For now raise error to catch duplicates
            # But FunctionalRule might have UNKNOWN id if naming convention fails
            if instance.rule_id != "UNKNOWN":
                 raise ValueError(f"Rule ID '{instance.rule_id}' is already registered.")

        self._rules[instance.rule_id] = instance
        return rule_obj

    def get_rule(self, rule_id: str) -> Optional[LintRule]:
        return self._rules.get(rule_id)

    def get_all_rules(self) -> List[LintRule]:
        return sorted(self._rules.values(), key=lambda r: r.rule_id)

    def clear(self):
        self._rules.clear()


# Global registry instance
default_registry = RuleRegistry()


def register(rule_obj: Union[Type[LintRule], Callable]) -> Union[Type[LintRule], Callable]:
    """
    Decorator to register a LintRule or function with the default registry.
    """
    return default_registry.register_rule(rule_obj)
