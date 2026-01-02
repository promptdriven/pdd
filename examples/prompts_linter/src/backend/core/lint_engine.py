"""
src/backend/core/lint_engine.py

The central orchestrator of the PDD Prompt Linter.
This module coordinates parsing, include resolution, and rule execution
to produce a standardized LintReport.
"""

import logging
from typing import List, Dict, Optional, Any

from src.backend.models.findings import (
    LintReport,
    Finding,
    Severity,
    Evidence,
    Summary,
    IssueCounts
)
from src.backend.core.parser import PromptParser, ParsedPrompt
from src.backend.rules.registry import default_registry as registry
from src.backend.core.include_resolver import IncludeResolver

# Configure logging
logger = logging.getLogger(__name__)

class LintEngine:
    """
    Orchestrates the linting workflow: Parsing -> Resolution -> Rule Execution -> Reporting.
    This class is stateless; each call to lint() is independent.
    """

    def __init__(self):
        self.parser = PromptParser()
        # registry is accessed via the imported default_registry
        self.resolver = IncludeResolver()

    def lint(
        self, 
        content: str, 
        file_path: str = "stdin", 
        options: Optional[Dict[str, Any]] = None
    ) -> LintReport:
        """
        Main entry point for linting a prompt.
        """
        if options is None:
            options = {}

        resolve_includes = options.get("resolve_includes", False)
        
        findings: List[Finding] = []
        token_count_estimate = 0
        
        # --- Step 1: Parse ---
        try:
            parsed_prompt = self.parser.parse(content)
        except Exception as e:
            logger.error(f"Parsing failed for {file_path}: {str(e)}")
            # Return immediate failure report
            fatal_finding = Finding(
                rule_id="parser_critical_error",
                title="Critical Parsing Failure",
                message=f"Parsing failed: {str(e)}",
                severity=Severity.ERROR,
                evidence=Evidence(line_start=1, line_end=1)
            )
            return self._build_report(file_path, [fatal_finding], 0, 0)

        # Add parser-detected syntax errors if any (assuming parser implementation supports this)
        if hasattr(parsed_prompt, 'syntax_errors') and parsed_prompt.syntax_errors:
            findings.extend(parsed_prompt.syntax_errors)

        # --- Step 2: Resolve Includes ---
        if resolve_includes:
            try:
                # Use the new resolve method on IncludeResolver
                resolution_result = self.resolver.resolve(parsed_prompt, base_path=file_path)
                findings.extend(resolution_result.findings)
                token_count_estimate = resolution_result.total_tokens
            except Exception as e:
                logger.error(f"Include resolution failed: {str(e)}")
                findings.append(Finding(
                    rule_id="include_resolution_error",
                    title="Include Resolution Failed",
                    message=f"Failed to resolve includes: {str(e)}",
                    severity=Severity.ERROR,
                    evidence=Evidence(line_start=1, line_end=1)
                ))
        else:
            # Simple estimate if no resolution
            token_count_estimate = len(content) // 4

        # --- Step 3: Load Rules ---
        rules = registry.get_all_rules()

        # --- Step 4: Execute Rules ---
        for rule in rules:
            try:
                if options.get("disabled_rules") and rule.rule_id in options["disabled_rules"]:
                    continue

                # Use .check() alias or .analyze()
                if hasattr(rule, 'check'):
                    rule_findings = rule.check(parsed_prompt)
                else:
                    rule_findings = rule.analyze(parsed_prompt)
                
                findings.extend(rule_findings)
                
            except Exception as e:
                logger.exception(f"Rule {rule.rule_id} crashed: {e}")
                findings.append(Finding(
                    rule_id="internal_linter_error",
                    title="Internal Linter Error",
                    message=f"Rule '{rule.rule_id}' crashed unexpectedly: {str(e)}",
                    severity=Severity.WARN, # Use WARN not WARNING
                    evidence=Evidence(line_start=1, line_end=1)
                ))

        # --- Step 5: Score & Summarize ---
        score = self._calculate_score(findings)
        
        return self._build_report(file_path, findings, score, token_count_estimate)

    def _build_report(self, filename: str, findings: List[Finding], score: int, tokens: int) -> LintReport:
        # Calculate counts
        error_count = sum(1 for f in findings if f.severity == Severity.ERROR)
        warn_count = sum(1 for f in findings if f.severity == Severity.WARN)
        info_count = sum(1 for f in findings if f.severity == Severity.INFO)
        
        summary = Summary(
            score=score,
            issue_counts=IssueCounts(error=error_count, warn=warn_count, info=info_count),
            token_count_estimate=tokens
        )
        
        return LintReport(
            filename=filename,
            summary=summary,
            findings=findings
        )

    def _calculate_score(self, findings: List[Finding]) -> int:
        score = 100
        error_deduction = 0
        warn_deduction = 0
        info_deduction = 0

        for f in findings:
            if f.severity == Severity.ERROR:
                error_deduction += 15
            elif f.severity == Severity.WARN:
                warn_deduction += 7
            elif f.severity == Severity.INFO:
                info_deduction += 2

        score -= (min(error_deduction, 45) + min(warn_deduction, 35) + min(info_deduction, 20))
        return max(0, score)