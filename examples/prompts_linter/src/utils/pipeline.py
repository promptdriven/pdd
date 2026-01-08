import logging
from pathlib import Path
from typing import Optional, Dict, List
from pydantic import BaseModel, Field

# Import internal modules based on the provided architecture
from src.utils.models import (
    Report,
    Issue,
    Severity,
    RuleCategory,
    LLMResponse,
    LLMSuggestionDetail
)
from src.utils import rules
from src.utils import llm
from src.utils import fix
from src.utils import helpers

# Configure logger
logger = logging.getLogger(__name__)

class LintConfig(BaseModel):
    """
    Configuration for the linting pipeline.
    Controls runtime behavior for LLM usage, fix generation, and thresholds.
    """
    use_llm: bool = Field(default=True, description="Whether to attempt LLM-based analysis.")
    generate_fix: bool = Field(default=False, description="Whether to generate a fixed version of the prompt.")
    llm_timeout: int = Field(default=30, description="Timeout in seconds for LLM requests.")
    llm_model_override: Optional[str] = Field(default=None, description="Specific LLM model to use.")
    
    # Scoring weights based on PDD Guide
    weights: Dict[str, int] = Field(
        default_factory=lambda: {
            "modularity": 30,
            "contracts": 20,
            "context": 20,
            "determinism": 15,
            "abstraction": 15
        }
    )

class PipelineReport(Report):
    """
    Extended Report model for the pipeline to include generated fixes.
    Subclasses Report to satisfy type hints while adding the optional field.
    """
    suggested_fix: Optional[str] = Field(default=None, description="Auto-generated fix scaffold.")

def _calculate_score(issues: List[Issue], weights: Dict[str, int]) -> int:
    """
    Calculates the final score (0-100) based on the weighted rubric.
    
    Logic:
    - Start with full points for each category.
    - ERROR: Reduces category score to 0.
    - WARNING: Reduces category score by 50%.
    - INFO: No deduction.
    """
    # Initialize scores with max weight
    category_scores = {
        RuleCategory.MODULARITY: weights.get("modularity", 30),
        RuleCategory.CONTRACTS: weights.get("contracts", 20),
        RuleCategory.CONTEXT: weights.get("context", 20),
        RuleCategory.DETERMINISM: weights.get("determinism", 15),
        RuleCategory.ANATOMY: weights.get("abstraction", 15), # Mapping Anatomy to Abstraction
        # Map ATTENTION to Context bucket if it appears, or treat as Context
        RuleCategory.ATTENTION: weights.get("context", 20), 
    }
    
    # Track deductions
    # We use a multiplier approach: 1.0 = full score, 0.5 = half score, 0.0 = zero score
    category_multipliers = {cat: 1.0 for cat in category_scores}

    for issue in issues:
        cat = issue.category
        
        # Handle categories that might not be in our map (fallback to Context or ignore)
        if cat not in category_multipliers:
            # Try to map string representation if enum matching fails
            found = False
            for known_cat in category_multipliers:
                # Check if cat is an Enum with .value or just a string/value
                cat_val = getattr(cat, 'value', cat)
                if known_cat.value == cat_val:
                    cat = known_cat
                    found = True
                    break
            if not found:
                continue

        if issue.severity == Severity.ERROR:
            category_multipliers[cat] = 0.0
        elif issue.severity == Severity.WARNING:
            # If already 0.0 (Error), stay 0.0. If 1.0, go to 0.5. If 0.5, stay 0.5.
            if category_multipliers[cat] > 0.5:
                category_multipliers[cat] = 0.5

    # Calculate final sum
    total_score = 0.0
    
    # We need to handle the specific mapping of categories to the 100 point total.
    # Since ATTENTION and CONTEXT share the "Context" weight in this logic,
    # we need to be careful not to double count.
    # Simplified approach: We sum the distinct buckets defined in the PDD guide.
    
    # 1. Modularity
    total_score += category_scores[RuleCategory.MODULARITY] * category_multipliers[RuleCategory.MODULARITY]
    
    # 2. Contracts
    total_score += category_scores[RuleCategory.CONTRACTS] * category_multipliers[RuleCategory.CONTRACTS]
    
    # 3. Context (combining Context and Attention logic)
    # If either Context or Attention has an error, the Context score is 0.
    ctx_mult = min(category_multipliers.get(RuleCategory.CONTEXT, 1.0), 
                   category_multipliers.get(RuleCategory.ATTENTION, 1.0))
    total_score += weights.get("context", 20) * ctx_mult
    
    # 4. Determinism
    total_score += category_scores[RuleCategory.DETERMINISM] * category_multipliers[RuleCategory.DETERMINISM]
    
    # 5. Abstraction (Anatomy)
    total_score += category_scores[RuleCategory.ANATOMY] * category_multipliers[RuleCategory.ANATOMY]

    return int(round(total_score))

def _map_llm_suggestion_to_issue(suggestion: LLMSuggestionDetail) -> Issue:
    """Converts an LLM suggestion into a standard Issue object."""
    # Default to Context category for LLM suggestions if not inferable
    category = RuleCategory.CONTEXT
    
    # Simple heuristic to map rule_id prefixes to categories
    rid = suggestion.rule_id.upper()
    if rid.startswith("MOD"): category = RuleCategory.MODULARITY
    elif rid.startswith("CON"): category = RuleCategory.CONTRACTS
    elif rid.startswith("DET"): category = RuleCategory.DETERMINISM
    elif rid.startswith("ANA") or rid.startswith("STR"): category = RuleCategory.ANATOMY
    
    return Issue(
        rule_id=suggestion.rule_id,
        line_number=1, # LLM issues are often global or hard to pinpoint line numbers without diffing
        severity=Severity.WARNING, # LLM suggestions are usually warnings, not hard errors
        category=category,
        title=suggestion.title,
        description=suggestion.rationale,
        fix_suggestion=f"Change '{suggestion.before}' to '{suggestion.after}'"
    )

def lint_text(text: str, config: Optional[LintConfig] = None) -> Report:
    """
    Orchestrates the linting process for a raw string of text.
    
    1. Runs deterministic heuristics.
    2. Runs LLM analysis (if enabled).
    3. Calculates score.
    4. Generates fixes (if enabled).
    """
    if config is None:
        config = LintConfig()

    issues: List[Issue] = []
    llm_response: Optional[LLMResponse] = None
    
    # 1. Heuristic Execution (Deterministic)
    try:
        heuristic_issues = rules.analyze_text(text)
        issues.extend(heuristic_issues)
    except Exception as e:
        logger.error(f"Error during heuristic analysis: {e}")
        # We continue, but add a system issue
        issues.append(Issue(
            rule_id="SYS001",
            line_number=1,
            severity=Severity.ERROR,
            category=RuleCategory.ANATOMY,
            title="System Error",
            description=f"Heuristic analysis failed: {str(e)}",
            fix_suggestion="Check system logs."
        ))
    
    # 2. LLM Integration
    if config.use_llm:
        llm_config = {
            "timeout": config.llm_timeout,
            "model": config.llm_model_override
        }
        
        # analyze_prompt handles exceptions internally and returns None on failure
        llm_response = llm.analyze_prompt(text, config=llm_config)
        
        if llm_response:
            # Merge LLM suggestions into issues
            if llm_response.suggestions:
                for sugg in llm_response.suggestions:
                    issues.append(_map_llm_suggestion_to_issue(sugg))
        else:
            # Graceful degradation: Log it, maybe add an INFO issue
            logger.warning("LLM analysis skipped or failed (returned None).")
            issues.append(Issue(
                rule_id="SYS002",
                line_number=1,
                severity=Severity.INFO,
                category=RuleCategory.CONTEXT,
                title="LLM Analysis Skipped",
                description="AI-based analysis was unavailable. Report is based on heuristics only.",
                fix_suggestion="Check API keys and network connection."
            ))

    # 3. Scoring
    score = _calculate_score(issues, config.weights)
    
    # Generate Summary
    summary = "Analysis complete."
    if llm_response and llm_response.guide_alignment_summary:
        summary = llm_response.guide_alignment_summary
    elif issues:
        error_count = sum(1 for i in issues if i.severity == Severity.ERROR)
        summary = f"Found {len(issues)} issues ({error_count} errors)."

    # 4. Construct Report
    # Use PipelineReport to allow attaching suggested_fix
    report = PipelineReport(
        filepath="<memory>", # Placeholder, updated by lint_file if used
        score=score,
        issues=issues,
        summary=summary,
        llm_analysis=llm_response
    )

    # 5. Fix Generation
    if config.generate_fix:
        try:
            # Check if the function exists before calling it to avoid AttributeError
            if hasattr(fix, 'generate_scaffold'):
                fixed_content = fix.generate_scaffold(text, report)
                report.suggested_fix = fixed_content
            else:
                # Fallback or log if the expected API is missing
                logger.warning("fix.generate_scaffold not found. Skipping fix generation.")
                report.issues.append(Issue(
                    rule_id="SYS003",
                    line_number=1,
                    severity=Severity.WARNING,
                    category=RuleCategory.ANATOMY,
                    title="Fix Generation Unavailable",
                    description="The fix module does not support scaffold generation.",
                    fix_suggestion="Update the fix module."
                ))
        except Exception as e:
            logger.error(f"Fix generation failed: {e}")
            report.issues.append(Issue(
                rule_id="SYS003",
                line_number=1,
                severity=Severity.WARNING,
                category=RuleCategory.ANATOMY,
                title="Fix Generation Failed",
                description=f"Could not generate scaffold: {str(e)}",
                fix_suggestion=""
            ))

    return report

def lint_file(path: Path, config: Optional[LintConfig] = None) -> Report:
    """
    Wrapper around lint_text that handles file I/O.
    Uses src.utils.helpers.read_file_content for consistent normalization.
    """
    if config is None:
        config = LintConfig()

    # 1. Read Content using helpers
    try:
        # helpers.read_file_content handles existence checks and normalization
        content = helpers.read_file_content(str(path))
    except FileNotFoundError:
        return PipelineReport(
            filepath=str(path),
            score=0,
            issues=[Issue(
                rule_id="SYS004",
                line_number=1,
                severity=Severity.ERROR,
                category=RuleCategory.ANATOMY,
                title="File Not Found",
                description=f"The file at {path} does not exist.",
                fix_suggestion="Check the file path."
            )],
            summary="Fatal Error: File not found."
        )
    except (IOError, PermissionError) as e:
        return PipelineReport(
            filepath=str(path),
            score=0,
            issues=[Issue(
                rule_id="SYS005",
                line_number=1,
                severity=Severity.ERROR,
                category=RuleCategory.ANATOMY,
                title="Read Error",
                description=f"Could not read file: {str(e)}",
                fix_suggestion="Check file permissions and encoding."
            )],
            summary="Fatal Error: Could not read file."
        )
    except Exception as e:
        # Catch-all for unexpected errors during read
        return PipelineReport(
            filepath=str(path),
            score=0,
            issues=[Issue(
                rule_id="SYS006",
                line_number=1,
                severity=Severity.ERROR,
                category=RuleCategory.ANATOMY,
                title="System Error",
                description=f"Unexpected error reading file: {str(e)}",
                fix_suggestion="Check system logs."
            )],
            summary="Fatal Error: Unexpected system error."
        )

    # 2. Delegate to lint_text
    report = lint_text(content, config)
    
    # Update filepath in the report
    report.filepath = str(path)
    
    return report