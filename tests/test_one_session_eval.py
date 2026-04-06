"""
Automated regression/eval suite for PDD's one-session sync mega-prompt.

Runs each scenario with BOTH the improved (current) and original prompt,
then uses LLM-as-judge to compare which version performed better.

Markers: @pytest.mark.e2e, @pytest.mark.integration
Requires: PDD_RUN_AGENTIC_TESTS=1 and an agentic CLI (claude/gemini/codex)
"""

from __future__ import annotations

import difflib
import json
import os
import re
import subprocess
import sys
import textwrap
import time
from concurrent.futures import ThreadPoolExecutor, Future
from pathlib import Path
from typing import Any, Dict, List, Optional

import pytest
from pydantic import BaseModel, Field

# ---------------------------------------------------------------------------
# Markers
# ---------------------------------------------------------------------------
pytestmark = [pytest.mark.e2e, pytest.mark.integration]

# ---------------------------------------------------------------------------
# Skip logic
# ---------------------------------------------------------------------------

def _skip_unless_agentic():
    if not os.environ.get("PDD_RUN_AGENTIC_TESTS"):
        pytest.skip("Set PDD_RUN_AGENTIC_TESTS=1 to run one-session eval tests")
    from pdd.agentic_common import get_available_agents
    if not get_available_agents():
        pytest.skip("No agentic CLI available (claude/gemini/codex)")


@pytest.fixture(autouse=True)
def _require_agentic_env():
    _skip_unless_agentic()


# ---------------------------------------------------------------------------
# Pydantic score models (LLM-as-judge output)
# ---------------------------------------------------------------------------

class DimensionVerdict(BaseModel):
    """Verdict for a single comparison dimension."""
    winner: str = Field(description="'current', 'original', or 'tie'")
    one_line: str = Field(
        description="One-sentence summary of why this winner was chosen (max 120 chars). "
        "Must cite specific evidence (file names, test counts, dollar amounts)."
    )
    explanation: str = Field(
        description="Full explanation with specific evidence from the outputs."
    )


class ComparativeResult(BaseModel):
    """Side-by-side comparison of improved vs original prompt on one scenario."""

    test_quality: DimensionVerdict = Field(
        description="Compare test quality: coverage of spec requirements, assertion strength, "
        "edge case handling. Look at the actual test files side by side."
    )
    example_quality: DimensionVerdict = Field(
        description="Compare example quality: does it demonstrate the module well? "
        "Is it clean and readable?"
    )
    minimality: DimensionVerdict = Field(
        description="Compare how surgical the changes were. Which version made fewer "
        "unnecessary modifications to files that didn't need changing?"
    )
    correctness: DimensionVerdict = Field(
        description="Compare correctness: did each version change the RIGHT file? "
        "Did either modify code when it should have fixed tests, or vice versa?"
    )
    cost: DimensionVerdict = Field(
        description="Compare cost. Use the dollar amounts provided."
    )
    speed: DimensionVerdict = Field(
        description="Compare wall-clock time. Use the times provided."
    )
    overall: DimensionVerdict = Field(
        description="Overall winner considering correctness, test_quality, example_quality, "
        "and minimality only. Do NOT factor in cost or speed."
    )
    agent_issues_current: str = Field(
        description="From the sync stdout: describe any loops, stuck behavior, "
        "bad decisions, or wasted iterations by the agent using the current prompt. "
        "Say 'none' if the agent performed cleanly."
    )
    agent_issues_original: str = Field(
        description="Same analysis for the original prompt's agent run."
    )
    prompt_improvement_suggestions: str = Field(
        description="Based on the comparison, suggest specific changes to the current prompt "
        "that could address any issues observed. Say 'none' if no improvements needed."
    )


# ---------------------------------------------------------------------------
# Module-level cost tracker
# ---------------------------------------------------------------------------
_COST_TRACKER: Dict[str, Dict[str, Any]] = {}

# ---------------------------------------------------------------------------
# Path to old prompt fixture
# ---------------------------------------------------------------------------
_ORIGINAL_PROMPT_PATH = (
    Path(__file__).parent / "fixtures" / "one_session_eval"
    / "one_session_agent_LLM_original.prompt"
)

# ---------------------------------------------------------------------------
# .pddrc template
# ---------------------------------------------------------------------------
PDDRC_CONTENT = textwrap.dedent("""\
    version: "1.0"
    contexts:
      default:
        defaults:
          generate_output_path: "src/"
          test_output_path: "tests/"
          example_output_path: "examples/"
          default_language: "python"
          target_coverage: 90.0
          strength: 0.818
          temperature: 0.0
          budget: 10.0
          max_attempts: 3
""")

# ---------------------------------------------------------------------------
# Evaluator prompts (for LLM-as-judge)
# ---------------------------------------------------------------------------
COMPARATIVE_EVALUATOR_PROMPT = textwrap.dedent("""\
    You are an expert evaluator comparing two versions of an LLM prompt template.

    ## Your task

    Two versions of a mega-prompt template were each given the SAME scenario (same starting
    files, same module spec). The only difference is the instructions each agent received.
    You must decide which version produced better results across several dimensions.

    - **Version A ("current")**: The prompt being actively developed
    - **Version B ("original")**: The old baseline prompt
    
    The mega-prompt requires an agent to sync up the code, test, and example files 
    to align with the prompt file for this scenario.

    ## Scenario
    {scenario_description}

    ## Expected behavior
    {expected_behavior}

    ## What to look for in this scenario
    {evaluation_guidance}

    ## Reference files (starting state before either version ran)
    {reference_files}

    ## Version A (current) results
    Cost: ${current_cost:.4f} | Time: {current_time:.1f}s | Sync exit: {current_exit}
    Tests: exit {current_test_exit} | Test count: {current_test_count}
    Example: exit {current_example_exit}

    Changes made (unified diff against reference files):
    {current_diffs}

    New files created by this version (full content):
    {current_new_files}

    Sync stdout (contains agent progress markers, fix attempts, and phase transitions):
    {current_stdout}

    ## Version B (original) results
    Cost: ${original_cost:.4f} | Time: {original_time:.1f}s | Sync exit: {original_exit}
    Tests: exit {original_test_exit} | Test count: {original_test_count}
    Example: exit {original_example_exit}

    Changes made (unified diff against reference files):
    {original_diffs}

    New files created by this version (full content):
    {original_new_files}

    Sync stdout:
    {original_stdout}

    ## Evaluation instructions

    For EACH dimension below, you must:
    1. Quote or cite specific evidence from the outputs above (file names, test function names,
       line numbers, dollar amounts, timestamps, stdout markers)
    2. State which version is better and why, or declare a tie with justification
    3. Use the labels "current", "original", or "tie" — not "A" or "B"
    4. Provide BOTH a one_line summary (max ~120 chars, with key evidence) AND a full explanation

    Do NOT make judgments based on assumptions. Only use what is present in the outputs above.
    If a file is missing or a run failed, that is itself evidence — do not speculate about
    what it would have produced.

    ### Dimensions

    **test_quality**: Compare the test files. Which covers more spec requirements?
    Which uses stronger assertions? Which tests more edge cases? Cite specific test functions.

    **example_quality**: Compare the example files. Which better demonstrates the module's API?

    **minimality**: Which made fewer unnecessary changes? Did either rewrite correct files?

    **correctness**: Did each version change the RIGHT file? The spec is the authority.
    Did either introduce new bugs?

    **cost**: Which cost less? (Lower is better.)

    **speed**: Which completed faster? (Lower is better.)

    **overall**: Weigh all dimensions. Only consider correctness, test_quality,
    example_quality, and minimality. Do NOT factor in cost or speed for the overall
    winner — those are reported separately for informational purposes only.

    ### Agent behavior analysis

    Examine the sync stdout for BOTH versions. Look for concrete evidence of:
    - `crash_fix_attempt` or `test_fix_attempt` markers appearing 3+ times (looping)
    - The agent repeating the same file edit or command
    - Modifying the wrong file (code vs tests)
    - Writing then immediately overwriting a file

    Report what you find for each version. Say "none observed" if the stdout shows clean
    execution with no wasted steps.

    ### Prompt improvement suggestions

    Based on problems you observed in the CURRENT version's behavior, suggest 1-3 specific
    changes to the current prompt that would fix those problems. Each suggestion must reference
    the concrete behavior you observed. Say "none" if the current version performed cleanly.
""")


# =========================================================================
# Inline scenario data — S1 through S6
# =========================================================================

S1_ALL_IN_SYNC = {
    "basename": "text_stats",
    "description": (
        "S1: All In Sync. Everything is already aligned — correct code, "
        "working example, 26 passing tests. The agent should preserve what works and "
        "only make additive improvements."
    ),
    "expected_behavior": (
        "Agent preserves all existing tests (26+) and the working code. "
        "It may add new tests or improve the example — that is fine. "
        "It must NOT delete or rewrite existing passing tests. All tests pass. Example runs."
    ),
    "evaluation_guidance": (
        "The key question is: did the agent PRESERVE what was already working? "
        "Adding tests on top of the existing 26 is fine. Improving the example is fine. "
        "What is NOT acceptable: "
        "- Rewriting tests/test_text_stats.py from scratch (losing existing coverage) "
        "- Reducing the test count below 26 "
        "- Making unnecessary changes to src/text_stats.py (code was already correct) "
        "- Introducing new test failures "
        "Compare the test count: reference has 26 tests. Final should have >= 26. "
        "Compare src/text_stats.py — were there any code changes? (there should be none) "
        "The agent that best preserves existing work while optionally improving it wins."
    ),
    "files": {
        "prompts/text_stats_python.prompt": textwrap.dedent("""\
            % Goal
            Write the `text_stats` module for computing statistics about text strings.

            % Requirements
            1. Function `word_count(text: str) -> int`: Returns the number of whitespace-separated words in the text. Empty or whitespace-only strings return 0.
            2. Function `char_count(text: str, ignore_whitespace: bool = False) -> int`: Returns the total number of characters. When `ignore_whitespace` is True, whitespace characters are excluded from the count.
            3. Function `sentence_count(text: str) -> int`: Returns the number of sentences, detected by splitting on `.`, `!`, and `?` followed by whitespace or end-of-string. Empty strings return 0.
            4. Function `average_word_length(text: str) -> float`: Returns the mean character length of all words. Returns 0.0 if the text contains no words.
            5. Function `most_common_words(text: str, n: int = 5) -> list[tuple[str, int]]`: Returns the `n` most frequently occurring words (case-insensitive) as (word, count) tuples, sorted by count descending then alphabetically. Words are stripped of leading/trailing punctuation before counting.
            6. Function `reading_time_minutes(text: str, wpm: int = 200) -> float`: Estimates reading time in minutes based on word count divided by words-per-minute. Returns 0.0 for empty text. Raises ValueError if wpm <= 0.

            % Dependencies
            Standard library only: `re`, `string`, `collections`.

            % Deliverables
            - Module at `src/text_stats.py` exporting `word_count`, `char_count`, `sentence_count`, `average_word_length`, `most_common_words`, `reading_time_minutes`.
        """),
        "src/text_stats.py": textwrap.dedent('''\
            """Text statistics module for computing metrics about text strings."""

            from __future__ import annotations

            import re
            import string
            from collections import Counter
            from typing import List, Tuple


            def word_count(text: str) -> int:
                """Return the number of whitespace-separated words in *text*."""
                words = text.split()
                return len(words)


            def char_count(text: str, ignore_whitespace: bool = False) -> int:
                """Return the total character count.

                When *ignore_whitespace* is True whitespace characters are excluded.
                """
                if ignore_whitespace:
                    return sum(1 for ch in text if not ch.isspace())
                return len(text)


            def sentence_count(text: str) -> int:
                """Return the number of sentences in *text*.

                Sentences are delimited by \'.\', \'!\' or \'?\' followed by whitespace or
                end-of-string.
                """
                if not text or not text.strip():
                    return 0
                parts = re.split(r\'[.!?](?:\\s|$)\', text)
                return sum(1 for p in parts if p.strip())


            def average_word_length(text: str) -> float:
                """Return the mean character length of all words in *text*.

                Returns 0.0 when the text contains no words.
                """
                words = text.split()
                if not words:
                    return 0.0
                return sum(len(w) for w in words) / len(words)


            def most_common_words(
                text: str, n: int = 5
            ) -> List[Tuple[str, int]]:
                """Return the *n* most common words (case-insensitive).

                Words are stripped of leading/trailing punctuation before counting.
                Results are sorted by count descending, then alphabetically.
                """
                words = text.lower().split()
                cleaned = [w.strip(string.punctuation) for w in words]
                cleaned = [w for w in cleaned if w]
                counts = Counter(cleaned)
                ranked = sorted(counts.items(), key=lambda item: (-item[1], item[0]))
                return ranked[:n]


            def reading_time_minutes(text: str, wpm: int = 200) -> float:
                """Estimate reading time in minutes.

                Raises ValueError if *wpm* is not positive.
                """
                if wpm <= 0:
                    raise ValueError("wpm must be positive")
                words = word_count(text)
                if words == 0:
                    return 0.0
                return words / wpm
        '''),
        "tests/test_text_stats.py": textwrap.dedent('''\
            """
            Test plan for text_stats module:
            1. word_count: empty string, whitespace-only, normal text, multiple spaces
            2. char_count: normal text, ignore_whitespace=False, ignore_whitespace=True, empty string
            3. sentence_count: empty string, single sentence, multiple sentences with . ! ?
            4. average_word_length: empty string returns 0.0, normal text, single word
            5. most_common_words: normal text, n parameter, case insensitivity, punctuation stripping, alphabetical tiebreaker
            6. reading_time_minutes: normal text, empty text returns 0.0, custom wpm, wpm <= 0 raises ValueError
            """

            import pytest
            import sys
            import os

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.text_stats import (
                word_count,
                char_count,
                sentence_count,
                average_word_length,
                most_common_words,
                reading_time_minutes,
            )


            class TestWordCount:
                def test_empty_string(self):
                    assert word_count("") == 0

                def test_whitespace_only(self):
                    assert word_count("   ") == 0

                def test_normal_text(self):
                    assert word_count("hello world") == 2

                def test_multiple_spaces(self):
                    assert word_count("hello   world   foo") == 3


            class TestCharCount:
                def test_normal_text(self):
                    assert char_count("hello") == 5

                def test_with_whitespace(self):
                    assert char_count("hello world") == 11

                def test_ignore_whitespace_false(self):
                    assert char_count("hello world", ignore_whitespace=False) == 11

                def test_ignore_whitespace_true(self):
                    assert char_count("hello world", ignore_whitespace=True) == 10

                def test_empty_string(self):
                    assert char_count("") == 0


            class TestSentenceCount:
                def test_empty_string(self):
                    assert sentence_count("") == 0

                def test_single_sentence(self):
                    assert sentence_count("Hello world.") == 1

                def test_multiple_sentences(self):
                    assert sentence_count("Hello. World! How?") == 3

                def test_whitespace_only(self):
                    assert sentence_count("   ") == 0


            class TestAverageWordLength:
                def test_empty_string(self):
                    assert average_word_length("") == 0.0

                def test_normal_text(self):
                    assert average_word_length("hi there") == 3.5

                def test_single_word(self):
                    assert average_word_length("hello") == 5.0


            class TestMostCommonWords:
                def test_basic(self):
                    result = most_common_words("the cat and the dog", n=2)
                    assert result == [("the", 2), ("and", 1)]

                def test_case_insensitive(self):
                    result = most_common_words("Hello hello HELLO", n=1)
                    assert result == [("hello", 3)]

                def test_punctuation_stripping(self):
                    result = most_common_words("hello, hello! world.", n=2)
                    assert result == [("hello", 2), ("world", 1)]

                def test_alphabetical_tiebreaker(self):
                    result = most_common_words("apple banana cherry", n=3)
                    assert result == [("apple", 1), ("banana", 1), ("cherry", 1)]

                def test_default_n(self):
                    result = most_common_words("a b c d e f g")
                    assert len(result) == 5


            class TestReadingTimeMinutes:
                def test_normal_text(self):
                    text = " ".join(["word"] * 200)
                    assert reading_time_minutes(text) == 1.0

                def test_empty_text(self):
                    assert reading_time_minutes("") == 0.0

                def test_custom_wpm(self):
                    text = " ".join(["word"] * 100)
                    assert reading_time_minutes(text, wpm=100) == 1.0

                def test_zero_wpm_raises(self):
                    with pytest.raises(ValueError):
                        reading_time_minutes("hello", wpm=0)

                def test_negative_wpm_raises(self):
                    with pytest.raises(ValueError):
                        reading_time_minutes("hello", wpm=-5)
        '''),
        "examples/text_stats_example.py": textwrap.dedent('''\
            """Example demonstrating the text_stats module."""

            import os
            import sys

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.text_stats import (
                word_count,
                char_count,
                sentence_count,
                average_word_length,
                most_common_words,
                reading_time_minutes,
            )


            def main():
                sample = (
                    "The quick brown fox jumps over the lazy dog. "
                    "The dog barked loudly! Did the fox escape? "
                    "Yes, the fox ran away quickly."
                )

                print("=== Text Statistics ===")
                print()
                print(f"Sample text: {sample!r}")
                print()
                print(f"Word count: {word_count(sample)}")
                print(f"Character count: {char_count(sample)}")
                print(f"Character count (no whitespace): {char_count(sample, ignore_whitespace=True)}")
                print(f"Sentence count: {sentence_count(sample)}")
                print(f"Average word length: {average_word_length(sample):.2f}")
                print()
                print("Most common words:")
                for word, count in most_common_words(sample, n=5):
                    print(f"  {word}: {count}")
                print()
                print(f"Reading time: {reading_time_minutes(sample):.2f} minutes")
                print(f"Reading time (at 100 wpm): {reading_time_minutes(sample, wpm=100):.2f} minutes")


            if __name__ == "__main__":
                main()
        '''),
    },
    "expected": {
        "min_test_count": 20,
        "quality_threshold": 3,
    },
}

S2_GREENFIELD = {
    "basename": "unit_converter",
    "description": (
        "S2: Greenfield. Prompt + correct code exist. NO example, NO test file. "
        "Agent must generate both from scratch."
    ),
    "expected_behavior": (
        "Agent generates example and test files. Example runs. All tests pass. "
        "Tests cover all 6 conversion functions and ValueError on negatives."
    ),
    "evaluation_guidance": (
        "Was an example file created? Was a test file created? "
        "Does the example run (exit code 0)? Do all tests pass? "
        "Quality of generated tests: do they cover all 6 functions? Do they test ValueError on "
        "negative inputs? Do they check specific numeric values (not just types)? "
        "Do they use pytest.approx() for floating-point comparisons? "
        "Quality of example: does it demonstrate all conversion functions? Is it readable? "
        "Ideal outcome: Both files generated, example runs, all tests pass with good coverage."
    ),
    "files": {
        "prompts/unit_converter_python.prompt": textwrap.dedent("""\
            % Goal
            Write the `unit_converter` module for converting between common measurement units.

            % Requirements
            1. Function `celsius_to_fahrenheit(celsius: float) -> float`: Converts Celsius to Fahrenheit using the formula F = C * 9/5 + 32.
            2. Function `fahrenheit_to_celsius(fahrenheit: float) -> float`: Converts Fahrenheit to Celsius using the formula C = (F - 32) * 5/9.
            3. Function `km_to_miles(km: float) -> float`: Converts kilometers to miles using the factor 0.621371. Raises ValueError if km is negative.
            4. Function `miles_to_km(miles: float) -> float`: Converts miles to kilometers using the factor 1.60934. Raises ValueError if miles is negative.
            5. Function `kg_to_pounds(kg: float) -> float`: Converts kilograms to pounds using the factor 2.20462. Raises ValueError if kg is negative.
            6. Function `pounds_to_kg(pounds: float) -> float`: Converts pounds to kilograms using the factor 0.453592. Raises ValueError if pounds is negative.

            % Dependencies
            Standard library only.

            % Deliverables
            - Module at `src/unit_converter.py` exporting `celsius_to_fahrenheit`, `fahrenheit_to_celsius`, `km_to_miles`, `miles_to_km`, `kg_to_pounds`, `pounds_to_kg`.
        """),
        "src/unit_converter.py": textwrap.dedent('''\
            """Unit converter module for common measurement conversions."""

            from __future__ import annotations


            def celsius_to_fahrenheit(celsius: float) -> float:
                """Convert Celsius to Fahrenheit."""
                return celsius * 9 / 5 + 32


            def fahrenheit_to_celsius(fahrenheit: float) -> float:
                """Convert Fahrenheit to Celsius."""
                return (fahrenheit - 32) * 5 / 9


            def km_to_miles(km: float) -> float:
                """Convert kilometers to miles.

                Raises ValueError if *km* is negative.
                """
                if km < 0:
                    raise ValueError("km must be non-negative")
                return km * 0.621371


            def miles_to_km(miles: float) -> float:
                """Convert miles to kilometers.

                Raises ValueError if *miles* is negative.
                """
                if miles < 0:
                    raise ValueError("miles must be non-negative")
                return miles * 1.60934


            def kg_to_pounds(kg: float) -> float:
                """Convert kilograms to pounds.

                Raises ValueError if *kg* is negative.
                """
                if kg < 0:
                    raise ValueError("kg must be non-negative")
                return kg * 2.20462


            def pounds_to_kg(pounds: float) -> float:
                """Convert pounds to kilograms.

                Raises ValueError if *pounds* is negative.
                """
                if pounds < 0:
                    raise ValueError("pounds must be non-negative")
                return pounds * 0.453592
        '''),
        # No tests/ or examples/ — agent must generate from scratch
    },
    "expected": {
        "min_test_count": 6,
        "quality_threshold": 3,
    },
}

S3_CODE_BUG = {
    "basename": "shopping_cart",
    "description": (
        "S3: Code Bug. Code has >= 100 instead of > 100 in discount logic. "
        "Tests are correct (aligned with spec). Agent should fix code, not tests."
    ),
    "expected_behavior": (
        "Agent detects failing tests, identifies the code bug (>= should be >), "
        "fixes the code, all tests pass. Existing tests must be preserved — adding new tests is fine."
    ),
    "evaluation_guidance": (
        "Did the agent fix the CODE (change >= to > in apply_discount), or did it wrongly fix the TEST? "
        "Compare src/shopping_cart.py — the only needed change is >= to > on the discount line. "
        "Do all tests pass after the fix? Did it preserve the existing tests? "
        "(Adding new tests is fine and should not be penalized — only penalize if existing tests were deleted or rewritten.) "
        "Did it break the example? Check sync stdout for diagnostic reasoning — "
        "did it correctly identify the root cause? Did it get stuck in crash-fix loops "
        "(look for crash_fix_attempt markers)? "
        "Ideal outcome: Agent identifies spec says 'strictly greater than $100', fixes the "
        "code's >= to >, all tests pass, example still works."
    ),
    "files": {
        "prompts/shopping_cart_python.prompt": textwrap.dedent("""\
            % Goal
            Write the `shopping_cart` module for managing a simple shopping cart with discount support.

            % Requirements
            1. Class `ShoppingCart` with an `__init__` method that creates an empty cart.
            2. Method `add_item(name: str, price: float, quantity: int = 1)`: Adds an item to the cart. If the item already exists, its quantity is increased. Raises ValueError if price is negative or quantity is less than 1.
            3. Method `remove_item(name: str)`: Removes an item entirely from the cart. Raises KeyError if the item is not in the cart.
            4. Method `get_subtotal() -> float`: Returns the sum of (price * quantity) for all items, rounded to 2 decimal places.
            5. Method `apply_discount(subtotal: float) -> float`: Applies a 10% discount only when the subtotal is strictly greater than $100 (not equal to $100). Returns the discounted total rounded to 2 decimal places.
            6. Method `get_total() -> float`: Returns `apply_discount(get_subtotal())`.
            7. Method `item_count() -> int`: Returns the total number of individual items (sum of all quantities).

            % Dependencies
            Standard library only.

            % Deliverables
            - Module at `src/shopping_cart.py` exporting `ShoppingCart`.
        """),
        "src/shopping_cart.py": textwrap.dedent('''\
            """Shopping cart module with discount support."""

            from __future__ import annotations

            from typing import Dict, Tuple


            class ShoppingCart:
                """A simple shopping cart with discount logic."""

                def __init__(self) -> None:
                    self._items: Dict[str, Tuple[float, int]] = {}

                def add_item(self, name: str, price: float, quantity: int = 1) -> None:
                    """Add an item to the cart or increase its quantity."""
                    if price < 0:
                        raise ValueError("price must be non-negative")
                    if quantity < 1:
                        raise ValueError("quantity must be at least 1")
                    if name in self._items:
                        existing_price, existing_qty = self._items[name]
                        self._items[name] = (existing_price, existing_qty + quantity)
                    else:
                        self._items[name] = (price, quantity)

                def remove_item(self, name: str) -> None:
                    """Remove an item from the cart."""
                    if name not in self._items:
                        raise KeyError(f"Item \\'{name}\\' not in cart")
                    del self._items[name]

                def get_subtotal(self) -> float:
                    """Return the sum of price * quantity for all items."""
                    total = sum(price * qty for price, qty in self._items.values())
                    return round(total, 2)

                def apply_discount(self, subtotal: float) -> float:
                    """Apply 10% discount for qualifying subtotals."""
                    if subtotal >= 100:
                        return round(subtotal * 0.9, 2)
                    return round(subtotal, 2)

                def get_total(self) -> float:
                    """Return the discounted total."""
                    return self.apply_discount(self.get_subtotal())

                def item_count(self) -> int:
                    """Return total number of individual items."""
                    return sum(qty for _, qty in self._items.values())
        '''),
        "tests/test_shopping_cart.py": textwrap.dedent('''\
            """
            Test plan for shopping_cart module:
            1. ShoppingCart.__init__: creates empty cart
            2. add_item: basic add, quantity increase for existing item, negative price raises ValueError, quantity < 1 raises ValueError
            3. remove_item: remove existing item, remove missing item raises KeyError
            4. get_subtotal: single item, multiple items, rounds to 2 decimal places
            5. apply_discount: subtotal strictly > $100 gets 10% off, subtotal == $100 gets NO discount, subtotal < $100 gets no discount
            6. get_total: integrates subtotal and discount
            7. item_count: empty cart, after adds, sum of quantities
            """

            import pytest
            import sys
            import os

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.shopping_cart import ShoppingCart


            class TestInit:
                def test_empty_cart(self):
                    cart = ShoppingCart()
                    assert cart.item_count() == 0
                    assert cart.get_subtotal() == 0.0


            class TestAddItem:
                def test_add_single_item(self):
                    cart = ShoppingCart()
                    cart.add_item("Widget", 10.0)
                    assert cart.item_count() == 1
                    assert cart.get_subtotal() == 10.0

                def test_add_with_quantity(self):
                    cart = ShoppingCart()
                    cart.add_item("Widget", 10.0, quantity=3)
                    assert cart.item_count() == 3
                    assert cart.get_subtotal() == 30.0

                def test_add_existing_increases_quantity(self):
                    cart = ShoppingCart()
                    cart.add_item("Widget", 10.0, quantity=2)
                    cart.add_item("Widget", 10.0, quantity=3)
                    assert cart.item_count() == 5
                    assert cart.get_subtotal() == 50.0

                def test_negative_price_raises(self):
                    cart = ShoppingCart()
                    with pytest.raises(ValueError):
                        cart.add_item("Widget", -5.0)

                def test_zero_quantity_raises(self):
                    cart = ShoppingCart()
                    with pytest.raises(ValueError):
                        cart.add_item("Widget", 10.0, quantity=0)


            class TestRemoveItem:
                def test_remove_existing(self):
                    cart = ShoppingCart()
                    cart.add_item("Widget", 10.0)
                    cart.remove_item("Widget")
                    assert cart.item_count() == 0

                def test_remove_missing_raises(self):
                    cart = ShoppingCart()
                    with pytest.raises(KeyError):
                        cart.remove_item("Nonexistent")


            class TestGetSubtotal:
                def test_single_item(self):
                    cart = ShoppingCart()
                    cart.add_item("Widget", 10.99, quantity=2)
                    assert cart.get_subtotal() == 21.98

                def test_multiple_items(self):
                    cart = ShoppingCart()
                    cart.add_item("A", 10.0)
                    cart.add_item("B", 20.0)
                    assert cart.get_subtotal() == 30.0

                def test_rounding(self):
                    cart = ShoppingCart()
                    cart.add_item("Widget", 1.005, quantity=3)
                    result = cart.get_subtotal()
                    assert result == round(1.005 * 3, 2)


            class TestApplyDiscount:
                def test_over_100_gets_discount(self):
                    cart = ShoppingCart()
                    result = cart.apply_discount(150.0)
                    assert result == 135.0

                def test_exactly_100_no_discount(self):
                    """Spec says discount is strictly > $100, so exactly $100 should NOT get a discount."""
                    cart = ShoppingCart()
                    result = cart.apply_discount(100.0)
                    assert result == 100.0

                def test_under_100_no_discount(self):
                    cart = ShoppingCart()
                    result = cart.apply_discount(50.0)
                    assert result == 50.0


            class TestGetTotal:
                def test_with_discount(self):
                    cart = ShoppingCart()
                    cart.add_item("Expensive", 60.0, quantity=2)
                    assert cart.get_total() == 108.0

                def test_without_discount(self):
                    cart = ShoppingCart()
                    cart.add_item("Cheap", 10.0)
                    assert cart.get_total() == 10.0


            class TestItemCount:
                def test_empty(self):
                    cart = ShoppingCart()
                    assert cart.item_count() == 0

                def test_after_adds(self):
                    cart = ShoppingCart()
                    cart.add_item("A", 10.0, quantity=2)
                    cart.add_item("B", 5.0, quantity=3)
                    assert cart.item_count() == 5
        '''),
        "examples/shopping_cart_example.py": textwrap.dedent('''\
            """Example demonstrating the shopping_cart module."""

            import os
            import sys

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.shopping_cart import ShoppingCart


            def main():
                cart = ShoppingCart()

                print("=== Shopping Cart Demo ===")
                print()

                # Add some items
                cart.add_item("Widget", 25.99, quantity=2)
                cart.add_item("Gadget", 49.99)
                cart.add_item("Doohickey", 12.50, quantity=3)

                print(f"Items in cart: {cart.item_count()}")
                print(f"Subtotal: ${cart.get_subtotal():.2f}")
                print(f"Total (with discount if applicable): ${cart.get_total():.2f}")
                print()

                # Remove an item
                cart.remove_item("Doohickey")
                print("After removing Doohickey:")
                print(f"Items in cart: {cart.item_count()}")
                print(f"Subtotal: ${cart.get_subtotal():.2f}")
                print(f"Total: ${cart.get_total():.2f}")


            if __name__ == "__main__":
                main()
        '''),
    },
    "expected": {
        "min_test_count": 15,
        "quality_threshold": 2,
    },
}

S4_MINIMAL_COVERAGE = {
    "basename": "stack_calculator",
    "description": (
        "S4: Minimal Test Coverage. Correct code + example + only 3 basic tests. "
        "Agent should add comprehensive tests covering all 7 requirements."
    ),
    "expected_behavior": (
        "Agent preserves the original 3 tests and adds many more covering: "
        "peek, size, clear, division, ZeroDivisionError, subtraction, multiplication, "
        "invalid tokens, empty expression, malformed expressions. All tests pass."
    ),
    "evaluation_guidance": (
        "How many tests in the final file vs the starting 3? Were the original 3 tests preserved "
        "(test_push_and_pop, test_evaluate_addition, test_evaluate_complex)? "
        "Coverage of new tests — does the final test file cover: "
        "peek() and empty-stack IndexError? size() and clear()? Division and ZeroDivisionError? "
        "Subtraction and multiplication? Malformed expressions (too few operands, too many values)? "
        "Invalid tokens? Empty expression? "
        "Do all tests pass? Did it make unnecessary code changes to src/stack_calculator.py? "
        "Did the agent introduce any bugs (e.g., f-string escaping issues like '{{token}}' instead of '{token}')? "
        "Ideal outcome: Original 3 tests preserved, many new tests added covering all 7 requirements, "
        "no code changes, all tests pass."
    ),
    "files": {
        "prompts/stack_calculator_python.prompt": textwrap.dedent("""\
            % Goal
            Write the `stack_calculator` module implementing a Reverse Polish Notation (RPN) calculator.

            % Requirements
            1. Class `StackCalculator` with an `__init__` method that creates an empty operand stack.
            2. Method `push(value: float)`: Pushes a numeric value onto the stack.
            3. Method `pop() -> float`: Pops and returns the top value from the stack. Raises IndexError if the stack is empty.
            4. Method `peek() -> float`: Returns the top value without removing it. Raises IndexError if the stack is empty.
            5. Method `evaluate(expression: str) -> float`: Parses a whitespace-separated RPN expression, pushes numbers, and applies operators (+, -, *, /). Returns the final result (the single remaining value on the stack). Raises ValueError if the expression is malformed (too few operands for an operator, or more than one value remains after processing). Raises ZeroDivisionError for division by zero.
            6. Method `size() -> int`: Returns the current number of values on the stack.
            7. Method `clear()`: Removes all values from the stack.

            % Dependencies
            Standard library only.

            % Deliverables
            - Module at `src/stack_calculator.py` exporting `StackCalculator`.
        """),
        "src/stack_calculator.py": textwrap.dedent('''\
            """RPN (Reverse Polish Notation) stack calculator."""

            from __future__ import annotations

            from typing import List


            class StackCalculator:
                """Reverse Polish Notation calculator using an explicit stack."""

                _OPERATORS = {"+", "-", "*", "/"}

                def __init__(self) -> None:
                    self._stack: List[float] = []

                def push(self, value: float) -> None:
                    """Push a numeric value onto the stack."""
                    self._stack.append(float(value))

                def pop(self) -> float:
                    """Pop and return the top value.

                    Raises IndexError if the stack is empty.
                    """
                    if not self._stack:
                        raise IndexError("pop from empty stack")
                    return self._stack.pop()

                def peek(self) -> float:
                    """Return the top value without removing it.

                    Raises IndexError if the stack is empty.
                    """
                    if not self._stack:
                        raise IndexError("peek at empty stack")
                    return self._stack[-1]

                def evaluate(self, expression: str) -> float:
                    """Evaluate a whitespace-separated RPN expression.

                    Raises ValueError for malformed expressions and
                    ZeroDivisionError for division by zero.
                    """
                    tokens = expression.split()
                    if not tokens:
                        raise ValueError("empty expression")

                    for token in tokens:
                        if token in self._OPERATORS:
                            if len(self._stack) < 2:
                                raise ValueError(
                                    f"not enough operands for operator \\'{token}\\'"
                                )
                            b = self._stack.pop()
                            a = self._stack.pop()
                            if token == "+":
                                self._stack.append(a + b)
                            elif token == "-":
                                self._stack.append(a - b)
                            elif token == "*":
                                self._stack.append(a * b)
                            elif token == "/":
                                if b == 0:
                                    raise ZeroDivisionError("division by zero")
                                self._stack.append(a / b)
                        else:
                            try:
                                self._stack.append(float(token))
                            except ValueError:
                                raise ValueError(f"invalid token: \\'{token}\\'")

                    if len(self._stack) != 1:
                        raise ValueError(
                            f"malformed expression: {len(self._stack)} values remain on stack"
                        )
                    return self._stack.pop()

                def size(self) -> int:
                    """Return the number of values on the stack."""
                    return len(self._stack)

                def clear(self) -> None:
                    """Remove all values from the stack."""
                    self._stack.clear()
        '''),
        "tests/test_stack_calculator.py": textwrap.dedent('''\
            """
            Test plan for stack_calculator module:
            1. push/pop basic operations
            2. evaluate simple addition
            3. evaluate complex expression
            (More tests needed for full coverage)
            """

            import sys
            import os

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.stack_calculator import StackCalculator


            def test_push_and_pop():
                calc = StackCalculator()
                calc.push(5.0)
                assert calc.pop() == 5.0


            def test_evaluate_addition():
                calc = StackCalculator()
                assert calc.evaluate("3 4 +") == 7.0


            def test_evaluate_complex():
                calc = StackCalculator()
                assert calc.evaluate("5 3 + 2 *") == 16.0
        '''),
        "examples/stack_calculator_example.py": textwrap.dedent('''\
            """Example demonstrating the stack_calculator module."""

            import os
            import sys

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.stack_calculator import StackCalculator


            def main():
                calc = StackCalculator()

                print("=== RPN Stack Calculator ===")
                print()

                # Basic arithmetic: (3 + 4) = 7
                result = calc.evaluate("3 4 +")
                print(f"3 4 + = {result}")

                # More complex: (5 + 3) * 2 = 16
                result = calc.evaluate("5 3 + 2 *")
                print(f"5 3 + 2 * = {result}")

                # Division: 10 / 3 = 3.333...
                result = calc.evaluate("10 3 /")
                print(f"10 3 / = {result:.4f}")

                # Manual stack operations
                calc.push(42)
                print(f"Pushed 42, stack size: {calc.size()}")
                print(f"Peek: {calc.peek()}")
                print(f"Pop: {calc.pop()}")
                print(f"Stack size after pop: {calc.size()}")


            if __name__ == "__main__":
                main()
        '''),
    },
    "expected": {
        "min_test_count": 8,
        "quality_threshold": 3,
    },
}

S5_CRASHING_EXAMPLE = {
    "basename": "password_validator",
    "description": (
        "S5: Crashing Example. Code is correct. Example crashes due to "
        "strict=True kwarg that doesn't exist. No test file. "
        "Agent should fix example and generate tests."
    ),
    "expected_behavior": (
        "Agent fixes the example (remove strict=True), generates comprehensive tests "
        "covering all checks (length, uppercase, digit, special char) and strength levels. "
        "Code should not be modified."
    ),
    "evaluation_guidance": (
        "Did the agent fix the example? The fix should remove the strict=True argument. "
        "Was the fix minimal (1-line change) or did the agent rewrite the entire example? "
        "Compare examples/password_validator_example.py — was the fix correct and minimal? "
        "Does the fixed example run? Was a test file generated? "
        "Test quality: does it cover all checks (length, uppercase, digit, special char)? "
        "Does it test strength calculation (weak/moderate/strong)? Does it test the valid flag? "
        "Does it test each check in isolation (not just combined passwords)? "
        "Did it unnecessarily modify the code? src/password_validator.py should be unchanged. "
        "Ideal outcome: Example fixed (remove strict=True), code unchanged, tests generated "
        "covering all requirements, everything passes."
    ),
    "files": {
        "prompts/password_validator_python.prompt": textwrap.dedent("""\
            % Goal
            Write the `password_validator` module for checking password strength and validity.

            % Requirements
            1. Function `validate_password(password: str) -> dict`: Returns a dictionary with keys `"valid"` (bool), `"errors"` (list of strings describing each failed check), and `"strength"` (str, one of "weak", "moderate", "strong"). A password is valid when it has zero errors.
            2. Check: Password must be at least 8 characters long. Error message: "Password must be at least 8 characters".
            3. Check: Password must contain at least one uppercase letter. Error message: "Password must contain at least one uppercase letter".
            4. Check: Password must contain at least one digit. Error message: "Password must contain at least one digit".
            5. Check: Password must contain at least one special character from the set `!@#$%^&*()_+-=`. Error message: "Password must contain at least one special character".
            6. Strength calculation: "weak" if 2 or more checks fail, "moderate" if exactly 1 check fails, "strong" if all checks pass.

            % Dependencies
            Standard library only.

            % Deliverables
            - Module at `src/password_validator.py` exporting `validate_password`.
        """),
        "src/password_validator.py": textwrap.dedent('''\
            """Password validator module for checking password strength."""

            from __future__ import annotations

            from typing import Dict, List

            SPECIAL_CHARS = set("!@#$%^&*()_+-=")


            def validate_password(password: str) -> Dict[str, object]:
                """Validate a password and return validity, errors, and strength.

                Returns a dict with:
                  - "valid": bool
                  - "errors": list of error message strings
                  - "strength": "weak" | "moderate" | "strong"
                """
                errors: List[str] = []

                if len(password) < 8:
                    errors.append("Password must be at least 8 characters")

                if not any(c.isupper() for c in password):
                    errors.append("Password must contain at least one uppercase letter")

                if not any(c.isdigit() for c in password):
                    errors.append("Password must contain at least one digit")

                if not any(c in SPECIAL_CHARS for c in password):
                    errors.append("Password must contain at least one special character")

                fail_count = len(errors)
                if fail_count >= 2:
                    strength = "weak"
                elif fail_count == 1:
                    strength = "moderate"
                else:
                    strength = "strong"

                return {
                    "valid": len(errors) == 0,
                    "errors": errors,
                    "strength": strength,
                }
        '''),
        # No tests/ — agent must generate
        "examples/password_validator_example.py": textwrap.dedent('''\
            """Example demonstrating the password_validator module."""

            import os
            import sys

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.password_validator import validate_password


            def main():
                passwords = [
                    "short",
                    "alllowercase1!",
                    "NoDigitHere!",
                    "NoSpecial1Char",
                    "Strong1Pass!",
                ]

                print("=== Password Validator ===")
                print()

                for pwd in passwords:
                    result = validate_password(pwd, strict=True)
                    print(f"Password: {pwd!r}")
                    print(f"  Valid: {result['valid']}")
                    print(f"  Strength: {result['strength']}")
                    if result["errors"]:
                        for err in result["errors"]:
                            print(f"  Error: {err}")
                    print()


            if __name__ == "__main__":
                main()
        '''),
    },
    "expected": {
        "min_test_count": 6,
        "quality_threshold": 3,
    },
}

S6_WRONG_TESTS = {
    "basename": "date_range",
    "description": (
        "S6: Wrong Tests. Code correctly uses half-open intervals [start, end). "
        "Tests were written for inclusive intervals — 6 tests have wrong expectations. "
        "Agent should fix tests, not code."
    ),
    "expected_behavior": (
        "Agent identifies that tests are wrong (not the code), since the spec says "
        "half-open intervals. Fixes all 6 failing tests. Code remains unchanged. "
        "All tests pass."
    ),
    "evaluation_guidance": (
        "Did the agent fix the TESTS (not the code)? The spec says half-open intervals — "
        "end date is excluded. The code is correct. "
        "Which specific tests were fixed? The 6 failing tests assume inclusive end dates: "
        "test_basic_range (expects 4 dates, should be 3), test_basic_count (expects 4, should be 3), "
        "test_end_included (expects True, should be False — ideally renamed to test_end_excluded), "
        "test_partial_overlap (expects 3 dates, should be 2), "
        "test_adjacent_ranges (expects ['2024-01-03'], should be [] since half-open ranges don't overlap), "
        "test_complete_containment (expects 4 dates, should be 3). "
        "Did the agent correctly reason that the spec (half-open) is authoritative over the tests? "
        "Did the code remain unchanged? src/date_range.py should be identical to reference. "
        "Ideal outcome: Agent identifies tests are wrong, fixes all 6, code unchanged, all tests pass."
    ),
    "files": {
        "prompts/date_range_python.prompt": textwrap.dedent("""\
            % Goal
            Write the `date_range` module for generating and querying date ranges using half-open intervals.

            % Requirements
            1. Function `date_range(start: str, end: str) -> list[str]`: Takes ISO-format date strings (YYYY-MM-DD). Returns a list of all dates in the half-open interval [start, end) — start is included, end is excluded. Raises ValueError if start >= end or if dates are malformed.
            2. Function `days_between(start: str, end: str) -> int`: Returns the number of days in the half-open interval [start, end). This equals len(date_range(start, end)). Raises ValueError if start >= end.
            3. Function `contains(start: str, end: str, date: str) -> bool`: Returns True if the given date falls within the half-open interval [start, end). The start date is included, the end date is excluded.
            4. Function `overlap(start1: str, end1: str, start2: str, end2: str) -> list[str]`: Returns the list of dates in the intersection of two half-open intervals. Returns an empty list if there is no overlap.
            5. Function `shift_range(start: str, end: str, days: int) -> tuple[str, str]`: Shifts both start and end by the given number of days (positive = forward, negative = backward). Returns the new (start, end) tuple as ISO-format strings.
            6. All date parameters use ISO format (YYYY-MM-DD). The module must use `datetime.date` for internal calculations.

            % Dependencies
            Standard library only: `datetime`.

            % Deliverables
            - Module at `src/date_range.py` exporting `date_range`, `days_between`, `contains`, `overlap`, `shift_range`.
        """),
        "src/date_range.py": textwrap.dedent('''\
            """Date range module using half-open intervals [start, end)."""

            from __future__ import annotations

            import datetime
            from typing import List, Tuple


            def _parse(date_str: str) -> datetime.date:
                """Parse an ISO-format date string."""
                try:
                    return datetime.date.fromisoformat(date_str)
                except (ValueError, TypeError) as e:
                    raise ValueError(f"Invalid date format: {date_str!r}") from e


            def date_range(start: str, end: str) -> List[str]:
                """Return all dates in the half-open interval [start, end).

                Start is included, end is excluded.
                Raises ValueError if start >= end.
                """
                s = _parse(start)
                e = _parse(end)
                if s >= e:
                    raise ValueError(f"start ({start}) must be before end ({end})")
                result = []
                current = s
                while current < e:
                    result.append(current.isoformat())
                    current += datetime.timedelta(days=1)
                return result


            def days_between(start: str, end: str) -> int:
                """Return the number of days in [start, end).

                Raises ValueError if start >= end.
                """
                s = _parse(start)
                e = _parse(end)
                if s >= e:
                    raise ValueError(f"start ({start}) must be before end ({end})")
                return (e - s).days


            def contains(start: str, end: str, date: str) -> bool:
                """Return True if date is in the half-open interval [start, end)."""
                s = _parse(start)
                e = _parse(end)
                d = _parse(date)
                return s <= d < e


            def overlap(start1: str, end1: str, start2: str, end2: str) -> List[str]:
                """Return dates in the intersection of two half-open intervals."""
                s1, e1 = _parse(start1), _parse(end1)
                s2, e2 = _parse(start2), _parse(end2)
                ov_start = max(s1, s2)
                ov_end = min(e1, e2)
                if ov_start >= ov_end:
                    return []
                result = []
                current = ov_start
                while current < ov_end:
                    result.append(current.isoformat())
                    current += datetime.timedelta(days=1)
                return result


            def shift_range(start: str, end: str, days: int) -> Tuple[str, str]:
                """Shift both start and end by the given number of days."""
                s = _parse(start)
                e = _parse(end)
                delta = datetime.timedelta(days=days)
                return ((s + delta).isoformat(), (e + delta).isoformat())
        '''),
        "tests/test_date_range.py": textwrap.dedent('''\
            """
            Test plan for date_range module:
            1. date_range: basic range, single day, start >= end raises ValueError
            2. days_between: basic count, single day, start >= end raises ValueError
            3. contains: start included, end included, before range, after range
            4. overlap: partial overlap, no overlap, complete containment
            5. shift_range: forward shift, backward shift
            6. Edge cases: malformed dates raise ValueError
            """

            import pytest
            import sys
            import os

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.date_range import date_range, days_between, contains, overlap, shift_range


            class TestDateRange:
                def test_basic_range(self):
                    result = date_range("2024-01-01", "2024-01-04")
                    # WRONG: expects end date included (inclusive interval)
                    assert result == ["2024-01-01", "2024-01-02", "2024-01-03", "2024-01-04"]

                def test_single_day(self):
                    result = date_range("2024-03-15", "2024-03-16")
                    assert result == ["2024-03-15"]

                def test_start_equals_end_raises(self):
                    with pytest.raises(ValueError):
                        date_range("2024-01-01", "2024-01-01")

                def test_start_after_end_raises(self):
                    with pytest.raises(ValueError):
                        date_range("2024-01-05", "2024-01-01")


            class TestDaysBetween:
                def test_basic_count(self):
                    # WRONG: expects 4 (inclusive) instead of 3 (half-open)
                    assert days_between("2024-01-01", "2024-01-04") == 4

                def test_single_day(self):
                    assert days_between("2024-03-15", "2024-03-16") == 1

                def test_start_equals_end_raises(self):
                    with pytest.raises(ValueError):
                        days_between("2024-01-01", "2024-01-01")


            class TestContains:
                def test_start_included(self):
                    assert contains("2024-01-01", "2024-01-05", "2024-01-01") is True

                def test_end_included(self):
                    # WRONG: expects end date to be included (inclusive interval)
                    assert contains("2024-01-01", "2024-01-05", "2024-01-05") is True

                def test_middle_date(self):
                    assert contains("2024-01-01", "2024-01-05", "2024-01-03") is True

                def test_before_range(self):
                    assert contains("2024-01-01", "2024-01-05", "2023-12-31") is False

                def test_after_range(self):
                    assert contains("2024-01-01", "2024-01-05", "2024-01-06") is False


            class TestOverlap:
                def test_partial_overlap(self):
                    result = overlap("2024-01-01", "2024-01-05", "2024-01-03", "2024-01-07")
                    # WRONG: expects end dates included
                    assert result == ["2024-01-03", "2024-01-04", "2024-01-05"]

                def test_no_overlap(self):
                    result = overlap("2024-01-01", "2024-01-03", "2024-01-05", "2024-01-07")
                    assert result == []

                def test_adjacent_ranges(self):
                    result = overlap("2024-01-01", "2024-01-03", "2024-01-03", "2024-01-05")
                    # WRONG: expects the touching date to be included
                    assert result == ["2024-01-03"]

                def test_complete_containment(self):
                    result = overlap("2024-01-01", "2024-01-10", "2024-01-03", "2024-01-06")
                    # WRONG: expects end date included
                    assert result == ["2024-01-03", "2024-01-04", "2024-01-05", "2024-01-06"]


            class TestShiftRange:
                def test_forward_shift(self):
                    assert shift_range("2024-01-01", "2024-01-05", 10) == ("2024-01-11", "2024-01-15")

                def test_backward_shift(self):
                    assert shift_range("2024-01-10", "2024-01-15", -5) == ("2024-01-05", "2024-01-10")

                def test_zero_shift(self):
                    assert shift_range("2024-01-01", "2024-01-05", 0) == ("2024-01-01", "2024-01-05")


            class TestEdgeCases:
                def test_malformed_date_raises(self):
                    with pytest.raises(ValueError):
                        date_range("not-a-date", "2024-01-05")

                def test_malformed_end_raises(self):
                    with pytest.raises(ValueError):
                        date_range("2024-01-01", "bad")
        '''),
        "examples/date_range_example.py": textwrap.dedent('''\
            """Example demonstrating the date_range module."""

            import os
            import sys

            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

            from src.date_range import date_range, days_between, contains, overlap, shift_range


            def main():
                print("=== Date Range Module (Half-Open Intervals) ===")
                print()

                # Generate a date range [start, end)
                dates = date_range("2024-01-01", "2024-01-05")
                print(f"date_range(\'2024-01-01\', \'2024-01-05\'):")
                for d in dates:
                    print(f"  {d}")
                print(f"  (end date 2024-01-05 is excluded)")
                print()

                # Count days
                n = days_between("2024-01-01", "2024-01-05")
                print(f"days_between(\'2024-01-01\', \'2024-01-05\'): {n}")
                print()

                # Check containment
                print(f"contains(\'2024-01-01\', \'2024-01-05\', \'2024-01-01\'): {contains('2024-01-01', '2024-01-05', '2024-01-01')}")
                print(f"contains(\'2024-01-01\', \'2024-01-05\', \'2024-01-04\'): {contains('2024-01-01', '2024-01-05', '2024-01-04')}")
                print(f"contains(\'2024-01-01\', \'2024-01-05\', \'2024-01-05\'): {contains('2024-01-01', '2024-01-05', '2024-01-05')}")
                print()

                # Overlap
                ov = overlap("2024-01-01", "2024-01-05", "2024-01-03", "2024-01-07")
                print(f"overlap(\'2024-01-01\', \'2024-01-05\', \'2024-01-03\', \'2024-01-07\'): {ov}")
                print()

                # Shift
                new_start, new_end = shift_range("2024-01-01", "2024-01-05", 10)
                print(f"shift_range(\'2024-01-01\', \'2024-01-05\', 10): ({new_start}, {new_end})")


            if __name__ == "__main__":
                main()
        '''),
    },
    "expected": {
        "min_test_count": 15,
        "quality_threshold": 2,
    },
}

# All small scenarios
_SMALL_SCENARIOS = {
    "s1": S1_ALL_IN_SYNC,
    "s2": S2_GREENFIELD,
    "s3": S3_CODE_BUG,
    "s4": S4_MINIMAL_COVERAGE,
    "s5": S5_CRASHING_EXAMPLE,
    "s6": S6_WRONG_TESTS,
}


# =========================================================================
# Fixture loader for large scenarios (S7-S9)
# =========================================================================

def _load_fixture_scenario(fixture_name: str) -> dict:
    """Load a large scenario from tests/fixtures/one_session_eval/."""
    fixture_dir = Path(__file__).parent / "fixtures" / "one_session_eval" / fixture_name
    if not fixture_dir.exists():
        pytest.skip(f"Fixture directory not found: {fixture_dir}")
    metadata = json.loads((fixture_dir / "scenario.json").read_text())
    files: Dict[str, str] = {}
    for subdir in ["src", "tests", "examples", "prompts"]:
        subdir_path = fixture_dir / subdir
        if subdir_path.exists():
            for f in subdir_path.iterdir():
                if f.is_file():
                    files[f"{subdir}/{f.name}"] = f.read_text()
    return {**metadata, "files": files}


# =========================================================================
# Helper functions
# =========================================================================

def _setup_scenario_dir(tmp_path: Path, scenario: dict) -> Path:
    """Create a complete PDD project directory from scenario data."""
    project_dir = tmp_path / "project"
    project_dir.mkdir()

    # Create directory structure
    for subdir in ["src", "tests", "examples", "prompts"]:
        (project_dir / subdir).mkdir()

    # Write .pddrc
    (project_dir / ".pddrc").write_text(PDDRC_CONTENT)

    # Write scenario files
    for rel_path, content in scenario["files"].items():
        file_path = project_dir / rel_path
        file_path.parent.mkdir(parents=True, exist_ok=True)
        file_path.write_text(content)

    # Git init (required by agentic CLIs)
    subprocess.run(
        ["git", "init"],
        cwd=project_dir,
        capture_output=True,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.email", "test@eval.pdd"],
        cwd=project_dir,
        capture_output=True,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "PDD Eval"],
        cwd=project_dir,
        capture_output=True,
        check=True,
    )
    subprocess.run(
        ["git", "add", "."],
        cwd=project_dir,
        capture_output=True,
        check=True,
    )
    subprocess.run(
        ["git", "commit", "-m", "Initial scenario state"],
        cwd=project_dir,
        capture_output=True,
        check=True,
    )

    return project_dir


def _run_pdd_sync(
    project_dir: Path,
    basename: str,
    timeout: int = 300,
    extra_env: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """Run pdd --local sync --one-session and return results."""
    import shutil
    pdd_cmd = shutil.which("pdd")
    if not pdd_cmd:
        pytest.skip("pdd CLI not found on PATH")

    cmd = [pdd_cmd, "--local", "sync", "--one-session", basename]

    env = {**os.environ, "PDD_FORCE": "1", "PDD_SKIP_UPDATE_CHECK": "1"}
    if extra_env:
        env.update(extra_env)

    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            cwd=project_dir,
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
            stdin=subprocess.DEVNULL,
        )
        wall_time = time.monotonic() - start
        stdout = proc.stdout or ""
        stderr = proc.stderr or ""
        if proc.returncode != 0:
            print(f"\n  >> sync failed: exit={proc.returncode} ({wall_time:.0f}s)")
            print(f"  >> stderr: {stderr[:300]}")
    except subprocess.TimeoutExpired as e:
        wall_time = time.monotonic() - start
        stdout = (e.stdout or b"").decode(errors="replace")
        stderr = (e.stderr or b"").decode(errors="replace")
        return {
            "stdout": stdout,
            "stderr": stderr,
            "exit_code": -1,
            "wall_time": wall_time,
            "cost": 0.0,
            "timed_out": True,
        }

    # Parse cost from stdout
    cost = 0.0
    cost_match = re.search(r"Total Estimated Cost:\s*\$?([\d.]+)", stdout)
    if cost_match:
        cost = float(cost_match.group(1))

    return {
        "stdout": stdout,
        "stderr": stderr,
        "exit_code": proc.returncode,
        "wall_time": wall_time,
        "cost": cost,
        "timed_out": False,
    }


def _run_pytest_on_result(
    project_dir: Path,
    basename: str,
) -> Dict[str, Any]:
    """Run pytest on the scenario's test file after sync."""
    test_file = project_dir / "tests" / f"test_{basename}.py"
    if not test_file.exists():
        return {"exit_code": -1, "output": "Test file not found", "test_count": 0}

    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-xvs", str(test_file)],
        cwd=project_dir,
        capture_output=True,
        text=True,
        timeout=120,
    )
    output = (proc.stdout or "") + (proc.stderr or "")

    # Count test functions
    test_content = test_file.read_text()
    test_count = len(re.findall(r"def test_\w+", test_content))

    return {
        "exit_code": proc.returncode,
        "output": output,
        "test_count": test_count,
    }


def _run_example(
    project_dir: Path,
    basename: str,
) -> Dict[str, Any]:
    """Run the example file after sync."""
    example_file = project_dir / "examples" / f"{basename}_example.py"
    if not example_file.exists():
        return {"exit_code": -1, "output": "Example file not found"}

    proc = subprocess.run(
        [sys.executable, str(example_file)],
        cwd=project_dir,
        capture_output=True,
        text=True,
        timeout=30,
    )
    return {
        "exit_code": proc.returncode,
        "output": (proc.stdout or "") + (proc.stderr or ""),
    }


def _collect_final_files(project_dir: Path) -> Dict[str, str]:
    """Read all .py and .prompt files from the scenario directory."""
    files: Dict[str, str] = {}
    for subdir in ["src", "tests", "examples", "prompts"]:
        subdir_path = project_dir / subdir
        if subdir_path.exists():
            for f in subdir_path.iterdir():
                if f.is_file() and f.suffix in (".py", ".prompt"):
                    files[f"{subdir}/{f.name}"] = f.read_text()
    return files


def _format_files_for_prompt(files: Dict[str, str], max_chars: int = 50000) -> str:
    """Format file contents for inclusion in the evaluator prompt.

    Prioritizes test and example files (the artifacts the judge needs to compare)
    over code and prompt files (which are mostly unchanged between variants).
    Large code files are truncated to head+tail to stay within budget.
    """
    # Prioritize: tests > examples > prompts > src (code files are largest, least likely to differ)
    def _sort_key(path: str) -> tuple:
        if path.startswith("tests/"):
            return (0, path)
        if path.startswith("examples/"):
            return (1, path)
        if path.startswith("prompts/"):
            return (2, path)
        return (3, path)

    parts = []
    total = 0
    for path in sorted(files.keys(), key=_sort_key):
        content = files[path]
        entry = f"--- {path} ---\n{content}\n"

        if total + len(entry) > max_chars:
            # For large files, include head + tail instead of skipping entirely
            remaining = max_chars - total - 200  # leave room for markers
            if remaining > 2000:
                head_size = remaining // 2
                tail_size = remaining // 2
                truncated = (
                    content[:head_size]
                    + f"\n\n--- [{path}: truncated {len(content) - head_size - tail_size} chars] ---\n\n"
                    + content[-tail_size:]
                )
                entry = f"--- {path} ---\n{truncated}\n"
                parts.append(entry)
            else:
                parts.append(
                    f"--- {path} (omitted, {len(content)} chars) ---\n"
                )
            break
        parts.append(entry)
        total += len(entry)
    return "\n".join(parts)


def _compute_diffs(
    reference_files: Dict[str, str],
    final_files: Dict[str, str],
    max_chars: int = 40000,
) -> str:
    """Compute unified diffs between reference (starting) and final files.

    For files that exist in final but not reference, shows the full content as
    a new-file diff. For files unchanged, notes 'no changes'. Escapes curly
    braces for str.format() safety.
    """
    parts = []
    total = 0

    all_paths = sorted(set(reference_files.keys()) | set(final_files.keys()))

    for path in all_paths:
        ref = reference_files.get(path, "")
        final = final_files.get(path, "")

        if ref == final:
            entry = f"--- {path}: no changes ---\n"
        elif not ref:
            # New file created by the agent
            lines = final.splitlines(keepends=True)
            diff_lines = [f"+{line}" for line in lines]
            diff_text = f"--- /dev/null\n+++ {path}\n" + "".join(diff_lines)
            entry = f"--- {path} (NEW FILE, {len(final)} chars) ---\n{diff_text}\n"
        else:
            diff_lines = list(difflib.unified_diff(
                ref.splitlines(keepends=True),
                final.splitlines(keepends=True),
                fromfile=f"reference/{path}",
                tofile=f"final/{path}",
                n=3,
            ))
            if not diff_lines:
                entry = f"--- {path}: no changes ---\n"
            else:
                diff_text = "".join(diff_lines)
                entry = f"{diff_text}\n"

        if total + len(entry) > max_chars:
            parts.append(f"--- (diff output truncated, {len(all_paths) - len(parts)} files remaining) ---")
            break
        parts.append(entry)
        total += len(entry)

    return "\n".join(parts)


def _get_new_files(
    reference_files: Dict[str, str],
    final_files: Dict[str, str],
) -> Dict[str, str]:
    """Return only files that exist in final but not in reference (newly created)."""
    return {
        path: content
        for path, content in final_files.items()
        if path not in reference_files
    }


def _setup_prompt_override(variant_dir: Path, variant: str) -> Optional[str]:
    """Set up a PDD_PATH override directory for the "original" variant.

    For "current": returns None (no override needed — uses installed package prompt).
    For "original": creates a directory with the old prompt template and returns
    the path to use as PDD_PATH, so the resolver finds it first.
    """
    if variant == "current":
        return None

    # Create a PDD_PATH directory with the old prompt template
    pdd_path_dir = variant_dir / "_pdd_path_override"
    prompts_dir = pdd_path_dir / "prompts"
    prompts_dir.mkdir(parents=True)
    old_prompt = _ORIGINAL_PROMPT_PATH.read_text()
    (prompts_dir / "one_session_agent_LLM.prompt").write_text(old_prompt)
    return str(pdd_path_dir)


def _run_scenario_variant(
    tmp_path: Path,
    scenario: dict,
    variant: str,
    timeout: int = 300,
) -> Dict[str, Any]:
    """Run a full scenario with one prompt variant. Returns all results bundled."""
    # Use a subdirectory per variant so both can coexist in the same tmp_path
    variant_dir = tmp_path / variant
    variant_dir.mkdir()
    project_dir = _setup_scenario_dir(variant_dir, scenario)

    # For "original" variant, override PDD_PATH so resolver picks up the old prompt
    # without mutating any shared files (safe for parallel execution)
    pdd_path_override = _setup_prompt_override(variant_dir, variant)
    extra_env = {"PDD_PATH": pdd_path_override} if pdd_path_override else None
    sync_result = _run_pdd_sync(
        project_dir, scenario["basename"], timeout=timeout, extra_env=extra_env,
    )

    test_result = _run_pytest_on_result(project_dir, scenario["basename"])
    example_result = _run_example(project_dir, scenario["basename"])
    final_files = _collect_final_files(project_dir)

    return {
        "variant": variant,
        "sync": sync_result,
        "test": test_result,
        "example": example_result,
        "final_files": final_files,
        "project_dir": project_dir,
    }


def _evaluate_comparative(
    scenario: dict,
    improved_run: Dict[str, Any],
    original_run: Dict[str, Any],
) -> ComparativeResult:
    """Use LLM-as-judge to compare improved vs original prompt results."""
    from pdd.llm_invoke import llm_invoke

    reference_files = scenario["files"]

    # Build prompt via str.replace to avoid .format() brace interpretation issues.
    # All dynamic content can contain literal curly braces (Python code, f-strings,
    # diffs, error messages) which .format() would misinterpret as template variables.
    replacements = {
        "{scenario_description}": scenario["description"],
        "{expected_behavior}": scenario["expected_behavior"],
        "{evaluation_guidance}": scenario.get("evaluation_guidance", "No specific guidance."),
        "{reference_files}": _format_files_for_prompt(reference_files, max_chars=20000),
        "{current_cost:.4f}": f"{improved_run['sync']['cost']:.4f}",
        "{current_time:.1f}": f"{improved_run['sync']['wall_time']:.1f}",
        "{current_exit}": str(improved_run["sync"]["exit_code"]),
        "{current_test_exit}": str(improved_run["test"]["exit_code"]),
        "{current_test_count}": str(improved_run["test"]["test_count"]),
        "{current_example_exit}": str(improved_run["example"]["exit_code"]),
        "{current_diffs}": _compute_diffs(reference_files, improved_run["final_files"]),
        "{current_new_files}": _format_files_for_prompt(
            _get_new_files(reference_files, improved_run["final_files"]), max_chars=40000,
        ),
        "{current_stdout}": improved_run["sync"]["stdout"][:8000],
        "{original_cost:.4f}": f"{original_run['sync']['cost']:.4f}",
        "{original_time:.1f}": f"{original_run['sync']['wall_time']:.1f}",
        "{original_exit}": str(original_run["sync"]["exit_code"]),
        "{original_test_exit}": str(original_run["test"]["exit_code"]),
        "{original_test_count}": str(original_run["test"]["test_count"]),
        "{original_example_exit}": str(original_run["example"]["exit_code"]),
        "{original_diffs}": _compute_diffs(reference_files, original_run["final_files"]),
        "{original_new_files}": _format_files_for_prompt(
            _get_new_files(reference_files, original_run["final_files"]), max_chars=40000,
        ),
        "{original_stdout}": original_run["sync"]["stdout"][:8000],
    }
    prompt_text = COMPARATIVE_EVALUATOR_PROMPT
    for placeholder, value in replacements.items():
        prompt_text = prompt_text.replace(placeholder, value)

    response = llm_invoke(
        messages=[{"role": "user", "content": prompt_text}],
        strength=0.5,
        temperature=0.1,
        output_pydantic=ComparativeResult,
        use_cloud=False,
    )

    return response["result"]


def _log_comparative_result(
    scenario_name: str,
    scenario_description: str,
    comparison: ComparativeResult,
    improved_run: Dict[str, Any],
    original_run: Dict[str, Any],
) -> None:
    """Log comparative results and update cost tracker."""
    cur_cost = improved_run["sync"].get("cost", 0.0)
    cur_time = improved_run["sync"].get("wall_time", 0.0)
    orig_cost = original_run["sync"].get("cost", 0.0)
    orig_time = original_run["sync"].get("wall_time", 0.0)

    _COST_TRACKER[scenario_name] = {
        "current_cost": cur_cost,
        "current_time": cur_time,
        "original_cost": orig_cost,
        "original_time": orig_time,
    }

    dimensions = [
        ("test_quality", comparison.test_quality),
        ("example", comparison.example_quality),
        ("minimality", comparison.minimality),
        ("correctness", comparison.correctness),
        ("cost", comparison.cost),
        ("speed", comparison.speed),
    ]

    print(f"\n{'='*80}")
    print(f"  {scenario_description}")
    print(f"  Current: ${cur_cost:.2f} / {cur_time:.0f}s  |  Original: ${orig_cost:.2f} / {orig_time:.0f}s")
    print(f"{'='*80}")

    # Overall first
    overall_tag = comparison.overall.winner.upper()
    print(f"  OVERALL  ->  {overall_tag}")
    print(f"    {comparison.overall.one_line}")
    print()

    # Dimensions table — winner in middle column
    print(f"  {'Dimension':<16s}  {'Winner':^10s}  Summary")
    print(f"  {'-'*16}  {'-'*10}  {'-'*45}")
    for name, verdict in dimensions:
        tag = verdict.winner.upper()
        print(f"  {name:<16s}  {tag:^10s}  {verdict.one_line}")
    print()

    if comparison.agent_issues_current != "none":
        print(f"  Agent issues (current): {comparison.agent_issues_current}")
    if comparison.agent_issues_original != "none":
        print(f"  Agent issues (original): {comparison.agent_issues_original}")
    if comparison.prompt_improvement_suggestions != "none":
        print(f"  Prompt suggestions for 'current': {comparison.prompt_improvement_suggestions}")
    print(f"{'='*80}\n")


# =========================================================================
# Cost summary (session-scoped)
# =========================================================================

@pytest.fixture(scope="session", autouse=True)
def _print_eval_header_and_summary(request):
    """Print intro header and cost summary for the eval session."""
    print(
        "\n"
        "========================================================================\n"
        "  One-Session Eval: Prompt Comparison\n"
        "========================================================================\n"
        "  This test suite compares the CURRENT version of\n"
        "  one_session_agent_LLM.prompt against an ORIGINAL version from\n"
        "  before April 2026. Both prompt versions are run against curated\n"
        "  out-of-sync scenarios to see how each prompt guides the agent\n"
        "  through syncing up code, examples, and tests.\n"
        "  An LLM judge then evaluates the results side by side.\n"
        "========================================================================"
    )
    yield
    if _COST_TRACKER:
        total_cur = sum(v.get("current_cost", 0) for v in _COST_TRACKER.values())
        total_orig = sum(v.get("original_cost", 0) for v in _COST_TRACKER.values())
        total_cur_t = sum(v.get("current_time", 0) for v in _COST_TRACKER.values())
        total_orig_t = sum(v.get("original_time", 0) for v in _COST_TRACKER.values())
        print(f"\n{'='*70}")
        print("  One-Session Eval — Cost Summary (Current vs Original)")
        print(f"{'='*70}")
        print(f"  {'Scenario':30s}  {'Cur Cost':>10s} {'Cur Time':>10s}  {'Orig Cost':>10s} {'Orig Time':>10s}")
        for name, data in _COST_TRACKER.items():
            print(
                f"  {name:30s}"
                f"  ${data.get('current_cost', 0):8.4f} {data.get('current_time', 0):8.1f}s"
                f"  ${data.get('original_cost', 0):8.4f} {data.get('original_time', 0):8.1f}s"
            )
        print(
            f"  {'TOTAL':30s}"
            f"  ${total_cur:8.4f} {total_cur_t:8.1f}s"
            f"  ${total_orig:8.4f} {total_orig_t:8.1f}s"
        )
        print(f"{'='*70}\n")


# =========================================================================
# Shared test runner — runs both variants and compares
# =========================================================================

def _run_comparative_test(
    tmp_path: Path,
    scenario: dict,
    scenario_name: str,
    timeout: int = 480,
    hard_assertions_fn=None,
) -> ComparativeResult:
    """Run scenario with both prompts, compare side by side, and return verdict.

    hard_assertions_fn: optional callable(improved_run, original_run, scenario) for
    scenario-specific hard assertions on the improved variant.
    """
    # Run both variants in parallel — they use separate project directories
    with ThreadPoolExecutor(max_workers=2) as executor:
        current_future: Future = executor.submit(
            _run_scenario_variant, tmp_path, scenario, "current", timeout,
        )
        original_future: Future = executor.submit(
            _run_scenario_variant, tmp_path, scenario, "original", timeout,
        )
        improved_run = current_future.result()
        original_run = original_future.result()

    # Print failure details only when a variant didn't complete
    for label, run in [("CURRENT", improved_run), ("ORIGINAL", original_run)]:
        s = run["sync"]
        if s["exit_code"] != 0:
            timed_out = s.get("timed_out", False)
            print(
                f"\n  >> {label} FAILED: exit={s['exit_code']} wall={s['wall_time']:.0f}s "
                f"timed_out={timed_out}"
            )
            print(f"  >> stdout (last 2000 chars):\n{s['stdout'][-2000:]}")

    # Always run the LLM judge — even if one variant failed or timed out, the
    # judge's analysis of the partial stdout and diffs is valuable for understanding
    # what went wrong and improving the prompt.
    comparison = _evaluate_comparative(
        scenario, improved_run, original_run,
    )

    # Log everything
    _log_comparative_result(
        scenario_name, scenario["description"], comparison, improved_run, original_run,
    )

    # Hard assertions: current variant must at least complete
    assert improved_run["sync"]["exit_code"] == 0, (
        f"Current sync failed (timed_out={improved_run['sync'].get('timed_out')}): "
        f"{improved_run['sync']['stderr'][:500]}"
    )

    # Scenario-specific hard assertions on improved variant
    if hard_assertions_fn:
        hard_assertions_fn(improved_run, original_run, scenario)

    return comparison


# =========================================================================
# Test functions — S1 through S6
# =========================================================================

def test_s1_all_in_sync(tmp_path):
    """S1: Everything in sync. Current prompt should preserve existing tests."""

    def _hard_assertions(improved_run, original_run, scenario):
        assert improved_run["test"]["test_count"] >= 26, (
            f"Current agent must preserve existing tests (got {improved_run['test']['test_count']}, "
            f"expected >= 26)"
        )

    comparison = _run_comparative_test(
        tmp_path, S1_ALL_IN_SYNC, "s1_all_in_sync",
        hard_assertions_fn=_hard_assertions,
    )

    assert comparison.correctness.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should preserve existing work at least as well: {comparison.overall.explanation}"
    )


def test_s2_greenfield(tmp_path):
    """S2: Generate example + tests from scratch. Compare quality of generated artifacts."""

    def _hard_assertions(improved_run, original_run, scenario):
        ff = improved_run["final_files"]
        assert any("test_unit_converter" in p for p in ff), "Test file should be generated"
        assert any("unit_converter_example" in p for p in ff), "Example file should be generated"

    comparison = _run_comparative_test(
        tmp_path, S2_GREENFIELD, "s2_greenfield",
        hard_assertions_fn=_hard_assertions,
    )

    assert comparison.test_quality.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should produce at least as good test quality: {comparison.overall.explanation}"
    )


def test_s3_code_bug_shopping_cart(tmp_path):
    """S3: Code has >= bug. Compare how well each prompt diagnoses and fixes it."""

    def _hard_assertions(improved_run, original_run, scenario):
        code = improved_run["final_files"].get("src/shopping_cart.py", "")
        assert "subtotal >= 100" not in code or "subtotal > 100" in code, (
            "Current agent should have fixed the discount boundary bug"
        )

    comparison = _run_comparative_test(
        tmp_path, S3_CODE_BUG, "s3_code_bug",
        hard_assertions_fn=_hard_assertions,
    )

    assert comparison.correctness.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should handle bug fix at least as well: {comparison.overall.explanation}"
    )


def test_s4_expand_tests(tmp_path):
    """S4: Only 3 tests exist. Compare test expansion quality."""

    def _hard_assertions(improved_run, original_run, scenario):
        assert improved_run["test"]["test_count"] > 3, (
            f"Expected more than 3 tests, got {improved_run['test']['test_count']}"
        )

    comparison = _run_comparative_test(
        tmp_path, S4_MINIMAL_COVERAGE, "s4_expand_tests",
        hard_assertions_fn=_hard_assertions,
    )

    assert comparison.test_quality.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should produce at least as good test coverage: {comparison.overall.explanation}"
    )


def test_s5_fix_crashing_example(tmp_path):
    """S5: Example crashes. Compare how surgically each prompt fixes it."""

    def _hard_assertions(improved_run, original_run, scenario):
        example = improved_run["final_files"].get("examples/password_validator_example.py", "")
        assert "strict=True" not in example, "Current agent should remove strict=True"
        assert any("test_password_validator" in p for p in improved_run["final_files"]), (
            "Current agent should generate test file"
        )

    comparison = _run_comparative_test(
        tmp_path, S5_CRASHING_EXAMPLE, "s5_fix_example",
        hard_assertions_fn=_hard_assertions,
    )

    assert comparison.minimality.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should make more surgical fixes: {comparison.overall.explanation}"
    )


def test_s6_fix_wrong_tests(tmp_path):
    """S6: Tests assume inclusive intervals. Compare correctness of diagnosis."""

    def _hard_assertions(improved_run, original_run, scenario):
        original_code = scenario["files"]["src/date_range.py"]
        final_code = improved_run["final_files"].get("src/date_range.py", "")
        assert final_code.strip() == original_code.strip(), (
            "Current agent should fix tests, not code."
        )

    comparison = _run_comparative_test(
        tmp_path, S6_WRONG_TESTS, "s6_wrong_tests",
        hard_assertions_fn=_hard_assertions,
    )

    assert comparison.correctness.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should correctly identify tests as wrong: {comparison.overall.explanation}"
    )


# =========================================================================
# Test functions — S7 through S9 (large scenarios from fixtures)
# =========================================================================

def test_s7_large_code_bug(tmp_path):
    """S7: Large module with code bug. Compare diagnosis ability at scale."""
    scenario = _load_fixture_scenario("s7_large_code_bug")

    comparison = _run_comparative_test(
        tmp_path, scenario, "s7_large_code_bug", timeout=720,
    )

    assert comparison.correctness.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should handle large module bug fix at least as well: {comparison.overall.explanation}"
    )


def test_s8_large_minimal_tests(tmp_path):
    """S8: Large module with minimal tests. Compare test expansion quality at scale."""
    scenario = _load_fixture_scenario("s8_large_minimal_tests")

    def _hard_assertions(improved_run, original_run, sc):
        assert improved_run["test"]["test_count"] > 5, (
            f"Expected more than 5 tests, got {improved_run['test']['test_count']}"
        )

    comparison = _run_comparative_test(
        tmp_path, scenario, "s8_large_minimal_tests", timeout=720,
        hard_assertions_fn=_hard_assertions,
    )

    assert comparison.test_quality.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should produce better tests at scale: {comparison.overall.explanation}"
    )


def test_s9_large_wrong_tests(tmp_path):
    """S9: Large module with wrong tests. Compare diagnosis at scale."""
    scenario = _load_fixture_scenario("s9_large_wrong_tests")

    def _hard_assertions(improved_run, original_run, sc):
        original_code_key = [k for k in sc["files"] if k.startswith("src/")][0]
        original_code = sc["files"][original_code_key]
        final_code = improved_run["final_files"].get(original_code_key, "")
        assert final_code.strip() == original_code.strip(), (
            "Current agent should fix tests, not code."
        )

    comparison = _run_comparative_test(
        tmp_path, scenario, "s9_large_wrong_tests", timeout=720,
        hard_assertions_fn=_hard_assertions,
    )

    assert comparison.correctness.winner != "original" or comparison.overall.winner != "original", (
        f"Current prompt should correctly fix wrong tests at scale: {comparison.overall.explanation}"
    )
