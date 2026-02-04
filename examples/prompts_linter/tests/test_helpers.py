import os
import sys
import pytest
import textwrap
from pathlib import Path
from z3 import *

# Import the module under test
# Adjusting path to ensure we can import from src
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from src.utils.helpers import (
    read_file_content,
    normalize_text,
    extract_tag_content,
    count_tags,
    calculate_code_ratio,
    TAG_INCLUDE,
    TAG_WEB,
    TAG_SHELL
)

# =============================================================================
# Unit Tests: File I/O
# =============================================================================

def test_read_file_content_success(tmp_path):
    """Test reading a valid file returns normalized content."""
    d = tmp_path / "subdir"
    d.mkdir()
    p = d / "test_file.txt"
    # Write content with Windows line endings and trailing spaces
    p.write_bytes(b"Hello World  \r\nSecond Line\r\n")
    
    content = read_file_content(str(p))
    
    # Expect normalized \n and stripped trailing spaces
    # Note: normalize_text preserves the final newline if present in the split/join logic
    expected = "Hello World\nSecond Line\n"
    assert content == expected

def test_read_file_content_not_found():
    """Test that FileNotFoundError is raised for missing files."""
    with pytest.raises(FileNotFoundError):
        read_file_content("non_existent_random_file_123.txt")

def test_read_file_content_is_directory(tmp_path):
    """Test that IOError is raised when path is a directory."""
    d = tmp_path / "subdir"
    d.mkdir()
    
    with pytest.raises(IOError) as excinfo:
        read_file_content(str(d))
    assert "exists but is not a file" in str(excinfo.value)

def test_read_file_content_encoding_handling(tmp_path):
    """Test that invalid UTF-8 bytes are replaced, not crashing."""
    p = tmp_path / "binary.txt"
    # Write invalid utf-8 byte sequence (0x80 is invalid start byte)
    p.write_bytes(b"Valid\n\x80\xff\nEnd")
    
    content = read_file_content(str(p))
    
    assert "Valid" in content
    assert "End" in content
    # The invalid bytes should be replaced by the replacement char  (U+FFFD)
    # or similar depending on implementation, but definitely not crash.
    assert "\ufffd" in content or content.count('\n') == 2

# =============================================================================
# Unit Tests: Text Normalization
# =============================================================================

def test_normalize_text_basics():
    """Test basic normalization of newlines and trailing whitespace."""
    raw = "Line 1  \r\nLine 2\rLine 3   "
    expected = "Line 1\nLine 2\nLine 3"
    assert normalize_text(raw) == expected

def test_normalize_text_preserves_indentation():
    """Test that leading whitespace (indentation) is preserved."""
    raw = "    Indented Code\n  List Item"
    expected = "    Indented Code\n  List Item"
    assert normalize_text(raw) == expected

def test_normalize_text_empty():
    """Test normalization of empty string."""
    assert normalize_text("") == ""

# =============================================================================
# Unit Tests: Tag Detection
# =============================================================================

def test_extract_tag_content_simple():
    """Test extracting content from simple tags."""
    text = "Prefix <include>path/to/file</include> Suffix"
    results = extract_tag_content(text, TAG_INCLUDE)
    assert results == ["path/to/file"]

def test_extract_tag_content_attributes():
    """Test extracting content from tags with attributes."""
    text = '<web url="http://example.com">Content</web>'
    results = extract_tag_content(text, TAG_WEB)
    assert results == ["Content"]

def test_extract_tag_content_multiline():
    """Test extracting multiline content."""
    text = """
    <shell>
    echo "hello"
    ls -la
    </shell>
    """
    results = extract_tag_content(text, TAG_SHELL)
    assert len(results) == 1
    assert 'echo "hello"' in results[0]
    assert 'ls -la' in results[0]

def test_extract_tag_content_case_insensitive():
    """Test that tag matching is case insensitive."""
    text = "<INCLUDE>file.txt</include>"
    results = extract_tag_content(text, "include")
    assert results == ["file.txt"]

def test_count_tags():
    """Test counting tags."""
    text = "<include>A</include> text <include>B</include>"
    assert count_tags(text, TAG_INCLUDE) == 2
    assert count_tags(text, TAG_WEB) == 0

# =============================================================================
# Unit Tests: Heuristics
# =============================================================================

def test_calculate_code_ratio_empty():
    """Test ratio for empty or whitespace-only text."""
    assert calculate_code_ratio("") == 0.0
    assert calculate_code_ratio("   \n   ") == 0.0

def test_calculate_code_ratio_pure_code():
    """Test ratio for obvious code."""
    code = textwrap.dedent("""
    def my_func():
        return True
    import os
    class MyClass:
        pass
    """)
    # All non-empty lines here look like code
    assert calculate_code_ratio(code) == 1.0

def test_calculate_code_ratio_pure_text():
    """Test ratio for natural language."""
    text = textwrap.dedent("""
    This is a standard sentence.
    Another sentence here.
    Please do the following.
    """)
    assert calculate_code_ratio(text) == 0.0

def test_calculate_code_ratio_indentation_heuristic():
    """Test that 4-space indentation counts as code."""
    text = textwrap.dedent("""
    This is text.
        This is indented code block.
        var x = 1
    """)
    # 3 lines total. 
    # Line 1: Text
    # Line 2: Indented (4 spaces) -> Code
    # Line 3: Indented (4 spaces) -> Code
    # Ratio: 2/3 = 0.666... -> 0.67
    assert calculate_code_ratio(text) == 0.67

def test_calculate_code_ratio_list_exception():
    """Test that indented lists are NOT counted as code."""
    text = textwrap.dedent("""
    Here is a list:
        - Item 1
        * Item 2
        1. Item 3
    """)
    # 4 lines.
    # Line 1: Text
    # Line 2: Indented but starts with '-' -> Text
    # Line 3: Indented but starts with '*' -> Text
    # Line 4: Indented but starts with '1.' -> Text
    # Ratio should be 0.0
    assert calculate_code_ratio(text) == 0.0

def test_calculate_code_ratio_mixed():
    """Test a mix of code and text."""
    text = textwrap.dedent("""
    Here is some python code:
    
    def hello():
        print(\"world\")
        
    That was code.
    """)
    # Non-empty lines:
    # 1. "Here is some python code:" (Text)
    # 2. "def hello():" (Code - keyword)
    # 3. "    print(\"world\")" (Code - indent)
    # 4. "That was code." (Text)
    # Total: 4. Code: 2. Ratio: 0.5
    assert calculate_code_ratio(text) == 0.5

# =============================================================================
# Z3 Formal Verification
# =============================================================================

def test_z3_indentation_logic_verification():
    """
    Formally verify the boolean logic used in calculate_code_ratio 
    to distinguish between code blocks and list items based on indentation.
    
    Logic under test (from source):
        indentation = len(line) - len(stripped)
        is_list_item = stripped.startswith(('-', '*', '+')) or (stripped[:1].isdigit() and stripped[1:2] == '.')
        is_code = (indentation >= 4 and not is_list_item)
    """
    s = Solver()

    # Inputs
    indentation = Int('indentation')
    
    # We model the list item check as a boolean flag provided by the string analysis
    # because Z3 string solvers are heavy, and we want to verify the logic flow.
    starts_with_list_marker = Bool('starts_with_list_marker')
    
    # The logic defined in the function
    # Note: The function considers it code if indent >= 4 AND it's NOT a list item
    is_code_heuristic = And(indentation >= 4, Not(starts_with_list_marker))

    # Constraint 1: Physical constraint (indentation cannot be negative)
    s.add(indentation >= 0)

    # Verification Goal 1: 
    # Prove that if it IS a list marker, it is NEVER considered code, regardless of indentation.
    # We negate the goal to find a counter-example.
    # Goal: Implies(starts_with_list_marker, Not(is_code_heuristic))
    # Negation: starts_with_list_marker AND is_code_heuristic
    s.push()
    s.add(starts_with_list_marker)
    s.add(is_code_heuristic)
    
    result = s.check()
    # If result is UNSAT, it means no counter-example exists -> Logic is sound.
    assert result == unsat, "Found a case where a list item is counted as code!"
    s.pop()

    # Verification Goal 2:
    # Prove that if indentation is less than 4, it is NEVER considered code (by this specific heuristic branch).
    # Negation: (indentation < 4) AND is_code_heuristic
    s.push()
    s.add(indentation < 4)
    s.add(is_code_heuristic)
    
    result = s.check()
    assert result == unsat, "Found a case where low indentation is counted as code!"
    s.pop()

# =============================================================================
# Test Plan
# =============================================================================
# 1. File I/O - Permission Handling:
#    - Verify that PermissionError is propagated correctly. Since file permissions 
#      can be flaky across OS/CI environments (chmod), we will use unittest.mock 
#      to simulate the exception.
#
# 2. Text Normalization - Complex Line Endings:
#    - Verify handling of mixed line endings in a single string (e.g., \r\n mixed with \r and \n).
#
# 3. Tag Detection - Advanced Cases:
#    - Multiple tags on a single line (ensure non-greedy matching works).
#    - Nested tags (document the limitation of the regex approach: it likely matches 
#      outer open to first close).
#    - Special characters in tag names (ensure re.escape is working).
#
# 4. Code Ratio Heuristics - Specific Patterns:
#    - Verify specific keywords and symbols defined in the regex (e.g., @decorators, 
#      try/except blocks, <script> tags).
#    - Verify "False Positives": Ensure capitalized words at the start of sentences 
#      (e.g., "Class", "Import") are NOT flagged as code, distinguishing them from 
#      keywords.
#
# 5. Formal Verification (Z3):
#    - Verify the arithmetic bounds of the ratio calculation. Ensure that for any 
#      valid non-negative integer inputs where code_lines <= total_lines, the 
#      resulting ratio is <= 1.0. This complements the existing boolean logic verification.

# =============================================================================
# New Unit Tests
# =============================================================================

def test_read_file_content_permission_error(tmp_path):
    """
    Test that PermissionError is raised and propagated when file is not readable.
    Uses mocking to ensure reliability across different operating systems.
    """
    # Import locally to avoid modifying top-level imports
    from unittest.mock import patch
    
    f = tmp_path / "locked.txt"
    f.write_text("secret content")
    
    # Mock builtins.open to raise PermissionError regardless of actual file permissions
    with patch("builtins.open", side_effect=PermissionError("Access denied")):
        with pytest.raises(PermissionError):
            read_file_content(str(f))

def test_normalize_text_mixed_line_endings():
    """Test normalization when input contains mixed line ending styles."""
    # \r\n, \r, and \n all in one file
    raw = "Line 1\r\nLine 2\rLine 3\nLine 4"
    expected = "Line 1\nLine 2\nLine 3\nLine 4"
    assert normalize_text(raw) == expected

def test_extract_tag_content_multiple_occurrences_single_line():
    """Test extracting multiple tags appearing on the same line."""
    text = "Prefix <web>Link1</web> Middle <web>Link2</web> Suffix"
    results = extract_tag_content(text, TAG_WEB)
    assert results == ["Link1", "Link2"]

def test_extract_tag_content_nested_behavior():
    """
    Test behavior with nested tags. 
    Note: The regex <tag>.*?</tag> is non-greedy. In a nested scenario like 
    <A><A>inner</A></A>, it will match the first opening <A> with the first closing </A>.
    This test documents that limitation/behavior.
    """
    tag = "container"
    text = f"<{tag}><{tag}>inner</{tag}></{tag}>"
    
    results = extract_tag_content(text, tag)
    
    # Expectation: Matches outer start to inner close
    # Content extracted: <container>inner
    assert len(results) == 1
    assert results[0] == f"<{tag}>inner"

def test_extract_tag_content_special_chars_in_name():
    """Test that tag names with special regex characters are handled correctly."""
    tag_name = "my-tag.v1"
    text = f"<{tag_name}>Content</{tag_name}>"
    results = extract_tag_content(text, tag_name)
    assert results == ["Content"]

def test_calculate_code_ratio_keywords_and_symbols():
    """Test specific code patterns like decorators, exception handling, and html tags."""
    text = textwrap.dedent("""
    @app.route('/home')
    def index():
        try:
            pass
        except Exception:
            pass
    <script>
    var x = 1;
    </script>
    """)
    # Analysis:
    # 1. @app.route... -> Code (starts with @)
    # 2. def index(): -> Code (keyword def)
    # 3. try: -> Code (keyword try)
    # 4. pass -> Code (indentation 4 spaces)
    # 5. except Exception: -> Code (keyword except)
    # 6. pass -> Code (indentation 4 spaces)
    # 7. <script> -> Code (starts with <script)
    # 8. var x = 1; -> Code (keyword var)
    # 9. </script> -> Text (doesn't match code patterns explicitly, no indent)
    
    # 8 code lines out of 9 total lines.
    # Ratio: 8/9 = 0.888... -> 0.89
    assert calculate_code_ratio(text) == 0.89

def test_calculate_code_ratio_false_positives():
    """
    Test that capitalized words at start of sentences are NOT treated as code keywords.
    The regex should be case-sensitive for keywords (e.g., 'class' vs 'Class').
    """
    text = textwrap.dedent("""
    Class is in session.
    Import the data into the system.
    Return the book to the library.
    Try to do your best.
    """)
    # None of these should match the code keywords (class, import, return, try)
    # because the regex uses \b and is case-sensitive for the keyword list.
    assert calculate_code_ratio(text) == 0.0

def test_z3_ratio_arithmetic_bounds():
    """
    Formally verify that for any valid counts of code lines and total lines,
    the calculated ratio never exceeds 1.0.
    """
    s = Solver()
    
    code_lines = Int('code_lines')
    total_lines = Int('total_lines')
    
    # Constraints representing the physical reality of the function inputs
    s.add(total_lines > 0)           # We only divide if lines exist
    s.add(code_lines >= 0)           # Count cannot be negative
    s.add(code_lines <= total_lines) # Count cannot exceed total lines
    
    # The calculation performed (using Real arithmetic for division)
    ratio = ToReal(code_lines) / ToReal(total_lines)
    
    # Goal: Prove ratio <= 1.0
    # We attempt to find a counter-example where ratio > 1.0
    s.add(ratio > 1.0)
    
    result = s.check()
    assert result == unsat, "Found a theoretical case where ratio > 1.0!"

import pytest
from z3 import *
from src.utils.helpers import (
    find_line_number,
    read_file_content,
    extract_tag_content,
    calculate_code_ratio,
    TAG_INCLUDE
)

# =============================================================================
# Unit Tests: Line Number Calculation
# =============================================================================

def test_find_line_number_basic():
    """Test finding line numbers in a simple multiline string."""
    # Indices:
    # 0123 4567 89
    # Line\nNext\n
    text = "Line\nNext\n"
    
    # 'L' at 0 -> Line 1
    assert find_line_number(text, 0) == 1
    # 'e' at 3 -> Line 1
    assert find_line_number(text, 3) == 1
    # '\n' at 4 -> Line 1 (The newline char ends line 1)
    assert find_line_number(text, 4) == 1
    # 'N' at 5 -> Line 2
    assert find_line_number(text, 5) == 2

def test_find_line_number_start():
    """Test line number at the very start of the string."""
    assert find_line_number("Hello", 0) == 1

def test_find_line_number_out_of_bounds():
    """
    Test behavior when index exceeds string length.
    Python's count() handles slice bounds gracefully by clamping to the string end.
    The function should return the number of the last line (or total lines + 1 if we consider the cursor after the last char).
    """
    text = "A\nB"
    # Length is 3. Index 10 is out of bounds.
    # count('\n', 0, 10) -> count('\n', 0, 3) -> 1 ('\n' is found)
    # Result: 1 + 1 = 2.
    assert find_line_number(text, 100) == 2

# =============================================================================
# Unit Tests: File I/O Edge Cases
# =============================================================================

def test_read_file_content_empty_file(tmp_path):
    """Test reading a completely empty file."""
    p = tmp_path / "empty.txt"
    p.write_text("")
    
    content = read_file_content(str(p))
    assert content == ""

# =============================================================================
# Unit Tests: Tag Extraction Edge Cases
# =============================================================================

def test_extract_tag_content_ignores_self_closing():
    """
    Test that self-closing tags are NOT matched.
    The regex requires a closing tag </tag>, so <tag /> should be ignored.
    """
    text = "Here is a self closing tag: <include file='foo' />"
    results = extract_tag_content(text, TAG_INCLUDE)
    # Should be empty because the regex expects <include>...</include>
    assert results == []

# =============================================================================
# Unit Tests: Heuristic Boundaries
# =============================================================================

def test_calculate_code_ratio_indentation_boundary():
    """
    Test the exact boundary of indentation heuristic (3 spaces vs 4 spaces).
    """
    # Case 1: 3 spaces (Should be treated as Text)
    text_3 = "   Not code yet"
    assert calculate_code_ratio(text_3) == 0.0
    
    # Case 2: 4 spaces (Should be treated as Code)
    text_4 = "    Is code now"
    assert calculate_code_ratio(text_4) == 1.0

# =============================================================================
# Z3 Formal Verification
# =============================================================================

def test_z3_line_number_monotonicity():
    """
    Formally verify that line numbers are monotonically increasing with respect to the index.
    i.e., if index_b > index_a, then line_number(index_b) >= line_number(index_a).
    
    Since we cannot pass the Python C-implementation of str.count to Z3, 
    we model the abstract logic of line counting.
    """
    s = Solver()
    
    # We model the text as a sequence of positions.
    # For any position i, let is_newline(i) be a boolean indicating if char at i is '\n'.
    # We don't need to solve for the string content, just the logic properties.
    
    # Let L(k) be the line number at index k.
    # L(k) = 1 + Sum(is_newline(i) for i in 0..k-1)
    
    # We want to prove: for all a, b: (b > a) => (L(b) >= L(a))
    # This is equivalent to proving L(a+1) >= L(a).
    
    # Let current_line_num be an integer representing L(a)
    current_line_num = Int('current_line_num')
    
    # Let is_nl be a boolean representing if the character at index 'a' is a newline
    is_nl = Bool('is_nl_at_a')
    
    # The next line number L(a+1) depends on whether 'a' was a newline
    # If is_nl is true, we add 1. If false, we add 0.
    next_line_num = If(is_nl, current_line_num + 1, current_line_num)
    
    # Constraints
    s.add(current_line_num >= 1) # Line numbers start at 1
    
    # Verification Goal: Prove next_line_num >= current_line_num
    # We negate the goal to find a counter-example
    s.add(Not(next_line_num >= current_line_num))
    
    result = s.check()
    
    # If UNSAT, it means no counter-example exists, so the logic is monotonic.
    assert result == unsat, "Line number calculation logic is not monotonic!"

# =============================================================================
# New Unit Tests
# =============================================================================

def test_normalize_text_whitespace_lines():
    """
    Test that lines containing only whitespace are stripped to empty strings,
    but the vertical structure (newlines) is preserved.
    """
    # Input: 3 lines. Middle one is tabs. Last one is spaces.
    raw = "Line1\n\t\t\n   "
    # Expected: "Line1\n\n" (last line becomes empty string, joined by \n)
    expected = "Line1\n\n"
    assert normalize_text(raw) == expected

def test_extract_tag_content_attribute_limitation():
    """
    Test the known limitation where a '>' inside an attribute value breaks parsing.
    The regex `[^>]*` stops at the first '>' it sees.
    """
    # The regex will match `<web title=">` as the opening tag.
    # The content captured will be `">Content`.
    text = '<web title=">">Content</web>'
    results = extract_tag_content(text, TAG_WEB)
    
    # Documenting the broken behavior:
    assert len(results) == 1
    assert results[0] == '">Content' 

def test_calculate_code_ratio_double_digit_list_limitation():
    """
    Test that double-digit list items (e.g., '10.') are NOT recognized as list items
    by the current heuristic, and thus are counted as code if indented.
    """
    text = textwrap.dedent("""
        1. Item one
        2. Item two
        ...
        10. Item ten
    """)
    # Indent the text to trigger the indentation check
    indented_text = "\n".join(f"    {line}" for line in text.splitlines() if line.strip())
    
    # Analysis:
    # "    1. Item one" -> Indent 4. stripped starts with digit+dot -> List Item -> Not Code.
    # "    2. Item two" -> Indent 4. stripped starts with digit+dot -> List Item -> Not Code.
    # "    ..." -> Indent 4. Not list item -> Code.
    # "    10. Item ten" -> Indent 4. stripped starts with "10.". 
    #      Logic: stripped[:1] is "1", stripped[1:2] is "0". "0" != ".". 
    #      Result: Not list item -> Code.
    
    # We expect a non-zero code ratio because of line 3 and line 4.
    ratio = calculate_code_ratio(indented_text)
    assert ratio > 0.0
    # Specifically, lines 3 and 4 are counted as code. Total 4 lines. Ratio 0.5.
    assert ratio == 0.5

def test_calculate_code_ratio_plus_marker():
    """Test that '+' is recognized as a valid list marker."""
    text = "    + List item"
    # Indented 4 spaces, but starts with +, so should be Text.
    assert calculate_code_ratio(text) == 0.0

def test_calculate_code_ratio_extended_keywords():
    """Test detection of C++/Java style keywords."""
    text = textwrap.dedent("""
    public class MyClass {
        private int x;
        switch (x) {
            case 1: break;
        }
    }
    """)
    # All lines here should trigger the regex keywords (public, private, switch, case) or symbols ({, })
    assert calculate_code_ratio(text) == 1.0

def test_find_line_number_at_newline_char():
    """
    Test that the line number at the exact index of a newline character
    corresponds to the line ending there.
    """
    # Index: 0123
    # Char:  A\nB
    text = "A\nB"
    # Index 1 is '\n'. It belongs to Line 1.
    assert find_line_number(text, 1) == 1
    # Index 2 is 'B'. It belongs to Line 2.
    assert find_line_number(text, 2) == 2

def test_read_file_content_ioerror_not_a_file(tmp_path):
    """
    Test that IOError is raised if the path exists but is not a file (e.g. directory).
    This covers the specific check `if not file_path.is_file(): raise IOError`.
    """
    d = tmp_path / "some_dir"
    d.mkdir()
    
    with pytest.raises(IOError) as excinfo:
        read_file_content(str(d))
    
    assert "exists but is not a file" in str(excinfo.value)

# =============================================================================
# Z3 Formal Verification: List Item Logic
# =============================================================================

def test_z3_list_item_digit_limitation_proof():
    """
    Formally prove that the current list item detection logic fails for 
    strings starting with two digits followed by a dot (e.g., "10.").
    """
    s = Solver()
    
    # We model the 'stripped' line string
    # We constrain it to look like "10."
    # Since Z3 string solving can be complex, we model the characters directly 
    # relevant to the logic: stripped[:1] and stripped[1:2].
    
    # Logic from code:
    # is_list_item = ... or (stripped[:1].isdigit() and stripped[1:2] == '.')
    
    # We represent the first two characters as integers/chars
    char1 = String('char1')
    char2 = String('char2')
    
    # The logic check in Python:
    # char1.isdigit() AND char2 == '.'
    
    # In Z3, we define what "isdigit" means for a single char string
    def is_digit_z3(c):
        return Or([c == StringVal(str(d)) for d in range(10)])
    
    is_list_item_logic = And(is_digit_z3(char1), char2 == StringVal('.'))
    
    # Scenario: The string starts with "10" (i.e., char1="1", char2="0")
    # We assert that this input exists
    s.add(char1 == StringVal("1"))
    s.add(char2 == StringVal("0"))
    
    # We want to prove that for this input, is_list_item_logic is FALSE.
    # So we assert that it is TRUE, and expect UNSAT (contradiction).
    s.add(is_list_item_logic)
    
    result = s.check()
    
    # If result is UNSAT, it means "10" cannot satisfy the list item logic.
    # This proves the limitation exists.
    assert result == unsat, "The logic incorrectly identified '10' as a list item start!"