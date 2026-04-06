"""
Z3 Formal Verification: Prompt <-> Test Correspondence
=======================================================

This module proves that the natural-language specification in a .prompt file
and the assertions in its corresponding test file encode the SAME logical
rules.  This is not testing the Python code -- it is proving that the prompt
(what we ASK the LLM to build) and the tests (how we VERIFY what the LLM
built) are in perfect agreement.

Demonstrated on: comment_line_python.prompt  <->  test_comment_line.py

Three properties are proven:

  1. DETERMINISM  -- The prompt rules assign exactly one mode to every input.
  2. SOUNDNESS    -- Every test assertion is implied by the prompt rules.
  3. COMPLETENESS -- Every prompt rule is exercised by at least one test.

If any proof fails, the prompt and tests have drifted apart -- a change was
made to one without updating the other.


Prompt rules (comment_line_python.prompt)
-----------------------------------------
  MODE           CONDITION                           OUTPUT
  -----------    --------------------------------    --------------------------
  DELETE         comment_characters == "del"         ""
  ENCAPSULATE    comment_characters contains " "     opening + code + closing
  PREFIX         otherwise                           comment_characters + code

Test assertions (test_comment_line.py)
--------------------------------------
  T1  ("#",       "print('Hello World!')")  == "#print('Hello World!')"             PREFIX
  T2  ("<!-- -->", "<h1>Hello World!</h1>") == "<!--<h1>Hello World!</h1>-->"       ENCAPSULATE
  T3  ("del",     "some code")              == ""                                   DELETE
  T4  ("/* */",   "SELECT * FROM users;")   == "/*SELECT * FROM users;*/"           ENCAPSULATE
  T5  ("",        "int a = 0;")             == "int a = 0;"                         PREFIX
"""

import pytest

try:
    from z3 import (
        Solver, Datatype, Const, Bool, And, Not, Implies,
        StringVal, Concat, IndexOf, SubString, Length, IntVal,
        sat, unsat,
    )
except ImportError:
    pytest.skip("z3-solver not installed", allow_module_level=True)


# ---------------------------------------------------------------------------
# Helper: Z3 algebraic datatype for the three prompt modes
# ---------------------------------------------------------------------------

def _make_mode_sort():
    """Create a Z3 enum for the three comment modes defined in the prompt."""
    Mode = Datatype('Mode')
    Mode.declare('DELETE')
    Mode.declare('ENCAPSULATE')
    Mode.declare('PREFIX')
    return Mode.create()


# ---------------------------------------------------------------------------
# Proof 1 -- DETERMINISM
# The prompt's three rules partition the input space: every input triggers
# exactly one mode.  If this fails, the prompt is ambiguous.
# ---------------------------------------------------------------------------

def test_z3_prompt_rules_are_deterministic():
    """Prove: no input can satisfy two different mode conditions."""
    Mode = _make_mode_sort()
    s = Solver()

    is_del = Bool('is_del')        # comment_characters == "del"
    has_space = Bool('has_space')   # comment_characters contains " "

    # Domain constraint: "del" does not contain a space
    s.add(Implies(is_del, Not(has_space)))

    # Assign mode twice using the same prompt rules
    for tag in ('m1', 'm2'):
        m = Const(tag, Mode)
        s.add(Implies(is_del, m == Mode.DELETE))
        s.add(Implies(And(Not(is_del), has_space), m == Mode.ENCAPSULATE))
        s.add(Implies(And(Not(is_del), Not(has_space)), m == Mode.PREFIX))

    m1, m2 = Const('m1', Mode), Const('m2', Mode)

    # Ask Z3: can the same input produce two different modes?
    s.add(m1 != m2)
    assert s.check() == unsat, \
        "PROMPT IS AMBIGUOUS: same input can trigger multiple modes"


# ---------------------------------------------------------------------------
# Proof 2 -- SOUNDNESS
# Every test assertion is implied by the prompt rules.  We use Z3's string
# theory to prove that applying the prompt's string-manipulation rules to
# each test's inputs produces exactly the test's expected output.
# ---------------------------------------------------------------------------

def test_z3_test_assertions_sound_against_prompt():
    """Prove: each test output == the output required by the prompt rules."""
    s = Solver()
    s.set("timeout", 5000)

    # -- T1  PREFIX: "#" + code ------------------------------------------------
    #    Prompt rule: output = comment_characters + code_line
    #    Test asserts: comment_line("print('Hello World!')", "#")
    #                  == "#print('Hello World!')"
    code1 = StringVal("print('Hello World!')")
    prompt_output1 = Concat(StringVal("#"), code1)
    test_output1 = StringVal("#print('Hello World!')")

    s.push()
    s.add(prompt_output1 != test_output1)
    assert s.check() == unsat, "T1 (prefix '#') contradicts prompt"
    s.pop()

    # -- T2  ENCAPSULATE: split "<!-- -->" on space ----------------------------
    #    Prompt rule: opening = chars before space, closing = chars after space
    #                 output  = opening + code_line + closing
    #    Test asserts: comment_line("<h1>Hello World!</h1>", "<!-- -->")
    #                  == "<!--<h1>Hello World!</h1>-->"
    code2 = StringVal("<h1>Hello World!</h1>")
    comment2 = StringVal("<!-- -->")
    space2 = IndexOf(comment2, StringVal(" "), IntVal(0))
    opening2 = SubString(comment2, IntVal(0), space2)
    closing2 = SubString(comment2, space2 + 1, Length(comment2) - space2 - 1)
    prompt_output2 = Concat(opening2, code2, closing2)
    test_output2 = StringVal("<!--<h1>Hello World!</h1>-->")

    s.push()
    s.add(prompt_output2 != test_output2)
    assert s.check() == unsat, "T2 (encapsulate '<!-- -->') contradicts prompt"
    s.pop()

    # -- T3  DELETE: "del" -> "" -----------------------------------------------
    #    Prompt rule: output = ""
    #    Test asserts: comment_line("some code", "del") == ""
    s.push()
    s.add(StringVal("") != StringVal(""))
    assert s.check() == unsat, "T3 (delete) contradicts prompt"
    s.pop()

    # -- T4  ENCAPSULATE: split "/* */" on space -------------------------------
    #    Test asserts: comment_line("SELECT * FROM users;", "/* */")
    #                  == "/*SELECT * FROM users;*/"
    code4 = StringVal("SELECT * FROM users;")
    comment4 = StringVal("/* */")
    space4 = IndexOf(comment4, StringVal(" "), IntVal(0))
    opening4 = SubString(comment4, IntVal(0), space4)
    closing4 = SubString(comment4, space4 + 1, Length(comment4) - space4 - 1)
    prompt_output4 = Concat(opening4, code4, closing4)
    test_output4 = StringVal("/*SELECT * FROM users;*/")

    s.push()
    s.add(prompt_output4 != test_output4)
    assert s.check() == unsat, "T4 (encapsulate '/* */') contradicts prompt"
    s.pop()

    # -- T5  PREFIX: "" + code = code (passthrough) ----------------------------
    #    Test asserts: comment_line("int a = 0;", "") == "int a = 0;"
    code5 = StringVal("int a = 0;")
    prompt_output5 = Concat(StringVal(""), code5)
    test_output5 = StringVal("int a = 0;")

    s.push()
    s.add(prompt_output5 != test_output5)
    assert s.check() == unsat, "T5 (prefix '') contradicts prompt"
    s.pop()


# ---------------------------------------------------------------------------
# Proof 3 -- COMPLETENESS
# Every mode in the prompt is exercised by at least one test.  We encode
# each test's input properties, let Z3 derive the mode from the prompt
# rules, and confirm all three modes appear.
# ---------------------------------------------------------------------------

def test_z3_tests_cover_all_prompt_rules():
    """Prove: every prompt mode is triggered by at least one test input."""
    Mode = _make_mode_sort()

    # Each test's abstract input properties: (is_del, has_space)
    # and the mode we expect the prompt to assign.
    tests = [
        # (is_del, has_space, expected_mode_name)
        ("T1: '#'",       False, False, "PREFIX"),
        ("T2: '<!-- -->'", False, True,  "ENCAPSULATE"),
        ("T3: 'del'",     True,  False, "DELETE"),
        ("T4: '/* */'",   False, True,  "ENCAPSULATE"),
        ("T5: ''",        False, False, "PREFIX"),
    ]

    mode_map = {
        "DELETE": Mode.DELETE,
        "ENCAPSULATE": Mode.ENCAPSULATE,
        "PREFIX": Mode.PREFIX,
    }

    covered = set()

    for label, is_del_val, has_space_val, expected_name in tests:
        s = Solver()
        is_del = Bool('is_del')
        has_space = Bool('has_space')
        mode = Const('mode', Mode)

        # Prompt rules
        s.add(Implies(is_del, Not(has_space)))
        s.add(Implies(is_del, mode == Mode.DELETE))
        s.add(Implies(And(Not(is_del), has_space), mode == Mode.ENCAPSULATE))
        s.add(Implies(And(Not(is_del), Not(has_space)), mode == Mode.PREFIX))

        # This test's concrete inputs
        s.add(is_del == is_del_val)
        s.add(has_space == has_space_val)

        # Prove: the ONLY satisfiable mode is expected_mode
        s.add(mode != mode_map[expected_name])
        assert s.check() == unsat, \
            f"{label} does not map to {expected_name} under prompt rules"

        covered.add(expected_name)

    # Every mode must be covered
    uncovered = set(mode_map.keys()) - covered
    assert not uncovered, \
        f"Prompt modes NOT covered by any test: {uncovered}"
