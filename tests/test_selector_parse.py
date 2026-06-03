from __future__ import annotations

from pdd._selector_parse import parse_selectors_string


def test_parse_keeps_comma_in_pytest_value():
    assert parse_selectors_string("pytest:test_one,test_two") == [
        "pytest:test_one,test_two"
    ]
