import json
import re

import pytest

from pdd.architecture_sync import parse_prompt_tags
from pdd.preprocess import preprocess


def _pdd_interface_payloads(text: str) -> list[dict]:
    matches = re.findall(r"<pdd-interface>(.*?)</pdd-interface>", text, re.DOTALL)
    return [json.loads(match.strip()) for match in matches if match.strip()]


def test_backtick_include_with_pdd_tags_is_format_safe(tmp_path):
    included_file = tmp_path / "inc.prompt"
    included_file.write_text(
        '<pdd-interface>{"type":"module","module":{"functions":[{"name":"tick"}]}}</pdd-interface>',
        encoding="utf-8",
    )

    processed = preprocess(
        f"```<{included_file}>```",
        recursive=False,
        double_curly_brackets=True,
    )
    formatted = processed.format()

    assert _pdd_interface_payloads(formatted)[0]["module"]["functions"][0]["name"] == "tick"


def test_nested_xml_includes_with_pdd_tags_are_format_safe(tmp_path):
    leaf = tmp_path / "leaf.prompt"
    leaf.write_text(
        '<pdd-interface>{"type":"module","module":{"functions":[{"name":"nested"}]}}</pdd-interface>',
        encoding="utf-8",
    )
    parent = tmp_path / "parent.prompt"
    parent.write_text(f"<include>{leaf}</include>", encoding="utf-8")

    processed = preprocess(
        f"<include>{parent}</include>",
        recursive=True,
        double_curly_brackets=True,
    )
    formatted = processed.format()

    assert parse_prompt_tags(formatted)["interface"]["module"]["functions"][0]["name"] == "nested"


def test_non_recursive_nested_xml_includes_with_pdd_tags_are_format_safe(tmp_path):
    leaf = tmp_path / "leaf.prompt"
    leaf.write_text('<pdd-interface>{"nested":"nonrecursive"}</pdd-interface>', encoding="utf-8")
    parent = tmp_path / "parent.prompt"
    parent.write_text(f"<include>{leaf}</include>", encoding="utf-8")

    processed = preprocess(
        f"<include>{parent}</include>",
        recursive=False,
        double_curly_brackets=True,
    )
    formatted = processed.format()

    assert parse_prompt_tags(formatted)["interface"]["nested"] == "nonrecursive"


def test_already_escaped_braces_in_pdd_content_keep_existing_preprocess_contract():
    prompt = '<pdd-interface>{"template":"{{already_escaped}}"}</pdd-interface>'

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    tags_before_format = parse_prompt_tags(processed)
    formatted = processed.format()
    tags_after_format = parse_prompt_tags(formatted)

    assert "{{{{already_escaped}}}}" not in processed
    assert tags_before_format["interface"]["template"] == "{already_escaped}"
    assert tags_after_format["interface"]["template"] == "{already_escaped}"


@pytest.mark.parametrize(
    "prompt",
    [
        "<pdd-interface></pdd-interface>",
        "<pdd-interface>   \n   </pdd-interface>",
    ],
)
def test_empty_or_whitespace_only_pdd_interface_tags_are_format_safe(prompt):
    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    assert processed.format() == prompt


@pytest.mark.parametrize(
    "included_text, expected",
    [
        ('<pdd-interface>{"position":"start"}</pdd-interface>\nbody', "start"),
        ('body\n<pdd-interface>{"position":"end"}</pdd-interface>', "end"),
    ],
)
def test_pdd_tags_at_included_file_boundaries_are_format_safe(
    tmp_path,
    included_text,
    expected,
):
    included = tmp_path / f"{expected}.prompt"
    included.write_text(included_text, encoding="utf-8")

    processed = preprocess(f"<include>{included}</include>", double_curly_brackets=True)
    formatted = processed.format()

    assert _pdd_interface_payloads(formatted)[0]["position"] == expected


def test_unicode_in_pdd_interface_is_format_safe():
    prompt = '<pdd-interface>{"name":"日本語","symbol":"{brace}"}</pdd-interface>'

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    formatted = processed.format()

    assert parse_prompt_tags(formatted)["interface"] == {"name": "日本語", "symbol": "{brace}"}


def test_real_file_include_with_pdd_tags_integration(tmp_path):
    included = tmp_path / "real.prompt"
    included.write_text(
        '<pdd-interface>{"real":"file","nested":{"ok":true}}</pdd-interface>',
        encoding="utf-8",
    )

    processed = preprocess(f"<include>{included}</include>", double_curly_brackets=True)
    formatted = processed.format()

    assert parse_prompt_tags(formatted)["interface"]["nested"]["ok"] is True


def test_full_pipeline_preprocess_then_parse_then_format(tmp_path):
    included = tmp_path / "pipe.prompt"
    included.write_text(
        '<pdd-interface>{"pipe":"line","shape":{"depth":2}}</pdd-interface>',
        encoding="utf-8",
    )

    processed = preprocess(
        f"<include>{included}</include>\nRender {{module_name}}",
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=["module_name"],
    )
    tags_before_format = parse_prompt_tags(processed)
    formatted = processed.format(module_name="orders")
    tags_after_format = parse_prompt_tags(formatted)

    assert tags_before_format["interface"]["shape"]["depth"] == 2
    assert "Render orders" in formatted
    assert tags_after_format["interface"]["pipe"] == "line"


@pytest.mark.parametrize(
    "raw_value",
    [
        "{ unclosed",
        "trailing }",
    ],
)
def test_malformed_brace_sequences_inside_pdd_json_do_not_break_format(raw_value):
    prompt = f'<pdd-interface>{{"broken":{json.dumps(raw_value)}}}</pdd-interface>'

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    formatted = processed.format()

    assert parse_prompt_tags(formatted)["interface"]["broken"] == raw_value


def test_pdd_tags_with_shell_and_web_tags_are_format_safe(monkeypatch):
    class FakeCache:
        def get(self, url):
            assert url == "https://example.test/pdd"
            return '<pdd-interface>{"source":"web","payload":{"cached":true}}</pdd-interface>'

        def set(self, url, content):
            raise AssertionError("cached web content should not be written")

    monkeypatch.setattr("pdd.preprocess.get_firecrawl_cache", lambda: FakeCache())
    prompt = (
        '<pdd-interface>{"source":"prompt","brace":"{value}"}</pdd-interface>\n'
        "<shell>printf shell-ok</shell>\n"
        "<web>https://example.test/pdd</web>"
    )

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    formatted = processed.format()
    payloads = _pdd_interface_payloads(formatted)

    assert "shell-ok" in formatted
    assert payloads == [
        {"source": "prompt", "brace": "{value}"},
        {"source": "web", "payload": {"cached": True}},
    ]
