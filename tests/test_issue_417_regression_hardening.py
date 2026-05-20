import pytest
from pdd.preprocess import preprocess
from pdd.architecture_sync import parse_prompt_tags

def test_backtick_include_with_pdd_tags_is_format_safe(tmp_path):
    """Test ```<file.txt>``` style includes with PDD tag content."""
    included_file = tmp_path / "inc.txt"
    included_file.write_text('<pdd-interface>\n{"key": "value"}\n</pdd-interface>')
    
    prompt = f"```<{included_file}>```"
    result = preprocess(prompt, double_curly_brackets=True)
    
    formatted = result.format()
    assert '<pdd-interface>\n{"key": "value"}\n</pdd-interface>' in formatted

def test_nested_includes_with_pdd_tags_are_format_safe(tmp_path):
    """Test that nested includes (file A includes file B which has PDD tags) work."""
    file_b = tmp_path / "b.txt"
    file_b.write_text('<pdd-interface>{"nested": "yes"}</pdd-interface>')
    
    file_a = tmp_path / "a.txt"
    file_a.write_text(f'<include>{file_b}</include>')
    
    prompt = f'<include>{file_a}</include>'
    
    result = preprocess(prompt, recursive=True, double_curly_brackets=True)
    formatted = result.format()
    
    assert '<pdd-interface>{"nested": "yes"}</pdd-interface>' in formatted

def test_nested_includes_non_recursive_with_pdd_tags(tmp_path):
    """Test that nested includes work even with recursive=False."""
    file_b = tmp_path / "b.txt"
    file_b.write_text('<pdd-interface>{"nested": "no_rec"}</pdd-interface>')
    
    file_a = tmp_path / "a.txt"
    file_a.write_text(f'<include>{file_b}</include>')
    
    prompt = f'<include>{file_a}</include>'
    
    # recursive=False should still resolve includes via _process_nested_includes
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    formatted = result.format()
    
    assert '<pdd-interface>{"nested": "no_rec"}</pdd-interface>' in formatted

def test_pdd_interface_with_mixed_braces_and_vars():
    """Test PDD interface containing both single braces, double braces, and ${VAR}."""
    prompt = '<pdd-interface>{"a": {val}, "b": "{{lit}}", "c": "${VAR}"}</pdd-interface>'
    result = preprocess(prompt, double_curly_brackets=True)
    
    # {val} -> {{val}} -> {val} (NOT replaced because it's protected)
    # {{lit}} -> {{lit}} (protected) -> {lit}
    # ${VAR} -> ${{VAR}} -> ${VAR}
    formatted = result.format(val=123)
    assert '<pdd-interface>{"a": {val}, "b": "{lit}", "c": "${VAR}"}</pdd-interface>' in formatted

def test_pdd_interface_with_excluded_keys():
    """Test that exclude_keys allows placeholders to work inside PDD tags."""
    prompt = '<pdd-interface>{"a": {val}}</pdd-interface>'
    result = preprocess(prompt, double_curly_brackets=True, exclude_keys=["val"])
    
    # {val} is excluded, so it stays {val} during double_curly
    # .format(val=123) -> 123
    formatted = result.format(val=123)
    assert '<pdd-interface>{"a": 123}</pdd-interface>' in formatted

def test_already_escaped_braces_in_pdd_content():
    """Test PDD content that already has {{escaped}} braces doesn't get quadrupled."""
    prompt = '<pdd-interface>{"key": "{{escaped}}"}</pdd-interface>'
    result = preprocess(prompt, double_curly_brackets=True)
    
    formatted = result.format()
    # Invariant: literal double braces in PDD JSON become single braces after .format()
    assert '<pdd-interface>{"key": "{escaped}"}</pdd-interface>' in formatted

def test_empty_pdd_interface_tag_is_format_safe():
    """Test <pdd-interface></pdd-interface> doesn't break format()."""
    prompt = "<pdd-interface></pdd-interface>"
    result = preprocess(prompt, double_curly_brackets=True)
    assert result.format() == "<pdd-interface></pdd-interface>"

def test_whitespace_only_pdd_interface_is_format_safe():
    """Test <pdd-interface>   </pdd-interface> is handled correctly."""
    prompt = "<pdd-interface>   \n   </pdd-interface>"
    result = preprocess(prompt, double_curly_brackets=True)
    assert result.format() == "<pdd-interface>   \n   </pdd-interface>"

def test_pdd_tag_at_start_of_included_file_is_format_safe(tmp_path):
    """Test included files that start directly with <pdd-interface>."""
    included = tmp_path / "start.txt"
    included.write_text('<pdd-interface>{"a": 1}</pdd-interface>\ntext')
    prompt = f"<include>{included}</include>"
    result = preprocess(prompt, double_curly_brackets=True)
    assert result.format() == '<pdd-interface>{"a": 1}</pdd-interface>\ntext'

def test_pdd_tag_at_end_of_included_file_is_format_safe(tmp_path):
    """Test included files that end with </pdd-interface> (no trailing newline)."""
    included = tmp_path / "end.txt"
    included.write_text('text\n<pdd-interface>{"b": 2}</pdd-interface>')
    prompt = f"<include>{included}</include>"
    result = preprocess(prompt, double_curly_brackets=True)
    assert result.format() == 'text\n<pdd-interface>{"b": 2}</pdd-interface>'

def test_pdd_tag_at_end_of_main_prompt_is_format_safe():
    prompt = 'text\n<pdd-interface>{"b": 2}</pdd-interface>'
    result = preprocess(prompt, double_curly_brackets=True)
    assert result.format() == 'text\n<pdd-interface>{"b": 2}</pdd-interface>'

def test_unicode_in_pdd_interface_is_format_safe():
    """Test PDD interface with Unicode characters like {"name": "日本語"}."""
    prompt = '<pdd-interface>{"name": "日本語"}</pdd-interface>'
    result = preprocess(prompt, double_curly_brackets=True)
    assert result.format() == '<pdd-interface>{"name": "日本語"}</pdd-interface>'

def test_real_file_include_with_pdd_tags_integration(tmp_path):
    """Integration test with actual temp files instead of mocks."""
    included = tmp_path / "real.txt"
    included.write_text('some content <pdd-interface>{"real": "file"}</pdd-interface>')
    prompt = f"Load <include>{included}</include>"
    result = preprocess(prompt, double_curly_brackets=True)
    assert '<pdd-interface>{"real": "file"}</pdd-interface>' in result.format()

def test_full_pipeline_preprocess_then_parse_then_format(tmp_path):
    """Test the complete flow: preprocess includes PDD content, 
    parse_prompt_tags extracts it, format() replaces placeholders."""
    included = tmp_path / "pipe.txt"
    included.write_text('<pdd-interface>{"pipe": "line"}</pdd-interface>')
    prompt = f"<include>{included}</include>"
    result = preprocess(prompt, double_curly_brackets=True)
    formatted = result.format()
    tags = parse_prompt_tags(formatted)
    assert tags.get("interface", {}).get("pipe") == "line"

def test_format_valueerror_from_incomplete_escape():
    """Test content like '{ unclosed' or 'trailing }' doesn't crash."""
    prompt = '<pdd-interface>{"broken": "{ unclosed"}</pdd-interface>'
    result = preprocess(prompt, double_curly_brackets=True)
    assert result.format() == '<pdd-interface>{"broken": "{ unclosed"}</pdd-interface>'
    
    prompt2 = '<pdd-interface>{"broken": "trailing }"}</pdd-interface>'
    result2 = preprocess(prompt2, double_curly_brackets=True)
    assert result2.format() == '<pdd-interface>{"broken": "trailing }"}</pdd-interface>'

def test_pdd_tags_with_shell_and_web_tags():
    """Test <pdd-interface> mixed with <shell> and <web> tags."""
    # Note: <web> requires FIRECRAWL_API_KEY if we try to process it, so we'll just test shell to avoid network/key deps
    prompt = '<shell>echo 1</shell><pdd-interface>{"a": 1}</pdd-interface>'
    result = preprocess(prompt, double_curly_brackets=True)
    formatted = result.format()
    assert "1\n<pdd-interface>{\"a\": 1}</pdd-interface>" in formatted
