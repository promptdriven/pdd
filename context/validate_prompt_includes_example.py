"""
Example: validate_prompt_includes

Demonstrates validating prompt include tags, preserving literal examples in
inline code, and sanitizing prompt outputs before writing.
"""

from pathlib import Path
from tempfile import TemporaryDirectory

from pdd.validate_prompt_includes import sanitize_prompt_output, validate_prompt_includes


def main() -> None:
    with TemporaryDirectory() as tmp:
        base_dir = Path(tmp)
        existing = base_dir / "existing.py"
        existing.write_text("def hello():\n    return 'world'\n", encoding="utf-8")

        prompt = """
% Use this real dependency.
<dependency><include>existing.py</include></dependency>

% This dependency is missing.
<missing_dependency><include>missing.py</include></missing_dependency>

% Literal documentation should be left alone: `<include>missing.py</include>`.
"""

        commented, invalid = validate_prompt_includes(
            prompt,
            base_dir=base_dir,
            remove_invalid=False,
        )
        assert invalid == ["missing.py"]
        assert "<include>existing.py</include>" in commented
        assert "<!-- Missing: missing.py -->" in commented
        assert "`<include>missing.py</include>`" in commented

        removed, invalid_removed = validate_prompt_includes(
            prompt,
            base_dir=base_dir,
            remove_invalid=True,
        )
        assert invalid_removed == ["missing.py"]
        assert "<missing_dependency>" not in removed

        sanitized, sanitized_invalid = sanitize_prompt_output(
            prompt,
            base_dir / "generated.prompt",
        )
        assert sanitized_invalid == ["missing.py"]
        assert "<!-- Missing: missing.py -->" in sanitized

        unchanged, unchanged_invalid = sanitize_prompt_output(
            prompt,
            base_dir / "generated.py",
        )
        assert unchanged == prompt
        assert unchanged_invalid == []

    print("validate_prompt_includes example passed")


if __name__ == "__main__":
    main()
