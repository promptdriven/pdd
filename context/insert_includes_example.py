"""
Example: insert_includes

Demonstrates all features of the insert_includes module:
  1. Load insert_includes_LLM.prompt template, preprocess with double curly brackets
  2. Read CSV file (create with header if missing)
  3. Call auto_include to get include_directives, csv_output, total_cost, model_name
  4. Apply <update> blocks deterministically (no LLM call)
  5. If <new> blocks remain, invoke LLM to place them in the prompt
  6. If no <new> blocks exist, skip LLM call
  7. Return (output_prompt, csv_output, total_cost, model_name)
  8. Pass prompt_filename for self-reference filtering
  9. Use progress_callback for TUI integration
 10. Use the time parameter for LLM thinking effort
"""

import os
import sys
import tempfile

from unittest.mock import patch

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.insert_includes import insert_includes, InsertIncludesOutput


def mock_auto_include_with_new_and_update(*args, **kwargs):
    """Mock auto_include returning both <new> and <update> blocks."""
    directives = (
        "<update><include select='def:helper'>context/helper_example.py</include></update>\n"
        "<new><include select='class:Parser'>context/parser_example.py</include></new>"
    )
    csv = (
        "full_path,file_summary,key_exports,dependencies,content_hash\n"
        "context/helper_example.py,\"Helper utilities\","
        "\"[\"\"helper\"\"]\",\"[]\",hash1\n"
        "context/parser_example.py,\"Parser module\","
        "\"[\"\"Parser\"\"]\",\"[]\",hash2"
    )
    return directives, csv, 0.05, "mock-gpt-4o"


def mock_auto_include_update_only(*args, **kwargs):
    """Mock auto_include returning only <update> blocks (no <new>)."""
    directives = (
        "<update><include select='def:helper'>context/helper_example.py</include></update>"
    )
    csv = (
        "full_path,file_summary,key_exports,dependencies,content_hash\n"
        "context/helper_example.py,\"Helper utilities\","
        "\"[\"\"helper\"\"]\",\"[]\",hash1"
    )
    return directives, csv, 0.03, "mock-gpt-4o"


def mock_llm_invoke(*args, **kwargs):
    """Mock llm_invoke returning an InsertIncludesOutput."""
    return {
        "result": InsertIncludesOutput(
            output_prompt=(
                "% You are an expert Python Programmer.\n\n"
                "<include select='def:helper'>context/helper_example.py</include>\n"
                "<include select='class:Parser'>context/parser_example.py</include>\n\n"
                "% Requirements:\n    1. Parse input files\n    2. Generate output"
            )
        ),
        "cost": 0.02,
        "model_name": "mock-gpt-4o",
    }


def main():
    print("=" * 60)
    print("Example: insert_includes")
    print("=" * 60)

    # ------------------------------------------------------------------
    # 1. Basic usage: prompt with both <new> and <update> blocks
    # ------------------------------------------------------------------
    print("\n--- 1. Basic call with <new> and <update> blocks ---")

    input_prompt = """\
% You are an expert Python Programmer.

<include>context/helper_example.py</include>

% Requirements:
    1. Parse input files
    2. Generate output"""

    with tempfile.TemporaryDirectory() as tmpdir:
        csv_path = os.path.join(tmpdir, "deps.csv")

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_with_new_and_update), \
             patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke), \
             patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed template"):

            output_prompt, csv_output, total_cost, model_name = insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path,
                strength=0.93,
                temperature=0.0,
                verbose=True,
            )

        print(f"Output prompt:\n{output_prompt}")
        print(f"CSV output (first 200 chars):\n{csv_output[:200]}...")
        print(f"Total cost: ${total_cost:.6f}")
        print(f"Model: {model_name}")
        assert total_cost == 0.07  # auto_include (0.05) + llm_invoke (0.02)
        print("[PASS] Basic usage with <new> and <update> blocks")

    # ------------------------------------------------------------------
    # 2. Update-only: LLM call is skipped
    # ------------------------------------------------------------------
    print("\n--- 2. Update-only (LLM skipped) ---")

    with tempfile.TemporaryDirectory() as tmpdir:
        csv_path = os.path.join(tmpdir, "deps.csv")

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_update_only), \
             patch("pdd.insert_includes.llm_invoke") as mock_llm, \
             patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed template"):

            output_prompt, csv_output, total_cost, model_name = insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path,
                verbose=False,
            )

        mock_llm.assert_not_called()
        assert total_cost == 0.03  # only auto_include cost
        assert model_name == "mock-gpt-4o"
        # The <update> block replaced the original <include> tag deterministically
        assert "select='def:helper'" in output_prompt
        print(f"Output prompt:\n{output_prompt}")
        print(f"Total cost: ${total_cost:.6f} (no LLM cost)")
        print("[PASS] Update-only skips LLM call")

    # ------------------------------------------------------------------
    # 3. CSV file creation when missing
    # ------------------------------------------------------------------
    print("\n--- 3. CSV auto-creation ---")

    with tempfile.TemporaryDirectory() as tmpdir:
        csv_path = os.path.join(tmpdir, "nonexistent.csv")
        assert not os.path.exists(csv_path)

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_update_only), \
             patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed template"):

            insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path,
            )

        assert os.path.exists(csv_path), "CSV file should be created"
        with open(csv_path) as f:
            header = f.readline().strip()
        assert header == "full_path,file_summary,key_exports,dependencies,content_hash"
        print(f"Created CSV with header: {header}")
        print("[PASS] CSV file auto-created with correct header")

    # ------------------------------------------------------------------
    # 4. prompt_filename for self-reference filtering
    # ------------------------------------------------------------------
    print("\n--- 4. prompt_filename passthrough ---")

    with tempfile.TemporaryDirectory() as tmpdir:
        csv_path = os.path.join(tmpdir, "deps.csv")

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_update_only) as mock_ai, \
             patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed template"):

            insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path,
                prompt_filename="prompts/insert_includes_python.prompt",
            )

        # Verify prompt_filename was passed through to auto_include
        call_kwargs = mock_ai.call_args[1]
        assert call_kwargs["prompt_filename"] == "prompts/insert_includes_python.prompt"
        print("[PASS] prompt_filename passed through to auto_include")

    # ------------------------------------------------------------------
    # 5. progress_callback passthrough
    # ------------------------------------------------------------------
    print("\n--- 5. progress_callback ---")
    progress_log = []

    def my_callback(current: int, total: int) -> None:
        progress_log.append((current, total))

    with tempfile.TemporaryDirectory() as tmpdir:
        csv_path = os.path.join(tmpdir, "deps.csv")

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_update_only) as mock_ai, \
             patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed template"):

            insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path,
                progress_callback=my_callback,
            )

        call_kwargs = mock_ai.call_args[1]
        assert call_kwargs["progress_callback"] is my_callback
        print("[PASS] progress_callback passed through to auto_include")

    # ------------------------------------------------------------------
    # 6. time parameter passthrough
    # ------------------------------------------------------------------
    print("\n--- 6. time parameter ---")

    with tempfile.TemporaryDirectory() as tmpdir:
        csv_path = os.path.join(tmpdir, "deps.csv")

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_with_new_and_update) as mock_ai, \
             patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke) as mock_llm, \
             patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed template"):

            insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path,
                time=0.8,
            )

        # Verify time was passed to both auto_include and llm_invoke
        assert mock_ai.call_args[1]["time"] == 0.8
        assert mock_llm.call_args[1]["time"] == 0.8
        print("[PASS] time parameter passed through to auto_include and llm_invoke")

    print("\n" + "=" * 60)
    print("All examples passed!")
    print("=" * 60)


if __name__ == "__main__":
    main()
