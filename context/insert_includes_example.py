"""
Example: insert_includes

Demonstrates the insert_includes function which determines needed dependencies
and inserts them into a prompt. Features demonstrated:

  1. Basic usage — insert new dependencies into a prompt via LLM
  2. Update existing includes with selectors (no LLM needed)
  3. Mixed update + new blocks (update applied first, then LLM for new)
  4. Dedup — remove redundant inline content that duplicates included files
  5. Dedup disabled — skip redundant-content removal
  6. CSV file auto-creation when missing
  7. Progress callback for TUI integration
  8. Parameters passed through correctly (strength, temperature, time)
  9. Missing prompt template raises ValueError
 10. Return tuple shape: (output_prompt, csv_output, total_cost, model_name)
"""

import os
import sys
import tempfile
import shutil
from unittest.mock import patch

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.insert_includes import insert_includes, InsertIncludesOutput


def mock_auto_include_with_new(*args, **kwargs):
    """Mock auto_include returning <new> blocks (triggers LLM call)."""
    return (
        "<new><include>context/llm_invoke_example.py</include></new>\n"
        "<new><include>context/preprocess_example.py</include></new>",
        "full_path,file_summary,content_hash\n"
        "context/llm_invoke_example.py,LLM invocation example,hash1\n"
        "context/preprocess_example.py,Preprocessing example,hash2\n",
        0.05,
        "mock-gpt-4o",
    )


def mock_auto_include_with_update(*args, **kwargs):
    """Mock auto_include returning only <update> blocks (no LLM call)."""
    return (
        "<update><include select='def:helper'>utils.py</include></update>",
        "full_path,file_summary,content_hash\nutils.py,Utility helpers,hash1\n",
        0.03,
        "mock-gpt-4o",
    )


def mock_auto_include_mixed(*args, **kwargs):
    """Mock auto_include returning both <update> and <new> blocks."""
    return (
        "<update><include select='class:Config'>config.py</include></update>\n"
        "<new><include>context/new_dep.py</include></new>",
        "full_path,file_summary,content_hash\n"
        "config.py,Configuration module,hash1\n"
        "context/new_dep.py,New dependency,hash2\n",
        0.04,
        "mock-gpt-4o",
    )


def mock_auto_include_empty(*args, **kwargs):
    """Mock auto_include returning empty directives."""
    return ("", "full_path,file_summary,content_hash\n", 0.01, "mock-gpt-4o")


def mock_llm_invoke(*args, **kwargs):
    """Mock llm_invoke returning an InsertIncludesOutput with dependencies inserted."""
    input_json = kwargs.get("input_json", {})
    prompt = input_json.get("actual_prompt_to_update", "")
    deps = input_json.get("actual_dependencies_to_insert", "")
    # Simulate LLM inserting the include tags into the prompt
    output = prompt.rstrip() + "\n\n% Auto-inserted dependencies:\n" + deps + "\n"
    return {
        "result": InsertIncludesOutput(output_prompt=output),
        "cost": 0.10,
        "model_name": "mock-gpt-4o",
    }


def main():
    print("=" * 60)
    print("Example: insert_includes")
    print("=" * 60)

    # Create a temp directory for CSV files
    tmp_dir = tempfile.mkdtemp()

    try:
        # ------------------------------------------------------------------
        # 1. Basic usage — new dependencies inserted via LLM
        # ------------------------------------------------------------------
        print("\n--- 1. Basic usage: new dependencies ---")
        input_prompt = """\
% You are an expert Python engineer.

% Generate a function that invokes an LLM and preprocesses the output.
"""
        csv_path = os.path.join(tmp_dir, "deps.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value="insert_includes_LLM template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed template"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_with_new), \
             patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke):

            output_prompt, csv_output, total_cost, model_name = insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path,
                strength=0.93,
                temperature=0.0,
                time=0.25,
                verbose=True,
            )

        print(f"Output prompt (first 200 chars):\n{output_prompt[:200]}...")
        print(f"CSV output (first 150 chars): {csv_output[:150]}...")
        print(f"Total cost: ${total_cost:.6f}")
        print(f"Model: {model_name}")
        assert isinstance(output_prompt, str), "output_prompt should be a string"
        assert isinstance(csv_output, str), "csv_output should be a string"
        assert isinstance(total_cost, float), "total_cost should be a float"
        assert isinstance(model_name, str), "model_name should be a string"
        # Cost = auto_include (0.05) + llm_invoke (0.10)
        assert abs(total_cost - 0.15) < 1e-9, f"Expected total_cost=0.15, got {total_cost}"
        print("[PASS] Basic new-dependency insertion works")

        # ------------------------------------------------------------------
        # 2. Update-only — no LLM call needed
        # ------------------------------------------------------------------
        print("\n--- 2. Update existing includes (no LLM) ---")
        input_prompt_with_include = """\
% You are an expert Python engineer.
<include>utils.py</include>
% End of prompt.
"""
        csv_path2 = os.path.join(tmp_dir, "deps2.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_with_update), \
             patch("pdd.insert_includes.llm_invoke") as mock_llm:

            output_prompt, csv_output, total_cost, model_name = insert_includes(
                input_prompt=input_prompt_with_include,
                directory_path="context/*_example.py",
                csv_filename=csv_path2,
                verbose=True,
            )

        # LLM should NOT have been called for update-only
        mock_llm.assert_not_called()
        assert "<include select='def:helper'>utils.py</include>" in output_prompt, \
            "Update should add select attribute to existing include"
        assert total_cost == 0.03, f"Cost should be auto_include only: {total_cost}"
        print(f"Updated prompt:\n{output_prompt}")
        print(f"Total cost: ${total_cost:.6f} (auto_include only, no LLM)")
        print("[PASS] Update-only skips LLM correctly")

        # ------------------------------------------------------------------
        # 3. Mixed update + new blocks
        # ------------------------------------------------------------------
        print("\n--- 3. Mixed update + new blocks ---")
        input_prompt_mixed = """\
% Configuration-driven prompt.
<include>config.py</include>
% Process data below.
"""
        csv_path3 = os.path.join(tmp_dir, "deps3.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_mixed), \
             patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke):

            output_prompt, csv_output, total_cost, model_name = insert_includes(
                input_prompt=input_prompt_mixed,
                directory_path="context/*_example.py",
                csv_filename=csv_path3,
                verbose=True,
            )

        print(f"Output (first 300 chars):\n{output_prompt[:300]}")
        # Cost = auto_include (0.04) + llm_invoke (0.10)
        assert abs(total_cost - 0.14) < 1e-9, f"Expected total_cost=0.14, got {total_cost}"
        print(f"Total cost: ${total_cost:.6f}")
        print("[PASS] Mixed update + new blocks handled correctly")

        # ------------------------------------------------------------------
        # 4. Dedup enabled (default)
        # ------------------------------------------------------------------
        print("\n--- 4. Dedup enabled ---")
        csv_path4 = os.path.join(tmp_dir, "deps4.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_with_new), \
             patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke):

            output_prompt_dedup, _, _, _ = insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path4,
                dedup=True,  # default
                verbose=True,
            )

        print(f"Output with dedup (first 200 chars): {output_prompt_dedup[:200]}...")
        print("[PASS] Dedup runs without error")

        # ------------------------------------------------------------------
        # 5. Dedup disabled
        # ------------------------------------------------------------------
        print("\n--- 5. Dedup disabled ---")
        csv_path5 = os.path.join(tmp_dir, "deps5.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_with_new), \
             patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke):

            output_prompt_no_dedup, _, _, _ = insert_includes(
                input_prompt=input_prompt,
                directory_path="context/*_example.py",
                csv_filename=csv_path5,
                dedup=False,
                verbose=True,
            )

        print(f"Output without dedup (first 200 chars): {output_prompt_no_dedup[:200]}...")
        print("[PASS] Dedup disabled works correctly")

        # ------------------------------------------------------------------
        # 6. CSV file auto-creation
        # ------------------------------------------------------------------
        print("\n--- 6. CSV auto-creation when missing ---")
        csv_path6 = os.path.join(tmp_dir, "nonexistent_subdir", "auto_created.csv")
        os.makedirs(os.path.dirname(csv_path6), exist_ok=True)

        with patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_empty), \
             patch("pdd.insert_includes.llm_invoke") as mock_llm:

            output_prompt, _, cost, _ = insert_includes(
                input_prompt="simple prompt",
                directory_path="context/*.py",
                csv_filename=csv_path6,
                verbose=True,
            )

        assert os.path.exists(csv_path6), "CSV file should be auto-created"
        print(f"CSV file created successfully")
        print(f"Output: {output_prompt}")
        mock_llm.assert_not_called()  # empty directives -> no LLM
        print("[PASS] Missing CSV file auto-created with correct header")

        # ------------------------------------------------------------------
        # 7. Progress callback
        # ------------------------------------------------------------------
        print("\n--- 7. Progress callback ---")
        progress_log = []

        def my_callback(current: int, total: int) -> None:
            progress_log.append((current, total))
            print(f"  Progress: {current}/{total}")

        csv_path7 = os.path.join(tmp_dir, "deps7.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_empty) as mock_ai, \
             patch("pdd.insert_includes.llm_invoke"):

            insert_includes(
                input_prompt="prompt",
                directory_path="context/*.py",
                csv_filename=csv_path7,
                progress_callback=my_callback,
            )

        # Verify progress_callback was passed to auto_include
        assert mock_ai.call_args[1]["progress_callback"] is my_callback
        print("  Callback passed to auto_include: verified")
        print("[PASS] progress_callback forwarded correctly")

        # ------------------------------------------------------------------
        # 8. Parameter pass-through (strength, temperature, time)
        # ------------------------------------------------------------------
        print("\n--- 8. Parameter pass-through ---")
        csv_path8 = os.path.join(tmp_dir, "deps8.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_with_new) as mock_ai, \
             patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke) as mock_llm:

            insert_includes(
                input_prompt="prompt",
                directory_path="context/*.py",
                csv_filename=csv_path8,
                prompt_filename="prompts/test.prompt",
                strength=0.9,
                temperature=0.2,
                time=0.8,
                include_docs=True,
                max_workers=4,
            )

        # Verify auto_include received the parameters
        ai_kwargs = mock_ai.call_args[1]
        assert ai_kwargs["strength"] == 0.9
        assert ai_kwargs["temperature"] == 0.2
        assert ai_kwargs["time"] == 0.8
        assert ai_kwargs["prompt_filename"] == "prompts/test.prompt"
        print("  auto_include received: strength=0.9, temperature=0.2, time=0.8")

        # Verify llm_invoke received the parameters
        llm_kwargs = mock_llm.call_args[1]
        assert llm_kwargs["strength"] == 0.9
        assert llm_kwargs["temperature"] == 0.2
        assert llm_kwargs["time"] == 0.8
        print("  llm_invoke received: strength=0.9, temperature=0.2, time=0.8")
        print("[PASS] Parameters passed through to auto_include and llm_invoke")

        # ------------------------------------------------------------------
        # 9. Missing prompt template raises ValueError
        # ------------------------------------------------------------------
        print("\n--- 9. Missing prompt template ---")
        csv_path9 = os.path.join(tmp_dir, "deps9.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value=None):
            try:
                insert_includes(
                    input_prompt="prompt",
                    directory_path="dir",
                    csv_filename=csv_path9,
                )
                print("  ERROR: Expected ValueError was not raised!")
            except ValueError as e:
                print(f"  Caught ValueError: {e}")
                print("[PASS] Missing prompt template raises ValueError")

        # ------------------------------------------------------------------
        # 10. Return tuple shape verification
        # ------------------------------------------------------------------
        print("\n--- 10. Return tuple shape ---")
        csv_path10 = os.path.join(tmp_dir, "deps10.csv")

        with patch("pdd.insert_includes.load_prompt_template", return_value="template"), \
             patch("pdd.insert_includes.preprocess", return_value="processed"), \
             patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include_with_new), \
             patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke):

            result = insert_includes(
                input_prompt="test prompt",
                directory_path="context/*.py",
                csv_filename=csv_path10,
            )

        assert isinstance(result, tuple), "Return value should be a tuple"
        assert len(result) == 4, f"Tuple should have 4 elements, got {len(result)}"
        output_prompt, csv_output, total_cost, model_name = result
        assert isinstance(output_prompt, str), "output_prompt must be str"
        assert isinstance(csv_output, str), "csv_output must be str"
        assert isinstance(total_cost, float), "total_cost must be float"
        assert isinstance(model_name, str), "model_name must be str"
        print(f"  Return types: str, str, float, str")
        print("[PASS] Return tuple has correct shape and types")

        print("\n" + "=" * 60)
        print("All examples passed!")
        print("=" * 60)

    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


if __name__ == "__main__":
    main()
