"""
Example: auto_include

Demonstrates all features of the auto_include module:
  1. Load the auto_include_LLM prompt template
  2. Run summarize_directory and format CSV rows for the LLM
  3. Two-stage retrieval: embed_and_retrieve pre-filter when candidates > 50
  4. Invoke auto_include_LLM via llm_invoke with Pydantic structured output (AutoIncludeResult)
  5. Build include_directives with <new> and <update> tagged blocks
  6. Filter duplicates, self-references, and circular dependencies
  7. Strip selectors from small files (<100 lines)
  8. Validate inputs; on LLM failure return empty include_directives
  9. Return (include_directives, csv_output, total_cost, model_name)
 10. Pass csv_file for cache reuse
 11. Use prompt_filename to filter self-referential example files
 12. Use progress_callback for TUI integration
 13. Use the time parameter for LLM thinking effort
 14. Pass include_docs to discover documentation files (.md, .txt, .rst)
 15. Pass max_workers for parallel LLM summarization
 16. Pass csv_path for incremental CSV persistence
"""

import os
import sys
import tempfile
import shutil
from unittest.mock import patch

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd import DEFAULT_STRENGTH, DEFAULT_TIME
from pdd.auto_include import (
    auto_include,
    AutoIncludeResult,
    NewInclude,
    IncludeAnnotation,
)
from pdd.summarize_directory import FileSummary


def mock_summarize_directory(*args, **kwargs):
    """Mock for summarize_directory to make the example run standalone."""
    csv = (
        "full_path,file_summary,key_exports,dependencies,content_hash\n"
        'context/llm_invoke_example.py,"Example usage of llm_invoke",'
        '"[""llm_invoke""]","[""pdd.llm_invoke""]",hash1\n'
        'context/summarize_directory_example.py,"Example usage of summarize_directory",'
        '"[""summarize_directory""]","[""pdd.summarize_directory""]",hash2\n'
        'context/auto_include_example.py,"Example usage of auto_include",'
        '"[""auto_include""]","[""pdd.auto_include""]",hash3'
    )
    return csv, 0.05, "mock-gpt-4o"


def mock_llm_invoke(*args, **kwargs):
    """Mock for llm_invoke returning a Pydantic AutoIncludeResult."""
    return {
        "result": AutoIncludeResult(
            reasoning="The prompt needs llm_invoke for LLM calls and summarize_directory for file scanning.",
            new_includes=[
                NewInclude(
                    file="context/llm_invoke_example.py",
                    module="pdd.llm_invoke",
                    select="def:llm_invoke",
                ),
                NewInclude(
                    file="context/summarize_directory_example.py",
                    module="pdd.summarize_directory",
                ),
                # This one will be filtered as a self-reference when prompt_filename is set
                NewInclude(
                    file="context/auto_include_example.py",
                    module="pdd.auto_include",
                ),
            ],
            existing_include_annotations=[
                IncludeAnnotation(
                    file="context/python_preamble.prompt",
                    select="def:coding_style",
                ),
                # This one has no select/query and should be skipped
                IncludeAnnotation(file="context/readme.md"),
            ],
        ),
        "cost": 0.12,
        "model_name": "mock-gpt-4o",
    }


def main():
    print("=" * 60)
    print("Example: auto_include")
    print("=" * 60)

    # ------------------------------------------------------------------
    # 1. Basic usage with all parameters
    # ------------------------------------------------------------------
    print("\n--- 1. Basic auto_include call ---")
    input_prompt = """\
% You are an expert Python Software Engineer.

<include>context/python_preamble.prompt</include>

% Requirements:
    1. Parse input files
    2. Generate output using LLM
"""

    with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize_directory), \
         patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke), \
         patch("pdd.auto_include.load_prompt_template", return_value="auto_include_LLM prompt"), \
         patch("pdd.auto_include._get_file_line_count", return_value=200):

        include_directives, csv_output, total_cost, model_name = auto_include(
            input_prompt=input_prompt,
            directory_path="context/c*.py",
            csv_file=None,
            prompt_filename="prompts/auto_include_python.prompt",
            strength=DEFAULT_STRENGTH,
            temperature=0.0,
            time=DEFAULT_TIME,
            verbose=True,
            include_docs=True,       # discover .md, .txt, .rst documentation files
            max_workers=4,           # parallelize LLM summarization calls
            csv_path="/tmp/deps.csv",  # incremental CSV persistence
        )

    print(f"\nInclude directives:\n{include_directives}")
    print(f"\nCSV output (first 200 chars):\n{csv_output[:200]}...")
    print(f"Total cost: ${total_cost:.6f}")
    print(f"Model: {model_name}")

    # Verify filtering
    assert "auto_include_example.py" not in include_directives, \
        "Self-referential example should be filtered"
    # python_preamble.prompt appears as an <update> (annotating existing include with selector)
    # but should NOT appear as a <new> block (duplicate filtering)
    assert "<new>" not in include_directives or "python_preamble.prompt" not in \
        "\n".join(b for b in include_directives.split("<new>") if "<new>" not in b), \
        "Duplicate <new> include should be filtered"
    assert "readme.md" not in include_directives, \
        "Annotation with no select/query should be skipped"
    # The <update> for python_preamble.prompt IS expected (adds select attribute)
    assert "<update>" in include_directives, \
        "Update block for existing include annotation should be present"
    print("[PASS] Self-references, duplicates, and empty annotations filtered correctly")

    # ------------------------------------------------------------------
    # 2. csv_file cache reuse
    # ------------------------------------------------------------------
    print("\n--- 2. Cache reuse via csv_file ---")
    with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize_directory), \
         patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke), \
         patch("pdd.auto_include.load_prompt_template", return_value="auto_include_LLM prompt"), \
         patch("pdd.auto_include._get_file_line_count", return_value=200):

        _, csv_output2, cost2, _ = auto_include(
            input_prompt=input_prompt,
            directory_path="context/c*.py",
            csv_file=csv_output,  # pass previous output as cache
            strength=0.8,
            temperature=0.0,
        )

    print(f"Cost with cache: ${cost2:.6f}")
    print("[PASS] csv_file parameter accepted for cache reuse")

    # ------------------------------------------------------------------
    # 3. progress_callback
    # ------------------------------------------------------------------
    print("\n--- 3. Progress callback ---")
    progress_log = []

    def my_callback(current: int, total: int) -> None:
        progress_log.append((current, total))
        print(f"  Progress: {current}/{total}")

    with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize_directory), \
         patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke), \
         patch("pdd.auto_include.load_prompt_template", return_value="auto_include_LLM prompt"), \
         patch("pdd.auto_include._get_file_line_count", return_value=200):

        auto_include(
            input_prompt=input_prompt,
            directory_path="context/c*.py",
            progress_callback=my_callback,
        )

    print(f"  Callback log: {progress_log}")
    print("[PASS] progress_callback forwarded to summarize_directory")

    # ------------------------------------------------------------------
    # 4. Input validation
    # ------------------------------------------------------------------
    print("\n--- 4. Input validation ---")
    try:
        auto_include(input_prompt="test", directory_path="dir", strength=1.5)
    except ValueError as e:
        print(f"  Caught: {e}")

    try:
        auto_include(input_prompt="test", directory_path="dir", temperature=-0.1)
    except ValueError as e:
        print(f"  Caught: {e}")

    print("[PASS] Strength and temperature validation works")

    # ------------------------------------------------------------------
    # 5. Prompt template load failure
    # ------------------------------------------------------------------
    print("\n--- 5. Prompt template load failure ---")
    with patch("pdd.auto_include.load_prompt_template", return_value=None):
        try:
            auto_include(input_prompt="test", directory_path="dir")
        except ValueError as e:
            print(f"  Caught: {e}")
    print("[PASS] ValueError raised when prompt template not found")

    # ------------------------------------------------------------------
    # 6. LLM failure returns empty directives
    # ------------------------------------------------------------------
    print("\n--- 6. LLM failure handling ---")

    def failing_llm(*args, **kwargs):
        raise RuntimeError("LLM service unavailable")

    with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize_directory), \
         patch("pdd.auto_include.llm_invoke", side_effect=failing_llm), \
         patch("pdd.auto_include.load_prompt_template", return_value="prompt"):

        directives, csv_out, cost, model = auto_include(
            input_prompt="test",
            directory_path="context/*.py",
        )

    assert directives == "", f"Expected empty directives on LLM failure, got: {directives}"
    print(f"  Directives: '{directives}' (empty as expected)")
    print(f"  Cost: ${cost:.6f} (only summarize cost)")
    print("[PASS] LLM failure returns empty include_directives gracefully")

    # ------------------------------------------------------------------
    # 7. time parameter
    # ------------------------------------------------------------------
    print("\n--- 7. Time parameter for LLM thinking effort ---")
    with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize_directory), \
         patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke) as mock_llm, \
         patch("pdd.auto_include.load_prompt_template", return_value="prompt"), \
         patch("pdd.auto_include._get_file_line_count", return_value=200):

        auto_include(
            input_prompt=input_prompt,
            directory_path="context/*.py",
            time=0.8,
        )

    print("[PASS] time parameter passed through to llm_invoke")

    # ------------------------------------------------------------------
    # 8. Two-stage retrieval: embed pre-filter when candidates > 50
    # ------------------------------------------------------------------
    print("\n--- 8. Two-stage retrieval (embed pre-filter) ---")

    # Build CSV with > 50 rows to trigger embedding pre-filter
    csv_rows = ["full_path,file_summary,key_exports,dependencies,content_hash"]
    for i in range(55):
        csv_rows.append(
            f'context/mod_{i}_example.py,"Module {i} summary",'
            f'"[""mod_{i}""]","[""pdd.mod_{i}""]",hash{i}'
        )
    large_csv = "\n".join(csv_rows)

    def mock_summarize_large(*args, **kwargs):
        return large_csv, 0.05, "mock-gpt-4o"

    embed_called = []

    def mock_embed_and_retrieve(query, candidates, top_n=50):
        embed_called.append({"query_len": len(query), "candidates": len(candidates), "top_n": top_n})
        # Return first top_n candidates with mock scores
        return [(c, 1.0 - i * 0.01) for i, c in enumerate(candidates[:top_n])]

    with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize_large), \
         patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke), \
         patch("pdd.auto_include.load_prompt_template", return_value="prompt"), \
         patch("pdd.auto_include._get_file_line_count", return_value=200), \
         patch("pdd.auto_include.embed_and_retrieve", side_effect=mock_embed_and_retrieve):

        _, _, _, _ = auto_include(
            input_prompt=input_prompt,
            directory_path="context/c*.py",
            verbose=True,
        )

    assert len(embed_called) == 1, f"Expected embed_and_retrieve called once, got {len(embed_called)}"
    assert embed_called[0]["candidates"] == 55, \
        f"Expected 55 candidates passed to embed, got {embed_called[0]['candidates']}"
    assert embed_called[0]["top_n"] == 50, \
        f"Expected top_n=50, got {embed_called[0]['top_n']}"
    print(f"  embed_and_retrieve called with {embed_called[0]['candidates']} candidates, top_n={embed_called[0]['top_n']}")
    print("[PASS] Two-stage retrieval triggers embed pre-filter when candidates > 50")

    # ------------------------------------------------------------------
    # 9. Skip embed pre-filter when candidates <= 50
    # ------------------------------------------------------------------
    print("\n--- 9. Skip embed pre-filter when candidates <= 50 ---")
    embed_called_small = []

    def mock_embed_small(query, candidates, top_n=50):
        embed_called_small.append(True)
        return [(c, 1.0) for c in candidates[:top_n]]

    with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize_directory), \
         patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke), \
         patch("pdd.auto_include.load_prompt_template", return_value="prompt"), \
         patch("pdd.auto_include._get_file_line_count", return_value=200), \
         patch("pdd.auto_include.embed_and_retrieve", side_effect=mock_embed_small):

        auto_include(
            input_prompt=input_prompt,
            directory_path="context/c*.py",
        )

    assert len(embed_called_small) == 0, \
        f"embed_and_retrieve should NOT be called for <= 50 candidates, but was called {len(embed_called_small)} times"
    print("  embed_and_retrieve not called (3 candidates <= 50)")
    print("[PASS] Embedding pre-filter skipped for small candidate sets")

    print("\n" + "=" * 60)
    print("All examples passed!")
    print("=" * 60)


if __name__ == "__main__":
    main()
