import json
import statistics
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner


FIXTURE_ROOT = Path(__file__).resolve().parent / "fixtures" / "generate_estimate_accuracy"


def _ape(estimate, actual):
    return abs(float(estimate) - float(actual)) / max(float(actual), 1.0)


def _percentile(values, pct):
    ordered = sorted(values)
    rank = (len(ordered) - 1) * pct
    lower = int(rank)
    upper = min(lower + 1, len(ordered) - 1)
    weight = rank - lower
    return ordered[lower] * (1 - weight) + ordered[upper] * weight


def _write_pricing_csv(path: Path, *, include_known: bool, include_unknown: bool) -> None:
    rows = [
        "provider,model,input,output,coding_arena_elo,model_rank_score,model_rank_source,base_url,api_key,max_reasoning_tokens,structured_output,reasoning_type,location,interactive_only"
    ]
    if include_known:
        rows.append(
            "Fixture,fixture/generate-known,1.0,4.0,1500,1,fixture,,,0,True,none,,False"
        )
    if include_unknown:
        rows.append(
            "Github Copilot,fixture/generate-unknown,0.0,0.0,1500,1,fixture,,,0,True,none,,True"
        )
    path.write_text("\n".join(rows) + "\n", encoding="utf-8")


def _run_generate_estimate(case, tmp_path, monkeypatch):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    import pdd.llm_invoke as llm_mod
    from pdd.core.cli import cli

    project_dir = tmp_path / f"project-{case['name']}"
    project_dir.mkdir()
    pdd_dir = project_dir / ".pdd"
    pdd_dir.mkdir()
    pricing_csv = pdd_dir / "llm_model.csv"
    known = case["model"] == "fixture/generate-known"
    _write_pricing_csv(pricing_csv, include_known=known, include_unknown=not known)

    monkeypatch.chdir(project_dir)
    monkeypatch.setenv("PDD_MODEL_DEFAULT", case["model"])
    monkeypatch.setenv("PDD_SKIP_LOCAL_MODELS", "1")
    monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", pricing_csv)
    monkeypatch.setattr(
        llm_mod,
        "_MODEL_RATE_MAP",
        {case["model"]: (1.0, 4.0) if known else (0.0, 0.0)},
    )
    monkeypatch.setattr(
        llm_mod,
        "_MODEL_PROVIDER_MAP",
        {case["model"]: "Fixture" if known else "Github Copilot"},
    )

    prompt_path = FIXTURE_ROOT / case["prompt"]
    output_path = project_dir / f"{case['name']}.py"
    cost_csv = project_dir / "cost.csv"

    with patch("pdd.llm_invoke.litellm.completion") as mock_completion, \
         patch("pdd.llm_invoke.litellm.batch_completion") as mock_batch_completion, \
         patch("pdd.llm_invoke._llm_invoke_cloud") as mock_cloud:
        result = CliRunner().invoke(
            cli,
            [
                "--estimate-json",
                "--output-cost",
                str(cost_csv),
                "--no-core-dump",
                "generate",
                "--output",
                str(output_path),
                str(prompt_path),
            ],
        )

    assert result.exit_code == 0, result.output
    mock_completion.assert_not_called()
    mock_batch_completion.assert_not_called()
    mock_cloud.assert_not_called()
    assert not output_path.exists()
    assert not cost_csv.exists()
    assert not (pdd_dir / "meta").exists()
    payload = json.loads(result.output)
    return payload


def test_generate_estimate_accuracy_against_deterministic_fixtures(tmp_path, monkeypatch):
    cases = json.loads((FIXTURE_ROOT / "manifest.json").read_text(encoding="utf-8"))

    rows = []
    for case in cases:
        payload = _run_generate_estimate(case, tmp_path, monkeypatch)
        record = payload["records"][0]

        assert payload["estimate"] is True
        assert record["command"] == "generate"
        assert record["provider_call_made"] is False
        assert case["expected_input_min"] <= payload["input_tokens"] <= case["expected_input_max"]
        assert case["expected_output_min"] <= payload["predicted_output_tokens"] <= case["expected_output_max"]
        assert payload["output_tokens_low"] <= payload["predicted_output_tokens"] <= payload["output_tokens_high"]

        if case["actual_cost"] is None:
            assert payload["estimated_cost"] is None
            assert payload["unknown_cost"] is True
            cost_ape = None
        else:
            assert payload["estimated_cost"] is not None
            assert payload["unknown_cost"] is False
            expected_cost = round(
                (payload["input_tokens"] * 1.0 + payload["predicted_output_tokens"] * 4.0)
                / 1_000_000,
                6,
            )
            assert payload["estimated_cost"] == expected_cost
            cost_ape = _ape(payload["estimated_cost"], case["actual_cost"])

        rows.append({
            "name": case["name"],
            "input_ape": _ape(payload["input_tokens"], case["actual_input_tokens"]),
            "output_ape": _ape(payload["predicted_output_tokens"], case["actual_output_tokens"]),
            "cost_ape": cost_ape,
            "old_output_ape": _ape(
                round(payload["input_tokens"] * 0.52),
                case["actual_output_tokens"],
            ),
        })

    input_apes = [row["input_ape"] for row in rows]
    output_apes = [row["output_ape"] for row in rows]
    cost_apes = [row["cost_ape"] for row in rows if row["cost_ape"] is not None]
    old_output_apes = [row["old_output_ape"] for row in rows]

    assert statistics.median(input_apes) <= 0.15
    assert statistics.median(output_apes) <= 0.15
    assert _percentile(output_apes, 0.80) <= 0.25
    assert statistics.median(cost_apes) <= 0.15
    assert _percentile(cost_apes, 0.80) <= 0.25
    assert statistics.median(output_apes) < statistics.median(old_output_apes)


def test_estimate_mode_rejects_non_generate_commands(tmp_path):
    import pdd.cli  # noqa: F401 - registers commands on the core CLI
    from pdd.core.cli import cli

    result = CliRunner().invoke(
        cli,
        ["--estimate-json", "--no-core-dump", "sync", "demo"],
    )

    assert result.exit_code != 0
    assert "Estimate mode currently supports `generate` only." in result.output
