"""Tests for report generation and the pure-python statistics."""

from harness.runner.report import (
    evaluate_thresholds,
    generate_report,
    least_squares,
    spearman_rho,
)


def _record(size, trial, hidden, tokens, share, delta=0.05, shape="gradual",
            failure=None):
    return {
        "run_id": f"demo.{size}x.trial{trial}",
        "scenario_id": "demo",
        "size": f"{size}x",
        "size_multiplier": size,
        "hidden_pass": hidden,
        "visible_pass": True,
        "input_tokens_per_run": tokens,
        "input_tokens_before_first_edit": tokens // 2,
        "max_request_input_tokens": tokens // 3,
        "search_or_tool_calls_before_first_edit": 3,
        "iterations_total": 6,
        "distractor_tokens_on_disk": (size - 1) * 1000,
        "distractor_context_share": share,
        "distractor_pool_coverage": share / 2,
        "distractor_context_share_delta": delta,
        "growth_shape": shape,
        "wrong_file_edit_rate": 0.0,
        "wall_clock_seconds": 10.0,
        "failure_class": failure,
    }


def _degrading_records():
    records = []
    for trial in range(3):
        records.append(_record(1, trial, True, 5000, 0.0))
        records.append(_record(5, trial, True, 9000, 0.15))
        records.append(
            _record(20, trial, trial == 0, 14000, 0.30, delta=0.2)
        )
        records.append(
            _record(
                50, trial, False, 22000, 0.45, delta=0.25,
                failure="wrong_file_edit",
            )
        )
    return records


def test_least_squares_recovers_line():
    xs = [0, 1, 2, 3, 4]
    ys = [1, 3, 5, 7, 9]  # y = 1 + 2x
    alpha, beta, r_squared = least_squares(xs, ys)
    assert abs(alpha - 1) < 1e-9
    assert abs(beta - 2) < 1e-9
    assert abs(r_squared - 1) < 1e-9


def test_spearman_monotone_nonlinear():
    xs = [1, 2, 3, 4, 5]
    ys = [1, 8, 27, 64, 125]  # monotone, nonlinear
    assert abs(spearman_rho(xs, ys) - 1.0) < 1e-9
    assert abs(spearman_rho(xs, list(reversed(ys))) + 1.0) < 1e-9


def test_report_contains_table_fits_failures_thresholds():
    report = generate_report(_degrading_records())
    assert "| Metric | 1x | 5x | 20x | 50x |" in report
    assert "`hidden_pass_rate`" in report
    assert "Trend fits" in report
    assert "wrong_file_edit: 3" in report
    assert "Pre-registered thresholds" in report


def test_thresholds_crossed_on_degrading_data():
    verdicts = evaluate_thresholds(_degrading_records())
    assert verdicts["localization-cost rise (≥2x tokens)"][0] == "CROSSED"
    assert verdicts["context-penetration rise (≥0.20 share)"][0] == "CROSSED"
    assert verdicts["hidden-success drop (≥20 pp)"][0] == "CROSSED"
    assert verdicts["H2 within-run accumulation"][0] == "CROSSED"
    assert verdicts["H3 breakdown location"][0] == "S* = 20x"


def test_thresholds_flat_data_not_crossed():
    records = []
    for trial in range(3):
        for size in (1, 5, 20, 50):
            records.append(_record(size, trial, True, 5000, 0.02, delta=0.0))
    verdicts = evaluate_thresholds(records)
    assert verdicts["localization-cost rise (≥2x tokens)"][0] == "not crossed"
    assert verdicts["hidden-success drop (≥20 pp)"][0] == "not crossed"
    assert verdicts["H3 breakdown location"][0].startswith("S* > 50x")


def test_empty_report():
    assert "(no run records)" in generate_report([])


# -- evidence gating (proxy-evidenced vs development-only) --------------------


def test_token_rows_exclude_runs_without_proxy_evidence():
    supported = [_record(1, t, True, 5000, 0.0) for t in range(2)]
    ghost = _record(50, 0, False, 0, 0.0)
    ghost.update(
        {"token_metrics_supported": False, "iterations_total": 0,
         "input_tokens_per_run": 0, "failure_class": "other"}
    )
    for r in supported:
        r["token_metrics_supported"] = True
    report = generate_report(supported + [ghost])
    # The 50x run still counts for outcomes...
    assert "| `hidden_pass_rate` | 2/2 | 0/1 |" in report
    # ...but its zero token counts never enter the token medians.
    assert "| `input_tokens_per_run` (med) | 5000 | — |" in report
    assert "token-level metrics unsupported" in report
    assert "demo.50x.trial0" in report


def test_development_only_runs_excluded_entirely():
    supported = [_record(1, t, True, 5000, 0.0) for t in range(2)]
    dev = _record(1, 9, True, 9999, 0.9)
    dev["development_only"] = True
    report = generate_report(supported + [dev])
    assert "| `hidden_pass_rate` | 2/2 |" in report
    assert "development-only (command arm, env_fingerprint null)" in report
    verdicts = evaluate_thresholds(supported + [dev])
    # dev run's 9999 tokens must not shift the cost baseline
    assert "5000" in verdicts["localization-cost rise (≥2x tokens)"][1]


def test_all_development_only_yields_no_pilot_report():
    dev = _record(1, 0, True, 5000, 0.0)
    dev["development_only"] = True
    report = generate_report([dev])
    assert "no pilot records" in report


def test_thresholds_unsupported_without_endpoint_evidence():
    records = [_record(1, t, True, 5000, 0.0) for t in range(2)]
    big = _record(50, 0, True, 0, 0.0)
    big.update({"token_metrics_supported": False, "input_tokens_per_run": 0,
                "iterations_total": 0})
    verdicts = evaluate_thresholds(records + [big])
    assert verdicts["localization-cost rise (≥2x tokens)"][0] == "unsupported"
    assert verdicts["context-penetration rise (≥0.20 share)"][0] == "unsupported"
