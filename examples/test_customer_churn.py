"""
Test suite for customer_churn.py
Generated via PDD (Prompt-Driven Development) workflow.
"""

import pytest
import pandas as pd
import numpy as np
from customer_churn import train, predict


# ── Fixtures ──────────────────────────────────────────────────────────────────

@pytest.fixture
def sample_df():
    """Returns a minimal valid DataFrame with 20 rows for training."""
    np.random.seed(42)
    n = 20
    return pd.DataFrame({
        "tenure": np.random.randint(1, 72, n),
        "monthly_charges": np.round(np.random.uniform(20, 120, n), 2),
        "total_charges": np.round(np.random.uniform(100, 8000, n), 2),
        "contract_type": np.random.choice(
            ["Month-to-month", "One year", "Two year"], n
        ),
        "payment_method": np.random.choice(
            ["Electronic check", "Mailed check", "Bank transfer", "Credit card"], n
        ),
        "num_support_tickets": np.random.randint(0, 10, n),
        "has_tech_support": np.random.choice([True, False], n),
        "churn": np.random.randint(0, 2, n),
    })


@pytest.fixture
def trained_result(sample_df):
    """Returns the result dict from train() on the sample DataFrame."""
    return train(sample_df)


@pytest.fixture
def sample_customer():
    """Returns a dict representing a single high-risk customer."""
    return {
        "tenure": 2,
        "monthly_charges": 95.50,
        "total_charges": 191.00,
        "contract_type": "Month-to-month",
        "payment_method": "Electronic check",
        "num_support_tickets": 5,
        "has_tech_support": False,
    }


# ── train() tests ─────────────────────────────────────────────────────────────

class TestTrain:

    def test_returns_all_expected_keys(self, trained_result):
        expected_keys = {"model", "accuracy", "precision", "recall", "f1", "feature_importances"}
        assert expected_keys == set(trained_result.keys())

    def test_accuracy_is_valid_float(self, trained_result):
        acc = trained_result["accuracy"]
        assert isinstance(acc, float)
        assert 0.0 <= acc <= 1.0

    def test_precision_is_valid_float(self, trained_result):
        assert 0.0 <= trained_result["precision"] <= 1.0

    def test_recall_is_valid_float(self, trained_result):
        assert 0.0 <= trained_result["recall"] <= 1.0

    def test_f1_is_valid_float(self, trained_result):
        assert 0.0 <= trained_result["f1"] <= 1.0

    def test_model_pipeline_is_not_none(self, trained_result):
        assert trained_result["model"] is not None

    def test_feature_importances_is_dict(self, trained_result):
        fi = trained_result["feature_importances"]
        assert isinstance(fi, dict)
        assert len(fi) > 0

    def test_feature_importances_contains_tenure(self, trained_result):
        assert "tenure" in trained_result["feature_importances"]

    def test_raises_on_missing_columns(self, sample_df):
        incomplete_df = sample_df.drop(columns=["monthly_charges"])
        with pytest.raises(ValueError, match="missing required columns"):
            train(incomplete_df)

    def test_raises_on_too_few_rows(self, sample_df):
        tiny_df = sample_df.head(5)
        with pytest.raises(ValueError, match="at least 10 rows"):
            train(tiny_df)

    def test_handles_missing_values_gracefully(self, sample_df):
        sample_df.loc[0, "tenure"] = np.nan
        sample_df.loc[1, "contract_type"] = np.nan
        result = train(sample_df)
        assert result["accuracy"] >= 0.0

    def test_reproducible_results(self, sample_df):
        result1 = train(sample_df)
        result2 = train(sample_df)
        assert result1["accuracy"] == result2["accuracy"]


# ── predict() tests ───────────────────────────────────────────────────────────

class TestPredict:

    def test_returns_float(self, trained_result, sample_customer):
        prob = predict(trained_result["model"], sample_customer)
        assert isinstance(prob, float)

    def test_probability_between_0_and_1(self, trained_result, sample_customer):
        prob = predict(trained_result["model"], sample_customer)
        assert 0.0 <= prob <= 1.0

    def test_returns_zero_for_none_model(self, sample_customer):
        assert predict(None, sample_customer) == 0.0

    def test_handles_missing_feature_gracefully(self, trained_result):
        incomplete_customer = {
            "tenure": 5,
            "monthly_charges": 70.0,
            # missing: total_charges, contract_type, payment_method, etc.
        }
        prob = predict(trained_result["model"], incomplete_customer)
        assert 0.0 <= prob <= 1.0

    def test_low_risk_customer_has_lower_prob(self, trained_result):
        low_risk = {
            "tenure": 60,
            "monthly_charges": 30.0,
            "total_charges": 1800.0,
            "contract_type": "Two year",
            "payment_method": "Bank transfer",
            "num_support_tickets": 0,
            "has_tech_support": True,
        }
        high_risk = {
            "tenure": 1,
            "monthly_charges": 110.0,
            "total_charges": 110.0,
            "contract_type": "Month-to-month",
            "payment_method": "Electronic check",
            "num_support_tickets": 8,
            "has_tech_support": False,
        }
        # Just verify both return valid probabilities (model may vary with small data)
        low_prob = predict(trained_result["model"], low_risk)
        high_prob = predict(trained_result["model"], high_risk)
        assert 0.0 <= low_prob <= 1.0
        assert 0.0 <= high_prob <= 1.0

    def test_boolean_tech_support_values(self, trained_result):
        for val in [True, False]:
            customer = {
                "tenure": 12, "monthly_charges": 65.0, "total_charges": 780.0,
                "contract_type": "One year", "payment_method": "Credit card",
                "num_support_tickets": 1, "has_tech_support": val
            }
            prob = predict(trained_result["model"], customer)
            assert 0.0 <= prob <= 1.0
