"""
Example usage of the customer_churn module.
Demonstrates the full PDD workflow: train → evaluate → predict.
"""

import pandas as pd
import numpy as np
from customer_churn import train, predict


def generate_sample_data(n: int = 100, seed: int = 42) -> pd.DataFrame:
    """Generate synthetic customer data for demonstration."""
    np.random.seed(seed)
    return pd.DataFrame({
        "tenure": np.random.randint(1, 72, n),
        "monthly_charges": np.round(np.random.uniform(20.0, 120.0, n), 2),
        "total_charges": np.round(np.random.uniform(100.0, 8640.0, n), 2),
        "contract_type": np.random.choice(
            ["Month-to-month", "One year", "Two year"], n, p=[0.55, 0.25, 0.20]
        ),
        "payment_method": np.random.choice(
            ["Electronic check", "Mailed check", "Bank transfer", "Credit card"], n
        ),
        "num_support_tickets": np.random.randint(0, 10, n),
        "has_tech_support": np.random.choice([True, False], n, p=[0.35, 0.65]),
        "churn": np.random.choice([0, 1], n, p=[0.73, 0.27]),  # ~27% churn rate
    })


def main():
    print("=" * 55)
    print("  PDD Example: Customer Churn Prediction")
    print("=" * 55)

    # Step 1: Generate synthetic data
    print("\n📦 Generating synthetic customer dataset (100 rows)...")
    df = generate_sample_data(n=100)
    churn_rate = df["churn"].mean()
    print(f"   Dataset shape : {df.shape}")
    print(f"   Churn rate    : {churn_rate:.1%}")

    # Step 2: Train the model
    print("\n🔧 Training logistic regression pipeline...")
    result = train(df)

    print(f"\n📊 Model Evaluation (held-out 20% test set):")
    print(f"   Accuracy  : {result['accuracy']:.2%}")
    print(f"   Precision : {result['precision']:.2%}")
    print(f"   Recall    : {result['recall']:.2%}")
    print(f"   F1 Score  : {result['f1']:.2%}")

    # Step 3: Show top feature importances
    print("\n🔍 Top 5 Feature Importances (by abs coefficient):")
    fi = result["feature_importances"]
    sorted_fi = sorted(fi.items(), key=lambda x: abs(x[1]), reverse=True)[:5]
    for feat, coef in sorted_fi:
        direction = "↑ increases churn" if coef > 0 else "↓ decreases churn"
        print(f"   {feat:<40} {coef:+.4f}  {direction}")

    # Step 4: Predict on individual customers
    print("\n🎯 Individual Customer Predictions:")

    high_risk_customer = {
        "tenure": 2,
        "monthly_charges": 99.95,
        "total_charges": 199.90,
        "contract_type": "Month-to-month",
        "payment_method": "Electronic check",
        "num_support_tickets": 6,
        "has_tech_support": False,
    }

    low_risk_customer = {
        "tenure": 58,
        "monthly_charges": 25.10,
        "total_charges": 1455.80,
        "contract_type": "Two year",
        "payment_method": "Bank transfer",
        "num_support_tickets": 0,
        "has_tech_support": True,
    }

    high_prob = predict(result["model"], high_risk_customer)
    low_prob = predict(result["model"], low_risk_customer)

    print(f"\n   High-risk customer (month-to-month, 2 months tenure):")
    print(f"   → Churn probability: {high_prob:.2%} {'🔴' if high_prob > 0.5 else '🟡'}")

    print(f"\n   Low-risk customer (2-year contract, 58 months tenure):")
    print(f"   → Churn probability: {low_prob:.2%} {'🟢' if low_prob < 0.3 else '🟡'}")

    print("\n" + "=" * 55)
    print("  ✅ PDD customer_churn example complete!")
    print("=" * 55)


if __name__ == "__main__":
    main()
