"""
Customer Churn Prediction Module
Generated via PDD (Prompt-Driven Development) workflow.
Prompt: prompts/customer_churn_python.prompt
"""

import pandas as pd
import numpy as np
from sklearn.pipeline import Pipeline
from sklearn.compose import ColumnTransformer
from sklearn.preprocessing import StandardScaler, OneHotEncoder
from sklearn.impute import SimpleImputer
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import train_test_split
from sklearn.metrics import accuracy_score, precision_score, recall_score, f1_score
from typing import Optional


REQUIRED_COLUMNS = [
    "tenure", "monthly_charges", "total_charges",
    "contract_type", "payment_method",
    "num_support_tickets", "has_tech_support", "churn"
]

NUMERIC_FEATURES = ["tenure", "monthly_charges", "total_charges", "num_support_tickets"]
CATEGORICAL_FEATURES = ["contract_type", "payment_method"]
BOOL_FEATURES = ["has_tech_support"]


def _validate_dataframe(df: pd.DataFrame, require_churn: bool = True) -> None:
    """Validate that the DataFrame has the required columns and sufficient rows."""
    required = REQUIRED_COLUMNS if require_churn else [c for c in REQUIRED_COLUMNS if c != "churn"]
    missing = [col for col in required if col not in df.columns]
    if missing:
        raise ValueError(f"DataFrame is missing required columns: {missing}")
    if len(df) < 10:
        raise ValueError(f"DataFrame must have at least 10 rows, got {len(df)}")


def _build_pipeline() -> Pipeline:
    """Build the sklearn preprocessing and model pipeline."""
    numeric_transformer = Pipeline(steps=[
        ("imputer", SimpleImputer(strategy="median")),
        ("scaler", StandardScaler())
    ])

    categorical_transformer = Pipeline(steps=[
        ("imputer", SimpleImputer(strategy="most_frequent")),
        ("onehot", OneHotEncoder(handle_unknown="ignore", sparse_output=False))
    ])

    bool_transformer = Pipeline(steps=[
        ("imputer", SimpleImputer(strategy="most_frequent")),
        ("scaler", StandardScaler())
    ])

    preprocessor = ColumnTransformer(transformers=[
        ("num", numeric_transformer, NUMERIC_FEATURES),
        ("cat", categorical_transformer, CATEGORICAL_FEATURES),
        ("bool", bool_transformer, BOOL_FEATURES)
    ])

    pipeline = Pipeline(steps=[
        ("preprocessor", preprocessor),
        ("classifier", LogisticRegression(max_iter=1000, random_state=42))
    ])

    return pipeline


def train(df: pd.DataFrame) -> dict:
    """
    Train a customer churn prediction model on the provided DataFrame.

    Args:
        df: A pandas DataFrame containing customer features and 'churn' label.
            Required columns: tenure, monthly_charges, total_charges,
            contract_type, payment_method, num_support_tickets,
            has_tech_support, churn.

    Returns:
        A dict with keys:
            - "model": fitted sklearn Pipeline
            - "accuracy": float
            - "precision": float
            - "recall": float
            - "f1": float
            - "feature_importances": dict mapping feature names to coefficients

    Raises:
        ValueError: If required columns are missing or DataFrame has fewer than 10 rows.
    """
    _validate_dataframe(df, require_churn=True)

    df = df.copy()
    df["has_tech_support"] = df["has_tech_support"].astype(float)

    X = df[NUMERIC_FEATURES + CATEGORICAL_FEATURES + BOOL_FEATURES]
    y = df["churn"].astype(int)

    X_train, X_test, y_train, y_test = train_test_split(
        X, y, test_size=0.2, random_state=42
    )

    pipeline = _build_pipeline()
    pipeline.fit(X_train, y_train)

    y_pred = pipeline.predict(X_test)

    accuracy = accuracy_score(y_test, y_pred)
    precision = precision_score(y_test, y_pred, zero_division=0)
    recall = recall_score(y_test, y_pred, zero_division=0)
    f1 = f1_score(y_test, y_pred, zero_division=0)

    # Extract feature importances (logistic regression coefficients)
    ohe_features = list(
        pipeline.named_steps["preprocessor"]
        .named_transformers_["cat"]
        .named_steps["onehot"]
        .get_feature_names_out(CATEGORICAL_FEATURES)
    )
    all_feature_names = NUMERIC_FEATURES + ohe_features + BOOL_FEATURES
    coefficients = pipeline.named_steps["classifier"].coef_[0]
    feature_importances = dict(zip(all_feature_names, coefficients.tolist()))

    return {
        "model": pipeline,
        "accuracy": round(accuracy, 4),
        "precision": round(precision, 4),
        "recall": round(recall, 4),
        "f1": round(f1, 4),
        "feature_importances": feature_importances
    }


def predict(model_pipeline: Optional[Pipeline], customer: dict) -> float:
    """
    Predict churn probability for a single customer.

    Args:
        model_pipeline: A fitted sklearn Pipeline returned by train().
                        Returns 0.0 if None.
        customer: A dict with customer feature values. Required keys:
                  tenure, monthly_charges, total_charges, contract_type,
                  payment_method, num_support_tickets, has_tech_support.

    Returns:
        Churn probability as a float between 0.0 and 1.0.
    """
    if model_pipeline is None:
        return 0.0

    customer_copy = dict(customer)
    customer_copy["has_tech_support"] = float(customer_copy.get("has_tech_support", False))

    input_df = pd.DataFrame([customer_copy])
    feature_cols = NUMERIC_FEATURES + CATEGORICAL_FEATURES + BOOL_FEATURES

    for col in feature_cols:
        if col not in input_df.columns:
            input_df[col] = np.nan

    input_df = input_df[feature_cols]
    proba = model_pipeline.predict_proba(input_df)[0][1]
    return round(float(proba), 4)
