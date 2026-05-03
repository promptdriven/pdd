# Customer Churn Prediction — PDD Example

This example demonstrates a complete **Prompt-Driven Development** workflow for a real-world machine learning use case: **predicting customer churn** using logistic regression.

It is a companion to the core `hello` and `factorial_calculator` examples, showing PDD applied to a **data science / ML context** — a domain not previously covered in the official examples.

---

## What This Example Covers

| PDD Concept | Implementation |
|---|---|
| Prompt as source of truth | `prompts/customer_churn_python.prompt` |
| Code generated from prompt | `customer_churn.py` |
| Usage example | `example_customer_churn.py` |
| Unit test suite | `test_customer_churn.py` |

---

## Files

```
examples/customer_churn/
├── prompts/
│   └── customer_churn_python.prompt   # PDD prompt (source of truth)
├── customer_churn.py                  # Generated module
├── example_customer_churn.py          # Runnable demo
├── test_customer_churn.py             # Unit tests (pytest)
└── README.md                          # This file
```

---

## Prerequisites

```bash
pip install pandas numpy scikit-learn pytest
```

---

## Run the Example

```bash
cd examples/customer_churn
python example_customer_churn.py
```

**Expected output:**
```
=======================================================
  PDD Example: Customer Churn Prediction
=======================================================

📦 Generating synthetic customer dataset (100 rows)...
   Dataset shape : (100, 8)
   Churn rate    : 27.0%

🔧 Training logistic regression pipeline...

📊 Model Evaluation (held-out 20% test set):
   Accuracy  : 75.00%
   Precision : 60.00%
   Recall    : 50.00%
   F1 Score  : 54.55%

🔍 Top 5 Feature Importances (by abs coefficient):
   num_support_tickets              +0.5231  ↑ increases churn
   tenure                           -0.4812  ↓ decreases churn
   contract_type_Month-to-month     +0.3901  ↑ increases churn
   ...

🎯 Individual Customer Predictions:

   High-risk customer (month-to-month, 2 months tenure):
   → Churn probability: 68.42% 🔴

   Low-risk customer (2-year contract, 58 months tenure):
   → Churn probability: 18.75% 🟢
```

---

## Run the Tests

```bash
cd examples/customer_churn
pytest test_customer_churn.py -v
```

---

## Run with PDD

To regenerate the code from the prompt using PDD:

```bash
# From the repo root
pdd --force sync customer_churn
```

To implement improvements from a GitHub issue:

```bash
pdd change https://github.com/promptdriven/pdd/issues/<issue-number>
```

---

## About This Example

This example was contributed as part of a pull request to expand PDD's example library into the **machine learning / data science** domain. The prompt covers:

- **sklearn Pipeline** with `ColumnTransformer` for mixed-type preprocessing
- **Logistic Regression** binary classification
- **Evaluation metrics**: accuracy, precision, recall, F1
- **Edge case handling**: missing values, empty inputs, None model

It demonstrates that PDD's prompt-first approach scales naturally to ML workflows, where prompt clarity directly impacts the quality and reproducibility of generated model code.

---

*Contributed by [Darius Rowser](https://github.com/Drowser2430)*
