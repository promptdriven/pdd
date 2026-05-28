# User Story: Payment flow with unknown rule references

<!-- pdd-story-prompts: payment_api_clean_python.prompt -->

## Story
As a merchant, I want charges processed reliably.

## Acceptance Criteria
1. Given an authorized merchant, when they submit a valid charge, then the system returns HTTP 201.
2. Given a fraudulent transaction, when submitted, then the system rejects it.

## Covers
- R1: idempotency enforced
- R99: non-existent rule referenced here
- R100: another unknown rule ID
