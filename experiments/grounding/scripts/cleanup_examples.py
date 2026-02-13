#!/usr/bin/env python3
"""Delete seeded test data from Firestore (documents with IDs starting with 'grnd-').

Usage:
    python3 scripts/cleanup_examples.py --env local|staging
"""

from __future__ import annotations

import argparse
import os
import sys


def _init_firebase(env: str):
    """Initialise Firebase Admin SDK and return a Firestore client."""
    import firebase_admin
    from firebase_admin import credentials, firestore

    project_id = "prompt-driven-development-stg"

    if env == "local":
        os.environ.setdefault("FIRESTORE_EMULATOR_HOST", "127.0.0.1:8080")
        os.environ.setdefault("FIREBASE_AUTH_EMULATOR_HOST", "127.0.0.1:9098")
        os.environ["FUNCTIONS_EMULATOR"] = "true"

    try:
        app = firebase_admin.get_app("grounding_cleanup")
    except ValueError:
        cred = credentials.ApplicationDefault() if env == "staging" else None
        app = firebase_admin.initialize_app(
            cred, {"projectId": project_id}, name="grounding_cleanup"
        )

    return firestore.client(app=app), app


def cleanup(env: str) -> None:
    """Delete all grnd-* documents from relevant collections."""
    db, _app = _init_firebase(env)

    collections = ["few_shot", "few_shot_prompts", "few_shot_code", "few_shot_tests"]
    total_deleted = 0

    for col_name in collections:
        print(f"Scanning {col_name} for grnd-* documents...")
        col_ref = db.collection(col_name)

        # Firestore doesn't support prefix queries on document IDs directly,
        # so we list documents and filter client-side.
        docs = col_ref.stream()
        batch = db.batch()
        batch_count = 0

        for doc in docs:
            if doc.id.startswith("grnd-"):
                batch.delete(doc.reference)
                batch_count += 1

                # Commit in batches of 500 (Firestore limit)
                if batch_count >= 500:
                    batch.commit()
                    total_deleted += batch_count
                    print(f"  Deleted {batch_count} documents from {col_name}")
                    batch = db.batch()
                    batch_count = 0

        if batch_count > 0:
            batch.commit()
            total_deleted += batch_count
            print(f"  Deleted {batch_count} documents from {col_name}")

    # Also delete the test user
    user_ref = db.collection("users").document("grnd-test-user")
    if user_ref.get().exists:
        user_ref.delete()
        total_deleted += 1
        print("  Deleted test user: grnd-test-user")

    print(f"\nCleanup complete: {total_deleted} documents deleted.")


def main() -> int:
    parser = argparse.ArgumentParser(description="Clean up grounding experiment test data")
    parser.add_argument(
        "--env",
        choices=["local", "staging"],
        required=True,
        help="Target environment",
    )
    args = parser.parse_args()

    cleanup(args.env)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
