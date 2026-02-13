#!/usr/bin/env python3
"""Seed test examples into Firestore for grounding retrieval experiments.

Usage:
    python3 scripts/seed_examples.py --env local|staging [--dry-run]

Reuses patterns from backend/tests/endpoint_tests/test_data.py.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import json
import os
import sys
import time
from pathlib import Path
from typing import List

# ---------------------------------------------------------------------------
# Embedding helpers (mirrors test_data.py:17-77)
# ---------------------------------------------------------------------------

@functools.lru_cache(maxsize=32)
def _get_real_embedding(text: str) -> List[float]:
    """Generate an embedding compatible with the reviewExamples endpoint.

    - Emulator: deterministic SHA-based vectors (matches emulator behaviour).
    - Staging: real gemini-embedding-001 vectors via Google AI SDK.
    """
    in_emulator = os.environ.get("FUNCTIONS_EMULATOR") == "true"
    if in_emulator and os.environ.get("EMBEDDINGS_ONLINE", "0") != "1":
        print(f"  Using deterministic embedding for emulator: {text[:50]}...")
        return _deterministic_embedding(text)

    api_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("VERTEX_AI_API_KEY")
    if not api_key:
        print("  Warning: No API key found, using deterministic fallback")
        return _deterministic_embedding(text)

    try:
        from google import genai
        from google.genai import types
        client = genai.Client(api_key=api_key)
        config = types.EmbedContentConfig(output_dimensionality=768)
        resp = client.models.embed_content(model="gemini-embedding-001", contents=text, config=config)
        embeddings = getattr(resp, "embeddings", None)
        if not embeddings or not getattr(embeddings[0], "values", None):
            raise RuntimeError("Empty embedding returned from Google AI SDK")
        embedding = embeddings[0].values
        print(f"  Generated real embedding for: {text[:50]}...")
        if hasattr(embedding, "tolist"):
            embedding = embedding.tolist()
        return list(embedding)
    except Exception as e:
        print(f"  Warning: Failed to generate real embedding: {e}")
        return _deterministic_embedding(text)


def _deterministic_embedding(text: str, dim: int = 768) -> List[float]:
    """SHA-based deterministic pseudo-embedding (matches vector_helpers.py:32-54)."""
    values: List[float] = []
    seed = text.encode("utf-8")
    counter = 0
    while len(values) < dim:
        h = hashlib.sha256(seed + counter.to_bytes(4, "big")).digest()
        for i in range(0, len(h), 4):
            if len(values) >= dim:
                break
            chunk = int.from_bytes(h[i : i + 4], "big", signed=False)
            x = (chunk % 10_000_000) / 10_000_000.0
            values.append(x * 0.2 - 0.1)
        counter += 1
    return values


# ---------------------------------------------------------------------------
# Firebase helpers
# ---------------------------------------------------------------------------

def _init_firebase(env: str):
    """Initialise Firebase Admin SDK and return a Firestore client."""
    import firebase_admin
    from firebase_admin import credentials, firestore

    project_id = "prompt-driven-development-stg"

    if env == "local":
        os.environ.setdefault("FIRESTORE_EMULATOR_HOST", "127.0.0.1:8080")
        os.environ.setdefault("FIREBASE_AUTH_EMULATOR_HOST", "127.0.0.1:9098")
        os.environ["FUNCTIONS_EMULATOR"] = "true"

    # Avoid double-init
    try:
        app = firebase_admin.get_app("grounding_seed")
    except ValueError:
        cred = credentials.ApplicationDefault() if env == "staging" else None
        app = firebase_admin.initialize_app(
            cred, {"projectId": project_id}, name="grounding_seed"
        )

    return firestore.client(app=app), app


# ---------------------------------------------------------------------------
# Seeding logic (mirrors test_data.py:591-711)
# ---------------------------------------------------------------------------

def seed_examples(env: str, dry_run: bool = False) -> None:
    """Upload test examples from domains.json into Firestore."""
    from firebase_admin import firestore as fs_module
    from google.cloud.firestore_v1.vector import Vector

    data_path = Path(__file__).resolve().parent.parent / "seed_data" / "domains.json"
    with data_path.open("r", encoding="utf-8") as f:
        data = json.load(f)

    examples = data["examples"]
    print(f"Seeding {len(examples)} examples into {env} ...")

    if dry_run:
        for ex in examples:
            print(f"  [dry-run] Would create {ex['id']} ({ex['title']})")
        return

    db, _app = _init_firebase(env)

    # Create a test user for createdBy references
    user_id = "grnd-test-user"
    user_ref = db.collection("users").document(user_id)
    if not user_ref.get().exists:
        user_ref.set({
            "uid": user_id,
            "email": "grnd-test@example.com",
            "displayName": "Grounding Test User",
            "credits": 5000,
            "isAdmin": True,
            "createdAt": fs_module.SERVER_TIMESTAMP,
            "updatedAt": fs_module.SERVER_TIMESTAMP,
        })
        print(f"  Created test user: {user_id}")

    for ex in examples:
        doc_id = ex["id"]
        print(f"  Seeding {doc_id} ({ex['title']}) ...")

        # 1. Create prompt subcollection doc
        prompt_ref = db.collection("few_shot_prompts").document(f"{doc_id}-prompt")
        prompt_ref.set({
            "content": ex["prompt_text"],
            "file_name": "prompt.txt",
            "created_at": fs_module.SERVER_TIMESTAMP,
        })

        # 2. Create code subcollection doc
        code_ref = db.collection("few_shot_code").document(f"{doc_id}-code")
        code_ref.set({
            "content": ex["code_content"],
            "file_name": f"{doc_id}.py" if ex["language"] == "Python" else f"{doc_id}.js",
            "created_at": fs_module.SERVER_TIMESTAMP,
        })

        # 3. Generate embedding
        embedding = _get_real_embedding(ex["prompt_text"])

        # 4. Write main few_shot document
        few_shot_ref = db.collection("few_shot").document(doc_id)
        few_shot_ref.set({
            "slug": ex["slug"],
            "createdBy": user_id,
            "marketplace": {
                "lifecycleState": ex["lifecycle_state"],
                "exclusionMode": "none",
            },
            "metadata": {
                "command": ex["command"],
                "title": ex["title"],
                "language": ex["language"],
                "userRank": 100,
                "isPublic": ex["is_public"],
                "createdAt": fs_module.SERVER_TIMESTAMP,
            },
            "inputRefs": {
                "prompts": [prompt_ref],
                "code": [code_ref],
                "test": [],
            },
            "outputRefs": {
                "code": [code_ref],
                "test": [],
            },
            "input": {
                "prompts": [{"content": ex["prompt_text"], "file_name": "prompt.txt"}],
                "code": [{"content": ex["code_content"], "file_name": "code.py"}],
                "test": [],
                "error": [],
                "example": [],
            },
            "output": {
                "code": [{"content": ex["code_content"], "file_name": "code.py"}],
                "test": [],
                "analysis": [],
                "prompts": [],
                "example": [],
            },
            "embeddings": {
                "current": {
                    "vector": Vector(embedding),
                },
            },
        })

        print(f"    OK {doc_id}")

    # Brief delay for emulator propagation
    if env == "local":
        time.sleep(0.5)

    print(f"\nSeeded {len(examples)} examples successfully.")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description="Seed grounding experiment test data")
    parser.add_argument(
        "--env",
        choices=["local", "staging"],
        required=True,
        help="Target environment",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print what would be created without writing",
    )
    args = parser.parse_args()

    seed_examples(args.env, dry_run=args.dry_run)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
