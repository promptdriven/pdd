"""
Example usage of the embed_retrieve module for embedding-based coarse retrieval.

Demonstrates how to use embed_and_retrieve() to rank text candidates by
semantic similarity to a query, using litellm embeddings and cosine similarity.

External dependencies (litellm) are mocked so this example runs standalone.
"""

import os
import sys
from unittest.mock import MagicMock, patch

from pdd.embed_retrieve import embed_and_retrieve


def make_mock_embedding_response(texts):
    """Build a mock litellm embedding response with deterministic vectors.

    Each text gets a simple vector based on word overlap with a fixed vocabulary,
    producing realistic-looking cosine similarity rankings.
    """
    import math

    vocab = ["authentication", "login", "user", "session", "database",
             "query", "cache", "server", "api", "endpoint", "token",
             "password", "security", "middleware", "config"]

    embeddings = []
    for text in texts:
        words = text.lower().split()
        vec = [1.0 if v in words else 0.0 for v in vocab]
        # Normalize to unit length
        norm = math.sqrt(sum(x * x for x in vec)) or 1.0
        vec = [x / norm for x in vec]
        embeddings.append(vec)

    # Build mock response matching litellm's response shape
    response = MagicMock()
    response.data = [{"embedding": emb} for emb in embeddings]
    return response


def example_basic_retrieval():
    """Demonstrate basic embedding-based retrieval with top-N ranking."""
    print("=== Example 1: Basic Retrieval ===")

    query = "user authentication login session"
    candidates = [
        "authentication login user session token password security",
        "database query cache server api endpoint",
        "config middleware server api",
        "user login authentication password token",
        "cache database query endpoint",
    ]

    # Mock litellm.embedding to avoid needing a real API key.
    # litellm is imported inside the function body, so we patch the module directly.
    with patch("litellm.embedding", side_effect=lambda model, input: make_mock_embedding_response(input)):
        results = embed_and_retrieve(query, candidates, top_n=3)

    print(f"Query: {query!r}")
    print(f"Candidates: {len(candidates)}")
    print(f"Top-N requested: 3")
    print(f"Results returned: {len(results)}")
    for i, (text, score) in enumerate(results, 1):
        print(f"  {i}. score={score:.4f} | {text}")
    print()

    # Results are sorted by descending similarity
    assert len(results) <= 3
    assert all(isinstance(r, tuple) and len(r) == 2 for r in results)
    scores = [s for _, s in results]
    assert scores == sorted(scores, reverse=True), "Results must be sorted by descending score"


def example_edge_cases():
    """Demonstrate edge case handling."""
    print("=== Example 2: Edge Cases ===")

    # Empty candidates → empty list
    result = embed_and_retrieve("some query", [], top_n=5)
    print(f"Empty candidates: {result}")
    assert result == []

    # top_n <= 0 → empty list
    result = embed_and_retrieve("some query", ["candidate"], top_n=0)
    print(f"top_n=0: {result}")
    assert result == []

    result = embed_and_retrieve("some query", ["candidate"], top_n=-1)
    print(f"top_n=-1: {result}")
    assert result == []

    print("All edge cases handled correctly.\n")


def example_api_failure_fallback():
    """Demonstrate graceful fallback when embedding API fails."""
    print("=== Example 3: API Failure Fallback ===")

    candidates = ["doc about auth", "doc about caching", "doc about logging"]

    # Simulate an API failure (e.g., missing API key, network error)
    with patch("litellm.embedding", side_effect=ConnectionError("API unreachable")):
        results = embed_and_retrieve("search query", candidates, top_n=10)

    print(f"Candidates: {len(candidates)}")
    print(f"Results on failure: {len(results)}")
    for text, score in results:
        print(f"  score={score:.1f} | {text}")
    print()

    # On failure, all candidates returned with score 0.0
    assert len(results) == len(candidates)
    assert all(score == 0.0 for _, score in results)


def example_custom_model():
    """Demonstrate configuring the embedding model via environment variable."""
    print("=== Example 4: Custom Embedding Model ===")

    # PDD_EMBEDDING_MODEL controls which model litellm uses
    # Default is "text-embedding-3-small"
    original = os.environ.get("PDD_EMBEDDING_MODEL")
    os.environ["PDD_EMBEDDING_MODEL"] = "text-embedding-3-large"

    candidates = ["authentication module", "database layer"]

    with patch("litellm.embedding", side_effect=lambda model, input: make_mock_embedding_response(input)) as mock_emb:
        results = embed_and_retrieve("auth", candidates, top_n=2)

        # Verify the custom model was passed to litellm
        call_args = mock_emb.call_args
        print(f"Model used: {call_args.kwargs.get('model', call_args[1].get('model', 'unknown'))}")

    print(f"Results: {len(results)}")
    for text, score in results:
        print(f"  score={score:.4f} | {text}")
    print()

    # Clean up
    if original is None:
        del os.environ["PDD_EMBEDDING_MODEL"]
    else:
        os.environ["PDD_EMBEDDING_MODEL"] = original


if __name__ == "__main__":
    example_basic_retrieval()
    example_edge_cases()
    example_api_failure_fallback()
    example_custom_model()
    print("All examples completed successfully.")
