"""Tests for pdd.embed_retrieve module."""

from __future__ import annotations

import math
from typing import List
from unittest.mock import MagicMock, patch

import pytest

from pdd.embed_retrieve import embed_and_retrieve


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_embedding_response(texts: List[str], dim: int = 8) -> MagicMock:
    """Build a mock litellm embedding response with deterministic vectors.

    Each text gets a vector based on word overlap with a small vocabulary,
    normalized to unit length so cosine similarity is meaningful.
    """
    vocab = ["auth", "login", "user", "cache", "db", "query", "api", "server"][:dim]
    embeddings = []
    for text in texts:
        words = text.lower().split()
        vec = [1.0 if v in words else 0.0 for v in vocab]
        norm = math.sqrt(sum(x * x for x in vec)) or 1.0
        vec = [x / norm for x in vec]
        embeddings.append(vec)

    response = MagicMock()
    response.data = [{"embedding": emb} for emb in embeddings]
    return response


def _make_fixed_embedding_response(vectors: List[List[float]]) -> MagicMock:
    """Build a mock response from pre-defined vectors."""
    response = MagicMock()
    response.data = [{"embedding": v} for v in vectors]
    return response


# ---------------------------------------------------------------------------
# Tests: empty / edge-case inputs
# ---------------------------------------------------------------------------

class TestEdgeCases:
    """Edge cases: empty candidates, top_n <= 0, empty query."""

    def test_empty_candidates_returns_empty(self):
        result = embed_and_retrieve("some query", [], top_n=5)
        assert result == []

    def test_top_n_zero_returns_empty(self):
        result = embed_and_retrieve("some query", ["a", "b"], top_n=0)
        assert result == []

    def test_top_n_negative_returns_empty(self):
        result = embed_and_retrieve("some query", ["a", "b"], top_n=-1)
        assert result == []

    def test_empty_query_returns_candidates_with_zero_score(self):
        candidates = ["alpha", "beta", "gamma"]
        result = embed_and_retrieve("", candidates, top_n=10)
        assert len(result) == 3
        assert all(score == 0.0 for _, score in result)
        assert [t for t, _ in result] == candidates

    def test_whitespace_only_query_returns_candidates_with_zero_score(self):
        candidates = ["alpha", "beta"]
        result = embed_and_retrieve("   ", candidates, top_n=10)
        assert len(result) == 2
        assert all(score == 0.0 for _, score in result)

    def test_empty_candidates_and_zero_top_n(self):
        result = embed_and_retrieve("query", [], top_n=0)
        assert result == []


# ---------------------------------------------------------------------------
# Tests: normal retrieval behaviour
# ---------------------------------------------------------------------------

class TestNormalRetrieval:
    """Core ranking behaviour with mocked litellm."""

    def test_returns_tuples_of_str_and_float(self):
        candidates = ["auth login user", "cache db query"]
        with patch(
            "litellm.embedding",
            side_effect=lambda model, input: _make_embedding_response(input),
        ):
            results = embed_and_retrieve("auth login", candidates, top_n=2)

        assert len(results) == 2
        for text, score in results:
            assert isinstance(text, str)
            assert isinstance(score, float)

    def test_results_sorted_descending_by_score(self):
        candidates = [
            "auth login user",
            "cache db query",
            "api server auth",
        ]
        with patch(
            "litellm.embedding",
            side_effect=lambda model, input: _make_embedding_response(input),
        ):
            results = embed_and_retrieve("auth login user", candidates, top_n=3)

        scores = [s for _, s in results]
        assert scores == sorted(scores, reverse=True)

    def test_top_n_limits_output(self):
        candidates = [f"candidate {i}" for i in range(10)]
        with patch(
            "litellm.embedding",
            side_effect=lambda model, input: _make_embedding_response(input),
        ):
            results = embed_and_retrieve("auth", candidates, top_n=3)

        assert len(results) <= 3

    def test_top_n_larger_than_candidates(self):
        candidates = ["auth login", "cache db"]
        with patch(
            "litellm.embedding",
            side_effect=lambda model, input: _make_embedding_response(input),
        ):
            results = embed_and_retrieve("auth", candidates, top_n=100)

        assert len(results) == 2

    def test_most_similar_candidate_ranked_first(self):
        """The candidate most similar to the query should be ranked first."""
        # query = [1,0,0], candidates: identical=[1,0,0], orthogonal=[0,1,0], partial=[0.7,0.7,0]
        query_vec = [1.0, 0.0, 0.0]
        identical_vec = [1.0, 0.0, 0.0]
        orthogonal_vec = [0.0, 1.0, 0.0]
        partial_norm = math.sqrt(0.7**2 + 0.7**2)
        partial_vec = [0.7 / partial_norm, 0.7 / partial_norm, 0.0]

        vectors = [query_vec, identical_vec, orthogonal_vec, partial_vec]

        candidates = ["identical", "orthogonal", "partial"]
        with patch(
            "litellm.embedding",
            return_value=_make_fixed_embedding_response(vectors),
        ):
            results = embed_and_retrieve("test query", candidates, top_n=3)

        assert results[0][0] == "identical"
        assert results[0][1] == pytest.approx(1.0, abs=1e-6)
        assert results[1][0] == "partial"
        assert results[2][0] == "orthogonal"
        assert results[2][1] == pytest.approx(0.0, abs=1e-6)


# ---------------------------------------------------------------------------
# Tests: cosine similarity correctness
# ---------------------------------------------------------------------------

class TestCosineSimilarity:
    """Verify cosine similarity computations are correct."""

    def test_identical_vectors_give_score_one(self):
        vec = [0.5, 0.5, 0.5, 0.5]
        vectors = [vec, vec]  # query + 1 candidate
        candidates = ["same"]
        with patch(
            "litellm.embedding",
            return_value=_make_fixed_embedding_response(vectors),
        ):
            results = embed_and_retrieve("q", candidates, top_n=1)

        assert results[0][1] == pytest.approx(1.0, abs=1e-6)

    def test_orthogonal_vectors_give_score_zero(self):
        query_vec = [1.0, 0.0, 0.0]
        cand_vec = [0.0, 1.0, 0.0]
        vectors = [query_vec, cand_vec]
        candidates = ["orthogonal"]
        with patch(
            "litellm.embedding",
            return_value=_make_fixed_embedding_response(vectors),
        ):
            results = embed_and_retrieve("q", candidates, top_n=1)

        assert results[0][1] == pytest.approx(0.0, abs=1e-6)

    def test_opposite_vectors_give_negative_score(self):
        query_vec = [1.0, 0.0]
        cand_vec = [-1.0, 0.0]
        vectors = [query_vec, cand_vec]
        candidates = ["opposite"]
        with patch(
            "litellm.embedding",
            return_value=_make_fixed_embedding_response(vectors),
        ):
            results = embed_and_retrieve("q", candidates, top_n=1)

        assert results[0][1] < 0.0


# ---------------------------------------------------------------------------
# Tests: graceful fallback on errors
# ---------------------------------------------------------------------------

class TestFallbackBehaviour:
    """When the embedding call fails, return all candidates with score 0.0."""

    def test_connection_error_returns_all_with_zero(self):
        candidates = ["a", "b", "c"]
        with patch("litellm.embedding", side_effect=ConnectionError("no network")):
            results = embed_and_retrieve("query", candidates, top_n=10)

        assert len(results) == 3
        assert all(score == 0.0 for _, score in results)

    def test_runtime_error_returns_all_with_zero(self):
        candidates = ["x", "y"]
        with patch("litellm.embedding", side_effect=RuntimeError("bad model")):
            results = embed_and_retrieve("query", candidates, top_n=10)

        assert len(results) == 2
        assert all(score == 0.0 for _, score in results)

    def test_fallback_respects_top_n(self):
        candidates = ["a", "b", "c", "d", "e"]
        with patch("litellm.embedding", side_effect=ValueError("fail")):
            results = embed_and_retrieve("query", candidates, top_n=2)

        assert len(results) == 2
        assert all(score == 0.0 for _, score in results)

    def test_fallback_preserves_candidate_order(self):
        candidates = ["first", "second", "third"]
        with patch("litellm.embedding", side_effect=Exception("fail")):
            results = embed_and_retrieve("query", candidates, top_n=10)

        texts = [t for t, _ in results]
        assert texts == candidates


# ---------------------------------------------------------------------------
# Tests: embedding model configuration
# ---------------------------------------------------------------------------

class TestModelConfiguration:
    """PDD_EMBEDDING_MODEL env var controls the embedding model."""

    def test_default_model_is_text_embedding_3_small(self, monkeypatch):
        monkeypatch.delenv("PDD_EMBEDDING_MODEL", raising=False)
        candidates = ["test"]
        with patch(
            "litellm.embedding",
            side_effect=lambda model, input: _make_embedding_response(input),
        ) as mock_emb:
            embed_and_retrieve("query", candidates, top_n=1)
            mock_emb.assert_called_once()
            call_kwargs = mock_emb.call_args
            assert call_kwargs.kwargs.get("model") or call_kwargs[1].get("model") == "text-embedding-3-small"

    def test_custom_model_from_env(self, monkeypatch):
        monkeypatch.setenv("PDD_EMBEDDING_MODEL", "text-embedding-3-large")
        candidates = ["test"]
        with patch(
            "litellm.embedding",
            side_effect=lambda model, input: _make_embedding_response(input),
        ) as mock_emb:
            embed_and_retrieve("query", candidates, top_n=1)
            call_kwargs = mock_emb.call_args
            used_model = call_kwargs.kwargs.get("model") or call_kwargs[1].get("model")
            assert used_model == "text-embedding-3-large"


# ---------------------------------------------------------------------------
# Tests: batching
# ---------------------------------------------------------------------------

class TestBatching:
    """Query and all candidates should be embedded in a single batched call."""

    def test_single_embedding_call_for_all_texts(self):
        candidates = ["c1", "c2", "c3"]
        with patch(
            "litellm.embedding",
            side_effect=lambda model, input: _make_embedding_response(input),
        ) as mock_emb:
            embed_and_retrieve("query", candidates, top_n=3)
            mock_emb.assert_called_once()
            # input should be [query] + candidates = 4 items
            call_input = mock_emb.call_args.kwargs.get("input") or mock_emb.call_args[1].get("input")
            assert len(call_input) == 4

    def test_query_is_first_in_batch(self):
        candidates = ["c1", "c2"]
        with patch(
            "litellm.embedding",
            side_effect=lambda model, input: _make_embedding_response(input),
        ) as mock_emb:
            embed_and_retrieve("my query", candidates, top_n=2)
            call_input = mock_emb.call_args.kwargs.get("input") or mock_emb.call_args[1].get("input")
            assert call_input[0] == "my query"
            assert call_input[1:] == candidates


# ---------------------------------------------------------------------------
# Tests: zero-vector handling
# ---------------------------------------------------------------------------

class TestZeroVector:
    """Zero-vector edge cases in embeddings."""

    def test_zero_query_vector_returns_zero_scores(self):
        zero = [0.0, 0.0, 0.0]
        cand = [1.0, 0.0, 0.0]
        vectors = [zero, cand]
        candidates = ["some candidate"]
        with patch(
            "litellm.embedding",
            return_value=_make_fixed_embedding_response(vectors),
        ):
            results = embed_and_retrieve("q", candidates, top_n=1)

        assert len(results) == 1
        assert results[0][1] == 0.0

    def test_zero_candidate_vector_does_not_crash(self):
        query = [1.0, 0.0, 0.0]
        zero_cand = [0.0, 0.0, 0.0]
        normal_cand = [1.0, 0.0, 0.0]
        vectors = [query, zero_cand, normal_cand]
        candidates = ["zero", "normal"]
        with patch(
            "litellm.embedding",
            return_value=_make_fixed_embedding_response(vectors),
        ):
            results = embed_and_retrieve("q", candidates, top_n=2)

        assert len(results) == 2
        # normal candidate should rank higher
        assert results[0][0] == "normal"
