from __future__ import annotations

import logging
import os
from typing import List, Tuple

from rich.console import Console

logger = logging.getLogger(__name__)
console = Console()


def embed_and_retrieve(
    query: str,
    candidates: List[str],
    top_n: int = 50,
) -> List[Tuple[str, float]]:
    """Embed a query and candidate texts, returning the top-N candidates ranked by cosine similarity.

    Uses ``litellm.embedding()`` to compute vector representations and numpy
    for cosine-similarity scoring.  When the embedding call fails for any
    reason the function degrades gracefully by returning **all** candidates
    with a similarity score of ``0.0``.

    Args:
        query: The prompt / search text to match against.
        candidates: A list of candidate text strings (e.g. file summaries).
        top_n: Maximum number of results to return.  Must be > 0 for any
            results to be produced.

    Returns:
        A list of ``(candidate_text, similarity_score)`` tuples sorted in
        descending order of cosine similarity.  At most ``top_n`` entries are
        returned.  An empty list is returned when *candidates* is empty or
        *top_n* ≤ 0.
    """

    # ── fast-exit edge cases ────────────────────────────────────────────
    if not candidates or top_n <= 0:
        return []

    if not query or not isinstance(query, str) or query.strip() == "":
        console.print(
            "[yellow]Warning:[/yellow] empty or invalid query – returning all candidates with score 0.0"
        )
        logger.warning("embed_and_retrieve called with empty/invalid query")
        return [(c, 0.0) for c in candidates[:top_n]]

    # ── resolve embedding model ─────────────────────────────────────────
    model: str = os.environ.get("PDD_EMBEDDING_MODEL", "text-embedding-3-small")

    # ── compute embeddings ──────────────────────────────────────────────
    try:
        import litellm  # function-scope: heavy / optional dependency
        import numpy as np  # function-scope: heavy dependency

        # Build the full list of texts to embed in a single batched call.
        texts: List[str] = [query] + list(candidates)

        response = litellm.embedding(model=model, input=texts)

        # litellm returns an object whose `data` attribute is a list of
        # embedding objects, each with an `embedding` field (list[float]).
        raw_embeddings = [item["embedding"] for item in response.data]

        query_vec = np.asarray(raw_embeddings[0], dtype=np.float64)
        candidate_vecs = np.asarray(raw_embeddings[1:], dtype=np.float64)

        # ── cosine similarity ───────────────────────────────────────────
        query_norm: float = float(np.linalg.norm(query_vec))
        if query_norm == 0.0:
            # Degenerate zero-vector query → cannot rank meaningfully.
            console.print(
                "[yellow]Warning:[/yellow] query embedding is a zero vector – returning candidates with score 0.0"
            )
            logger.warning("Query embedding is a zero vector; cannot compute cosine similarity")
            return [(c, 0.0) for c in candidates[:top_n]]

        candidate_norms = np.linalg.norm(candidate_vecs, axis=1)
        # Guard against zero-norm candidates (replace 0 with 1 to avoid div-by-zero).
        safe_norms = np.where(candidate_norms == 0.0, 1.0, candidate_norms)

        similarities = candidate_vecs.dot(query_vec) / (safe_norms * query_norm)

        # ── rank & select top-N ─────────────────────────────────────────
        # argsort ascending, then reverse for descending order.
        ranked_indices = np.argsort(similarities)[::-1][:top_n]

        results: List[Tuple[str, float]] = [
            (candidates[int(idx)], float(similarities[int(idx)]))
            for idx in ranked_indices
        ]

        console.print(
            f"[green]embed_and_retrieve:[/green] returned {len(results)} of "
            f"{len(candidates)} candidates (model={model})"
        )
        logger.info(
            "embed_and_retrieve: returned %d of %d candidates (model=%s)",
            len(results),
            len(candidates),
            model,
        )

        return results

    except Exception as exc:  # noqa: BLE001 – intentional broad catch for graceful fallback
        console.print(
            f"[yellow]Warning:[/yellow] embedding call failed ({type(exc).__name__}: {exc}) "
            f"– returning all candidates with score 0.0"
        )
        logger.warning(
            "embed_and_retrieve: embedding call failed (%s: %s); falling back to score=0.0 for all candidates",
            type(exc).__name__,
            exc,
        )
        return [(c, 0.0) for c in candidates[:top_n]]