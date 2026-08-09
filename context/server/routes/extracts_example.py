"""
Example usage of the extracts router module (pdd/server/routes/extracts.py).

Demonstrates how to mount the extracts router in a FastAPI application,
configure the project root dependency, and interact with all three endpoints:
  - GET /api/v1/extracts        (list all cached extracts)
  - GET /api/v1/extracts/{key}  (get single extract with content)
  - GET /api/v1/extracts/for-prompt (list extracts for a prompt file)
"""

import asyncio
import json
import hashlib
import os
import tempfile
from pathlib import Path

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from fastapi import FastAPI
from httpx import AsyncClient, ASGITransport

from pdd.server.routes.extracts import router as extracts_router, set_project_root


def _compute_cache_key(source_path: str, query: str) -> str:
    """Mirror the cache key formula: sha256(normpath(path) + '\\n' + query)."""
    normalized = os.path.normpath(source_path)
    return hashlib.sha256((normalized + "\n" + query).encode("utf-8")).hexdigest()


async def setup_test_environment(project_root: Path) -> str:
    """
    Create a mock project environment with a source file, prompt file,
    and cached extracts to exercise every endpoint.

    Returns the cache key of the created extract.
    """
    extracts_dir = project_root / ".pdd" / "extracts"
    extracts_dir.mkdir(parents=True, exist_ok=True)

    # --- Requirement 2/3: source file for freshness checking ---
    source_file = project_root / "src" / "main.py"
    source_file.parent.mkdir(parents=True, exist_ok=True)
    source_content = "def hello():\n    print('world')\n"
    source_file.write_text(source_content)
    source_hash = hashlib.sha256(source_content.encode()).hexdigest()

    # --- Requirement 7: cache key via sha256(normpath(path) + '\n' + query) ---
    source_path_str = "src/main.py"
    query = "List all functions"
    cache_key = _compute_cache_key(source_path_str, query)

    # --- Cache layout: {key}.md and {key}.meta.json ---
    md_path = extracts_dir / f"{cache_key}.md"
    md_path.write_text("```python\ndef hello():\n    print('world')\n```")

    meta_path = extracts_dir / f"{cache_key}.meta.json"
    meta_data = {
        "source_path": source_path_str,
        "query": query,
        "timestamp": "2024-06-15T10:30:00Z",
        "source_hash": source_hash,
        "token_count": 15,
    }
    meta_path.write_text(json.dumps(meta_data))

    # --- Requirement 5/8: prompt with <include query="...">file</include> tags ---
    prompt_file = project_root / "prompts" / "review.prompt"
    prompt_file.parent.mkdir(parents=True, exist_ok=True)
    prompt_content = (
        'Review this code:\n'
        '<include query="List all functions">../src/main.py</include>\n'
    )
    prompt_file.write_text(prompt_content)

    return cache_key


async def run_example() -> None:
    """Run the example demonstrating all three extracts router endpoints."""
    with tempfile.TemporaryDirectory() as temp_dir:
        project_root = Path(temp_dir)

        # --- Requirement 6: configure project root via getter/setter pattern ---
        set_project_root(project_root)

        cache_key = await setup_test_environment(project_root)
        print(f"Project root: {project_root}")
        print(f"Cache key:    {cache_key}\n")

        app = FastAPI(title="Extracts API Example")
        app.include_router(extracts_router)

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://testserver"
        ) as client:

            # --- Requirement 2: GET / lists all cached extracts ---
            print("=== GET /api/v1/extracts (list all) ===")
            resp = await client.get("/api/v1/extracts")
            print(f"Status: {resp.status_code}")
            data = resp.json()
            print(f"Total: {data['total']}, Stale: {data['stale_count']}")
            for ext in data["extracts"]:
                print(f"  - {ext['source_path']} | fresh={ext['is_fresh']}")
            print()

            # --- Requirement 3: check_freshness=false returns is_fresh=null ---
            print("=== GET /api/v1/extracts?check_freshness=false ===")
            resp = await client.get("/api/v1/extracts", params={"check_freshness": "false"})
            data = resp.json()
            for ext in data["extracts"]:
                print(f"  - {ext['source_path']} | fresh={ext['is_fresh']}")
            print()

            # --- Requirement 4: GET /{cache_key} returns full content ---
            print(f"=== GET /api/v1/extracts/{{cache_key}} ===")
            resp = await client.get(f"/api/v1/extracts/{cache_key}")
            print(f"Status: {resp.status_code}")
            detail = resp.json()
            print(f"Source: {detail['source_path']}, Fresh: {detail['is_fresh']}")
            print(f"Content preview: {detail['content'][:60]}...")
            print()

            # --- Requirement 4: invalid cache key returns 404 ---
            print("=== GET /api/v1/extracts/invalid-key (expect 404) ===")
            resp = await client.get("/api/v1/extracts/not-a-hex-key")
            print(f"Status: {resp.status_code} - {resp.json()['detail']}")
            print()

            # --- Requirement 5: GET /for-prompt lists extracts for a prompt ---
            print("=== GET /api/v1/extracts/for-prompt ===")
            resp = await client.get(
                "/api/v1/extracts/for-prompt",
                params={"prompt_path": "prompts/review.prompt"},
            )
            print(f"Status: {resp.status_code}")
            for info in resp.json():
                print(
                    f"  - include={info['include_path']}, "
                    f"query={info['query']}, "
                    f"cached={info['has_cached_entry']}, "
                    f"fresh={info['is_fresh']}"
                )
            print()

            # --- Requirement 5: missing prompt returns 404 ---
            print("=== GET /api/v1/extracts/for-prompt (missing prompt, expect 404) ===")
            resp = await client.get(
                "/api/v1/extracts/for-prompt",
                params={"prompt_path": "nonexistent.prompt"},
            )
            print(f"Status: {resp.status_code} - {resp.json()['detail']}")

        set_project_root(None)


if __name__ == "__main__":
    asyncio.run(run_example())
