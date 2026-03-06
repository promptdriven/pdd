#!/usr/bin/env python3
"""
Generate architecture.json using the same PDD pipeline as `pdd generate` (Issue #617 proof).

This script simulates what happens when the LLM returns architecture JSON:
1. Start with "LLM-like" output (flat filenames, old behavior)
2. Run the real PDD normalizer (normalize_architecture_filenames)
3. Write architecture.json

So the file on disk is produced by the exact same code path as `pdd generate --template architecture/architecture_json`.

Run from repo root:
  python context/generate_architecture_json_proof.py

Output: architecture.json in the current directory with filename mirroring filepath.
"""
import json
import sys
from pathlib import Path

repo_root = Path(__file__).resolve().parent.parent
if str(repo_root) not in sys.path:
    sys.path.insert(0, str(repo_root))

from pdd.architecture_sync import normalize_architecture_filenames

# Simulated LLM output (flat filenames — what we'd get before Issue #617 fix)
MOCK_LLM_ARCHITECTURE = [
    {
        "reason": "Prisma schema for database",
        "description": "Schema definitions",
        "dependencies": [],
        "priority": 1,
        "filename": "prisma_schema_Prisma.prompt",
        "filepath": "prisma/schema.prisma",
        "tags": ["database"],
    },
    {
        "reason": "Shared types",
        "description": "TypeScript types",
        "dependencies": [],
        "priority": 2,
        "filename": "lib_types_TypeScript.prompt",
        "filepath": "lib/types.ts",
        "tags": ["shared"],
    },
    {
        "reason": "Sheets API route",
        "description": "API route handler",
        "dependencies": ["lib/types_TypeScript.prompt"],
        "priority": 3,
        "filename": "app_api_sheets_route_TypeScript.prompt",
        "filepath": "app/api/sheets/route.ts",
        "tags": ["api"],
    },
    {
        "reason": "Dynamic route",
        "description": "Route with [id]",
        "dependencies": [],
        "priority": 4,
        "filename": "app_api_sheets_id_route_TypeScript.prompt",
        "filepath": "app/api/sheets/[id]/route.ts",
        "tags": ["api"],
    },
    {
        "reason": "Grid cell component",
        "description": "React component",
        "dependencies": [],
        "priority": 5,
        "filename": "components_grid_Cell_TypeScriptReact.prompt",
        "filepath": "components/grid/Cell.tsx",
        "tags": ["frontend"],
    },
]


def main():
    cwd = Path.cwd()
    out_path = cwd / "architecture.json"

    # Same logic as code_generator_main: parse (we already have list), normalize, write
    arch_data = [dict(entry) for entry in MOCK_LLM_ARCHITECTURE]
    normalize_architecture_filenames(arch_data)

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(arch_data, f, indent=2, ensure_ascii=False)

    print(f"Written: {out_path.resolve()}")
    print("\nProof (filename should mirror filepath):")
    print("-" * 70)
    for m in arch_data:
        print(f"  filepath: {m['filepath']}")
        print(f"  filename: {m['filename']}")
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
