#!/usr/bin/env python3
"""
Issue #617 verification: see how normalize_architecture_filenames makes filename mirror filepath.

Run from repo root:
  python context/issue_617_verify_filename_mirrors_filepath.py

Or with PDD on path:
  python -m pdd.architecture_sync  # (this file is in context/, run the script directly)
"""
import json
import sys
from pathlib import Path

# Add repo root so we can import pdd
repo_root = Path(__file__).resolve().parent.parent
if str(repo_root) not in sys.path:
    sys.path.insert(0, str(repo_root))

from pdd.architecture_sync import normalize_architecture_filenames

def main():
    # Example: what the LLM might have produced (flat filenames)
    arch_before = [
        {"filepath": "prisma/schema.prisma", "filename": "prisma_schema_Prisma.prompt", "priority": 1},
        {"filepath": "lib/types.ts", "filename": "lib_types_TypeScript.prompt", "priority": 2},
        {"filepath": "app/api/sheets/route.ts", "filename": "app_api_sheets_route_TypeScript.prompt", "priority": 3},
        {"filepath": "app/sheet/[id]/page.tsx", "filename": "app_sheet_id_page_TypeScriptReact.prompt", "priority": 4},
    ]

    print("BEFORE (flat filenames — old behavior):")
    print("-" * 60)
    for m in arch_before:
        print(f"  filepath: {m['filepath']!r}")
        print(f"  filename: {m['filename']!r}")
        print()

    arch_after = [dict(m) for m in arch_before]
    normalize_architecture_filenames(arch_after)

    print("AFTER (filename mirrors filepath — Issue #617 fix):")
    print("-" * 60)
    for m in arch_after:
        print(f"  filepath: {m['filepath']!r}")
        print(f"  filename: {m['filename']!r}")
        print()

    print("Quick check: filename should have same path structure as filepath")
    print("  (e.g. app/api/sheets/route.ts -> app/api/sheets/route_TypeScript.prompt)")
    return 0

if __name__ == "__main__":
    sys.exit(main())
