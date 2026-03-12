import os
import pathlib

def filepath_to_prompt_filename(filepath: str, language: str) -> str:
    """
    Computes the prompt filename from a given output filepath and language.
    The prompt filename mirrors the directory structure of the filepath.

    Args:
        filepath: The target output path (e.g., "app/api/route.ts").
        language: The programming language (e.g., "TypeScript").

    Returns:
        A string representing the prompt filename path with forward slashes.
    """
    path = pathlib.Path(filepath)
    
    # Extract directory, stem (filename without extension), and extension
    # Note: path.stem handles files like 'route.ts' -> 'route'
    directory = path.parent
    filename_stem = path.stem
    
    # Construct the new filename
    new_filename = f"{filename_stem}_{language}.prompt"
    
    # Join directory and new filename
    # If directory is '.', result is just the filename
    if directory == pathlib.Path('.'):
        result_path = new_filename
    else:
        result_path = directory / new_filename
        
    # Ensure forward slashes regardless of OS
    return str(result_path).replace(os.sep, '/')

# Examples/Tests:
if __name__ == "__main__":
    test_cases = [
        ("prisma/schema.prisma", "Prisma", "prisma/schema_Prisma.prompt"),
        ("lib/types.ts", "TypeScript", "lib/types_TypeScript.prompt"),
        ("lib/formulaEngine.ts", "TypeScript", "lib/formulaEngine_TypeScript.prompt"),
        ("app/api/sheets/route.ts", "TypeScript", "app/api/sheets/route_TypeScript.prompt"),
        ("app/api/sheets/[id]/route.ts", "TypeScript", "app/api/sheets/[id]/route_TypeScript.prompt"),
        ("components/grid/Cell.tsx", "TypeScriptReact", "components/grid/Cell_TypeScriptReact.prompt"),
        ("app/sheet/[id]/page.tsx", "TypeScriptReact", "app/sheet/[id]/page_TypeScriptReact.prompt"),
        ("schema.prisma", "Prisma", "schema_Prisma.prompt"),
        ("src/models/user.py", "Python", "src/models/user_Python.prompt"),
        ("app/layout.tsx", "TypeScriptReact", "app/layout_TypeScriptReact.prompt"),
    ]

    for fp, lang, expected in test_cases:
        actual = filepath_to_prompt_filename(fp, lang)
        assert actual == expected, f"Failed: {fp} -> {actual} (Expected: {expected})"
        print(f"Success: {fp} -> {actual}")