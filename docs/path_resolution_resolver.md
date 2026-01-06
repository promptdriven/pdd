# Path Resolution Resolver (Minimal Interface + Test Matrix)

## Goal

Create a single, reusable path resolver that captures current behavior for:
- include resolution (preprocess)
- prompt template loading
- project root selection
- strict PDD_PATH data file lookup

This is a refactor draft. The only intended behavior change vs current code
is the repo_root fallback for includes (Issue #240); project-root handling
already follows existing prompt intent to ignore package-root PDD_PATH.

## Non-goals

- Do not change precedence order for any caller.
- Do not change output path resolution (construct_paths/generate_output_paths).

## Target Behavior Profiles (Explicit)

These are the behaviors the resolver must implement (includes the Issue #240
repo_root fallback for includes).

### Include Resolution (preprocess)
Target behavior for `pdd/pdd/preprocess.py:get_file_path`
Order:
1) CWD (`./<rel>`)
2) package dir (`<package_root>/<rel>`)
3) repo root (`<repo_root>/<rel>`)
4) return CWD path (caller raises FileNotFound later)

### Prompt Template Resolution
Target behavior for `pdd/pdd/load_prompt_template.py:load_prompt_template`
Order:
1) `PDD_PATH` root
2) repo root (parent of package root)
3) CWD
Candidate subpaths per root (in order):
- `<root>/prompts/<name>.prompt`
- `<root>/pdd/prompts/<name>.prompt`

### Project Root Resolution
Target behavior for `pdd/pdd/llm_invoke.py` project root selection
Order:
1) `PDD_PATH` if valid dir and not inside package root
2) marker search from CWD (up to 5 levels): `.git`, `pyproject.toml`, `data/`, `.env`
3) CWD

### Data File Resolution (Strict)
Target behavior for `pdd/pdd/get_extension.py`, `pdd/pdd/get_language.py`,
`pdd/pdd/get_run_command.py`, `pdd/pdd/get_comment.py`
Order:
1) `PDD_PATH` only (error if missing)

## Proposed Minimal API

```python
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Literal

IncludeProfile = Literal["cwd_then_package_then_repo"]
PromptProfile = Literal["pdd_path_then_repo_then_cwd"]
DataProfile = Literal["pdd_path_only"]
ProjectRootProfile = Literal["pdd_path_then_marker_then_cwd"]

@dataclass(frozen=True)
class PathResolver:
    cwd: Path
    pdd_path_env: Optional[Path]
    package_root: Path      # .../pdd/pdd
    repo_root: Optional[Path]  # parent of package_root if present

    def resolve_include(self, rel: str, profile: IncludeProfile = "cwd_then_package_then_repo") -> Path: ...
    def resolve_prompt_template(self, name: str, profile: PromptProfile = "pdd_path_then_repo_then_cwd") -> Optional[Path]: ...
    def resolve_data_file(self, rel: str, profile: DataProfile = "pdd_path_only") -> Path: ...
    def resolve_project_root(self, profile: ProjectRootProfile = "pdd_path_then_marker_then_cwd") -> Path: ...
```

## Integration Map

Hook each caller to the resolver with the profile shown:

- `pdd/pdd/preprocess.py:get_file_path` -> `resolve_include("cwd_then_package_then_repo")`
- `pdd/pdd/load_prompt_template.py` -> `resolve_prompt_template("pdd_path_then_repo_then_cwd")`
- `pdd/pdd/llm_invoke.py` project root selection -> `resolve_project_root("pdd_path_then_marker_then_cwd")`
- `pdd/pdd/get_extension.py` and peers -> `resolve_data_file("pdd_path_only")`

## Test Matrix (Minimum)

This table documents expected results for a minimal resolver test suite.

| ID | Profile | Inputs | Expected |
| --- | --- | --- | --- |
| INC-01 | include | file exists in CWD only | resolves to CWD path |
| INC-02 | include | missing in CWD, exists in package | resolves to package path |
| INC-03 | include | missing in CWD/package, exists in repo_root | resolves to repo_root path |
| INC-04 | include | missing in all | returns CWD path (caller fails later) |
| PRM-01 | prompt | PDD_PATH set, prompts file in PDD_PATH/prompts | resolves to that file |
| PRM-02 | prompt | PDD_PATH set, prompts file in PDD_PATH/pdd/prompts | resolves to that file |
| PRM-03 | prompt | PDD_PATH unset, prompts file in repo_root/prompts | resolves to repo_root file |
| PRM-04 | prompt | no PDD_PATH/repo_root match, prompts file in CWD/prompts | resolves to CWD file |
| PROJ-01 | project root | PDD_PATH valid and not in package | resolves to PDD_PATH |
| PROJ-02 | project root | PDD_PATH invalid, CWD marker present | resolves to marker dir |
| PROJ-03 | project root | no markers | resolves to CWD |
| PROJ-04 | project root | PDD_PATH points to package root | resolves to marker dir or CWD |
| DATA-01 | data | PDD_PATH set, file exists | resolves to PDD_PATH file |
| DATA-02 | data | PDD_PATH missing | raises error (strict behavior) |
