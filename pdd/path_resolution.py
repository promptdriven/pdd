from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
from typing import Literal, Optional

IncludeProfile = Literal["cwd_then_package_then_repo"]
PromptProfile = Literal["pdd_path_then_repo_then_cwd"]
DataProfile = Literal["pdd_path_only"]
ProjectRootProfile = Literal["pdd_path_then_marker_then_cwd"]


@dataclass(frozen=True)
class PathResolver:
    cwd: Path
    pdd_path_env: Optional[Path]
    package_root: Path
    repo_root: Optional[Path]

    def resolve_include(self, rel: str, profile: IncludeProfile = "cwd_then_package_then_repo") -> Path:
        if profile != "cwd_then_package_then_repo":
            raise ValueError(f"Unsupported include profile: {profile}")

        cwd_path = self.cwd / rel
        if cwd_path.exists():
            return cwd_path

        pkg_path = self.package_root / rel
        if pkg_path.exists():
            return pkg_path

        if self.repo_root is not None:
            repo_path = self.repo_root / rel
            if repo_path.exists():
                return repo_path

        return cwd_path

    def resolve_prompt_template(
        self,
        name: str,
        profile: PromptProfile = "pdd_path_then_repo_then_cwd",
    ) -> Optional[Path]:
        if profile != "pdd_path_then_repo_then_cwd":
            raise ValueError(f"Unsupported prompt profile: {profile}")

        roots = []
        if self.pdd_path_env is not None:
            roots.append(self.pdd_path_env)
        if self.repo_root is not None:
            roots.append(self.repo_root)
        roots.append(self.cwd)

        prompt_file = f"{name}.prompt"
        for root in roots:
            candidate = root / "prompts" / prompt_file
            if candidate.exists():
                return candidate
            candidate = root / "pdd" / "prompts" / prompt_file
            if candidate.exists():
                return candidate

        return None

    def resolve_data_file(self, rel: str, profile: DataProfile = "pdd_path_only") -> Path:
        if profile != "pdd_path_only":
            raise ValueError(f"Unsupported data profile: {profile}")
        if self.pdd_path_env is None:
            raise ValueError("PDD_PATH environment variable is not set.")
        return self.pdd_path_env / rel

    def resolve_project_root(
        self,
        profile: ProjectRootProfile = "pdd_path_then_marker_then_cwd",
        max_levels: int = 5,
    ) -> Path:
        if profile != "pdd_path_then_marker_then_cwd":
            raise ValueError(f"Unsupported project root profile: {profile}")

        if (
            self.pdd_path_env is not None
            and self.pdd_path_env.is_dir()
            and not _is_within(self.pdd_path_env, self.package_root)
        ):
            return self.pdd_path_env

        current = self.cwd
        for _ in range(max_levels):
            if _has_project_marker(current):
                return current
            parent = current.parent
            if parent == current:
                break
            current = parent

        return self.cwd


def get_default_resolver() -> PathResolver:
    cwd = Path.cwd().resolve()

    pdd_path_env = None
    env_value = os.getenv("PDD_PATH")
    if env_value:
        pdd_path_env = Path(env_value).expanduser().resolve()

    package_root = Path(__file__).resolve().parent
    repo_root = package_root.parent

    return PathResolver(
        cwd=cwd,
        pdd_path_env=pdd_path_env,
        package_root=package_root,
        repo_root=repo_root,
    )


def _has_project_marker(path: Path) -> bool:
    return (
        (path / ".git").exists()
        or (path / "pyproject.toml").exists()
        or (path / "data").is_dir()
        or (path / ".env").exists()
    )


def _is_within(path: Path, parent: Path) -> bool:
    try:
        resolved_path = path.resolve()
        resolved_parent = parent.resolve()
    except Exception:
        return False

    if resolved_path == resolved_parent:
        return True
    parent_str = str(resolved_parent)
    if not parent_str.endswith(os.sep):
        parent_str = parent_str + os.sep
    return str(resolved_path).startswith(parent_str)
