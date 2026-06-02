from __future__ import annotations

import ast
import contextlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

from .architecture_sync import sync_all_prompts_to_architecture
from .checkup_gates import discover_gates, run_gates
from .ci_drift_heal import (
    _build_ci_env,
    _parse_cost_from_csv,
    detect_drift,
    heal_module,
)
from .metadata_sync import run_metadata_sync
from .operation_log import infer_module_identity


_CODE_EXTENSIONS = {
    ".c",
    ".cc",
    ".cpp",
    ".cs",
    ".go",
    ".h",
    ".hpp",
    ".java",
    ".js",
    ".jsx",
    ".kt",
    ".kts",
    ".mjs",
    ".py",
    ".pyi",
    ".rb",
    ".rs",
    ".sh",
    ".swift",
    ".ts",
    ".tsx",
}
_DOC_EXTENSIONS = {".md", ".mdx", ".rst", ".txt", ".adoc"}
_SECRET_RE = re.compile(
    r"(gh[pousr]_[A-Za-z0-9_]{20,}|sk-[A-Za-z0-9_-]{20,}|"
    r"xox[baprs]-[A-Za-z0-9-]{20,}|[A-Za-z0-9_]*TOKEN[A-Za-z0-9_]*=[^\s]+)",
    re.IGNORECASE,
)
_QUARANTINE_ENV = "PDD_PRE_CHECKUP_QUARANTINE"
# Upper bound on the caller-compatibility repo walk so the sweep stays
# predictable on very large trees. The cheap substring pre-filter keeps the
# expensive AST parse off all but a handful of files; this caps the walk
# itself. Truncation is surfaced as a note (never silently dropped).
_MAX_CALLER_SCAN_FILES = 20000


@dataclass
class _CheckOutcome:
    ok: bool
    messages: List[str]
    cost: float = 0.0


@contextlib.contextmanager
def _pushd(path: Path) -> Iterable[None]:
    old = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(old)


def _norm(path: str) -> str:
    # NB: ``.removeprefix("./")`` not ``.lstrip("./")`` — lstrip strips a
    # CHARACTER SET, so it would eat leading dots from real names
    # (``.npmrc`` -> ``npmrc``, ``.github/...`` -> ``github/...``). That silently
    # defeats the package-manager-config RCE skip-guard in checkup_gates (which
    # matches the ``.npmrc`` basename) and the docs-only ``.github/`` short
    # circuit. removeprefix strips only a literal leading ``./``.
    return str(path).replace("\\", "/").strip().removeprefix("./")


def _scrub(text: Any) -> str:
    value = "" if text is None else str(text)
    # Compose the loop's vetted secret-scrubber (broad: AWS/Google/Bearer/
    # Authorization/URL-creds/PEM) with the local regex (catches bare
    # ``token=``/``secret=`` forms the vetted one may miss). Lazy import avoids
    # a load-time cycle; fall back to the local regex if it is unavailable.
    try:
        from .checkup_review_loop import _scrub_secrets

        value = _scrub_secrets(value)
    except Exception:
        pass
    return _SECRET_RE.sub("[REDACTED]", value)


def _excerpt(text: str, limit: int = 1600) -> str:
    text = _scrub(text)
    if len(text) <= limit:
        return text
    return text[:limit] + "...[truncated]"


def _strict_enabled(strict: Optional[bool]) -> bool:
    if strict is not None:
        return bool(strict)
    return os.environ.get("PDD_STRICT_DOC_SYNC", "").strip().lower() in {
        "1",
        "true",
        "yes",
    }


def _changed_code_files(changed_files: Sequence[str]) -> List[str]:
    out: List[str] = []
    for raw in changed_files:
        rel = _norm(raw)
        if not rel:
            continue
        if Path(rel).suffix.lower() in _CODE_EXTENSIONS:
            out.append(rel)
    return sorted(set(out))


def _docs_only(changed_files: Sequence[str]) -> bool:
    normalized = [_norm(p) for p in changed_files if _norm(p)]
    if not normalized:
        return True
    if any(Path(p).suffix.lower() in _CODE_EXTENSIONS for p in normalized):
        return False
    return all(
        Path(p).suffix.lower() in _DOC_EXTENSIONS
        or p.startswith(("docs/", "doc/", ".github/"))
        for p in normalized
    )


def _load_architecture(worktree: Path) -> List[Dict[str, Any]]:
    path = worktree / "architecture.json"
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return []
    if isinstance(data, dict):
        modules = data.get("modules", [])
        return modules if isinstance(modules, list) else []
    return data if isinstance(data, list) else []


def _prompt_path_for_filename(worktree: Path, filename: str) -> Optional[Path]:
    for base in (worktree / "pdd" / "prompts", worktree / "prompts"):
        candidate = base / filename
        if candidate.exists():
            return candidate
    matches = list(worktree.glob(f"**/prompts/{filename}"))
    return matches[0] if matches else None


def _prompt_filename_from_changed(rel: str) -> Optional[str]:
    marker = "/prompts/"
    if rel.startswith("prompts/"):
        return rel[len("prompts/") :]
    if marker in rel:
        return rel.split(marker, 1)[1]
    return None


def _architecture_entry_maps_file(entry: Dict[str, Any], rel: str) -> bool:
    filepath = _norm(entry.get("filepath", ""))
    filename = _norm(entry.get("filename", ""))
    return rel in {filepath, f"pdd/prompts/{filename}", f"prompts/{filename}"}


def _touched_prompt_files(
    worktree: Path,
    changed_files: Sequence[str],
    architecture: Sequence[Dict[str, Any]],
) -> Dict[str, Tuple[Path, Optional[Path]]]:
    touched: Dict[str, Tuple[Path, Optional[Path]]] = {}
    for raw in changed_files:
        rel = _norm(raw)
        prompt_filename = _prompt_filename_from_changed(rel)
        if prompt_filename:
            prompt_path = _prompt_path_for_filename(worktree, prompt_filename)
            if prompt_path is not None:
                code_path: Optional[Path] = None
                for entry in architecture:
                    if _norm(entry.get("filename", "")) == prompt_filename:
                        filepath = entry.get("filepath")
                        if isinstance(filepath, str) and filepath:
                            code_path = worktree / filepath
                        break
                touched[prompt_filename] = (prompt_path, code_path)
            continue
        for entry in architecture:
            if _architecture_entry_maps_file(entry, rel):
                filename = entry.get("filename")
                if not isinstance(filename, str) or not filename.endswith(".prompt"):
                    continue
                prompt_path = _prompt_path_for_filename(worktree, filename)
                if prompt_path is None:
                    continue
                filepath = entry.get("filepath")
                code_path = worktree / filepath if isinstance(filepath, str) and filepath else None
                touched[filename] = (prompt_path, code_path)
    return touched


def _module_names_from_prompts(prompt_pairs: Dict[str, Tuple[Path, Optional[Path]]]) -> List[str]:
    modules: Set[str] = set()
    for _filename, (prompt_path, _code_path) in prompt_pairs.items():
        try:
            basename, _language = infer_module_identity(str(prompt_path))
        except Exception:
            basename = None
        if basename:
            modules.add(basename)
    return sorted(modules)


def _run_drift_sync(
    worktree: Path,
    changed_files: Sequence[str],
    *,
    base_ref: Optional[str],
    strict: bool,
) -> _CheckOutcome:
    architecture = _load_architecture(worktree)
    prompt_pairs = _touched_prompt_files(worktree, changed_files, architecture)
    only_files = set(prompt_pairs.keys())
    messages: List[str] = []
    failures: List[str] = []
    warnings: List[str] = []
    cost = 0.0

    if only_files:
        try:
            result = sync_all_prompts_to_architecture(
                prompts_dir=worktree / "pdd" / "prompts",
                architecture_path=worktree / "architecture.json",
                dry_run=False,
                only_files=only_files,
            )
            if not result.get("success", False):
                errors = "; ".join(result.get("errors", []) or ["unknown architecture sync error"])
                target = failures if strict else warnings
                target.append(f"architecture-sync failed for {sorted(only_files)}: {errors}")
        except Exception as exc:
            target = failures if strict else warnings
            target.append(f"architecture-sync raised for {sorted(only_files)}: {_scrub(exc)}")

    for filename, (prompt_path, code_path) in prompt_pairs.items():
        try:
            result = run_metadata_sync(
                prompt_path,
                code_path if code_path and code_path.exists() else None,
                repo_root=worktree,
                architecture_path=worktree / "architecture.json",
            )
            if not getattr(result, "ok", False):
                stage = getattr(result, "failing_stage", None) or "unknown"
                failures.append(f"metadata-sync failed for {filename}: stage={stage}")
        except Exception as exc:
            failures.append(f"metadata-sync raised for {filename}: {_scrub(exc)}")

    modules = _module_names_from_prompts(prompt_pairs)
    if modules:
        with tempfile.NamedTemporaryFile(prefix="pdd-pre-checkup-cost-", suffix=".csv", delete=True) as cost_file:
            env = _build_ci_env(cost_file.name)
            env.setdefault("PDD_FORCE_LOCAL", "1")
            parsed_cost = 0.0
            with _pushd(worktree):
                try:
                    prompt_drifts, example_drifts = detect_drift(
                        modules=list(modules),
                        diff_base=base_ref,
                    )
                except Exception as exc:
                    failures.append(f"detect-drift raised for {modules}: {_scrub(exc)}")
                    prompt_drifts, example_drifts = [], []

                for drift in prompt_drifts:
                    try:
                        healed = heal_module(drift, env)
                    except Exception as exc:
                        healed = False
                        failures.append(f"heal-module raised for {drift.basename}: {_scrub(exc)}")
                    current_cost = _parse_cost_from_csv(cost_file.name)
                    cost += max(0.0, current_cost - parsed_cost)
                    parsed_cost = current_cost
                    if healed is False:
                        failures.append(
                            f"heal-module failed for {drift.basename}: "
                            f"{_scrub(getattr(drift, 'reason', 'drift detected'))}"
                        )
                    elif healed is None:
                        warnings.append(f"heal-module skipped {drift.basename}")

                try:
                    remaining_updates, remaining_other = detect_drift(
                        modules=list(modules),
                        diff_base=base_ref,
                    )
                except Exception as exc:
                    failures.append(f"post-heal detect-drift raised for {modules}: {_scrub(exc)}")
                    remaining_updates, remaining_other = [], []

            if remaining_updates:
                failures.extend(
                    f"residual update drift after heal: {d.basename} ({_scrub(d.reason)})"
                    for d in remaining_updates
                )
            residual_other = [*example_drifts, *remaining_other]
            if residual_other:
                residual = "; ".join(
                    f"{d.basename}:{d.operation}" for d in residual_other
                )
                (failures if strict else warnings).append(
                    f"residual non-update drift: {residual}"
                )
    elif only_files:
        warnings.append("no module names resolved for touched prompt files")

    if warnings:
        messages.append("phase=drift-sync warnings: " + " | ".join(warnings))
    if failures:
        messages.append("phase=drift-sync failures: " + " | ".join(failures))
    if not messages:
        messages.append("phase=drift-sync passed")
    return _CheckOutcome(ok=not failures, messages=messages, cost=cost)


def _module_name_for_python_path(path: Path, worktree: Path) -> Optional[str]:
    try:
        rel = path.resolve().relative_to(worktree.resolve())
    except ValueError:
        return None
    if rel.suffix != ".py" or rel.name == "__init__.py":
        return None
    parts = list(rel.with_suffix("").parts)
    if not parts:
        return None
    if parts[0] == "tests":
        return None
    if parts[0] == "pdd":
        return ".".join(parts)
    current = worktree
    package_parts: List[str] = []
    for part in parts[:-1]:
        current = current / part
        if not (current / "__init__.py").exists():
            return None
        package_parts.append(part)
    package_parts.append(parts[-1])
    return ".".join(package_parts)


def _run_command(
    cmd: Sequence[str],
    *,
    worktree: Path,
    timeout: float,
    env: Optional[Dict[str, str]] = None,
    success_codes: Sequence[int] = (0,),
) -> Tuple[bool, str]:
    try:
        result = subprocess.run(
            list(cmd),
            cwd=worktree,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout.decode(errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode(errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return False, f"timeout after {timeout}s: {_excerpt(stdout + stderr)}"
    except Exception as exc:
        return False, _scrub(exc)
    output = "\n".join(part for part in (result.stdout, result.stderr) if part)
    return result.returncode in success_codes, _excerpt(output)


# Precise provider/cloud/VCS prefixes + the canonical secret-key SUFFIXES —
# NOT a broad ``KEY|TOKEN|SECRET`` substring match. This gate hard-blocks, so an
# over-broad scrub that strips a var a target repo's unit test legitimately
# reads (e.g. ``DJANGO_SECRET_KEY``) would false-block it — the exact
# false-positive class the caller-compat sweep was hardened against. Since the
# env scrub is defence-in-depth on the workflow's own worktree (not untrusted
# fork code), precision matters more than catching every conceivable secret.
_SECRET_ENV_PREFIXES = (
    "AWS_", "GOOGLE_", "GCP_", "AZURE_", "ANTHROPIC", "OPENAI", "GEMINI",
    "MISTRAL", "COHERE", "GROQ", "DEEPSEEK", "OPENROUTER", "HUGGINGFACE", "HF_",
    "GH_", "GITHUB_",
)
_SECRET_ENV_SUFFIX_RE = re.compile(r"_(API_KEY|ACCESS_KEY|SECRET_ACCESS_KEY)$", re.IGNORECASE)


def _is_secret_env_key(key: str) -> bool:
    return key.startswith(_SECRET_ENV_PREFIXES) or bool(_SECRET_ENV_SUFFIX_RE.search(key))


def _python_import_env(worktree: Path) -> Dict[str, str]:
    """Hardened subprocess env for the gate's OWN Python subprocesses (import /
    route / existence probe / targeted tests).

    The gate executes worktree code (imports modules, runs pytest), so as
    defence in depth it MUST NOT hand that code the parent's live credentials:
    drop secret-bearing vars (LLM/cloud/VCS keys + tokens) and sanitize PATH
    (drop ``.``/relative/worktree-resolving entries via checkup_gates'
    ``_sanitized_path`` so a PR-shipped shim cannot become a tool). It KEEPS the
    controlled ``PYTHONPATH=worktree`` the import + existence probes need (the
    checkup_gates env builder strips PYTHONPATH, which would silently break
    them) and non-secret vars like ``PDD_PATH`` (PDD unit tests resolve data
    from it and mock LLM calls, so removing API keys does not break them)."""
    env = {k: v for k, v in os.environ.items() if not _is_secret_env_key(k)}
    try:
        from .checkup_gates import _sanitized_path

        sanitized = _sanitized_path(worktree)
        if sanitized:
            env["PATH"] = sanitized
    except Exception:
        pass
    env["PYTHONPATH"] = str(worktree)
    env.setdefault("NO_COLOR", "1")
    env.setdefault("CI", "1")
    return env


def _check_python_imports(
    worktree: Path,
    code_files: Sequence[str],
    *,
    timeout: float,
) -> List[str]:
    failures: List[str] = []
    env = _python_import_env(worktree)
    for rel in code_files:
        path = worktree / rel
        module = _module_name_for_python_path(path, worktree)
        if not module:
            continue
        ok, output = _run_command(
            [
                sys.executable,
                "-c",
                "import importlib, sys; importlib.import_module(sys.argv[1])",
                module,
            ],
            worktree=worktree,
            timeout=timeout,
            env=env,
        )
        if not ok:
            failures.append(f"import-check failed for {rel} ({module}): {output}")
    return failures


def _route_like_source(text: str) -> bool:
    """True only if the source ACTUALLY constructs a web router/app or declares
    a route, detected via the AST (real ``Call`` / decorator nodes) rather than
    a raw substring scan. A substring match (``"APIRouter(" in text``) also
    fires when a file merely *mentions* these names in a string or comment —
    including this module's own token list — which made the route-probe
    hard-block any PR that touches such a file. The AST sees those mentions as
    ``ast.Constant`` strings, not calls, so they no longer false-trigger.
    """
    try:
        tree = ast.parse(text)
    except (SyntaxError, ValueError):
        return False
    constructors = {"APIRouter", "FastAPI", "Blueprint"}
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            func = node.func
            cname = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
            if cname in constructors:
                return True
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for dec in node.decorator_list:
                target = dec.func if isinstance(dec, ast.Call) else dec
                if isinstance(target, ast.Attribute) and target.attr == "route":
                    return True
    return False


def _check_route_probe(
    worktree: Path,
    code_files: Sequence[str],
    *,
    timeout: float,
) -> List[str]:
    """Best-effort app-wiring smoke check, returned as NON-BLOCKING notes.

    It imports each changed route-like module and counts route/router objects.
    It is intentionally NOT a hard block: it does not actually catch the
    "router never mounted" critical (a populated-but-unmounted router imports
    fine and counts > 0, so it passes), and it false-positives on valid route
    modules it cannot introspect — Flask apps/blueprints (no ``.routes``),
    factory-built routers, re-exported routers, custom ``@x.route`` classes.
    Since the gate hard-blocks arbitrary PRs, a heuristic with that false-
    positive profile is surfaced to checkup as a note rather than failing the
    gate. Genuine import errors are still hard-blocked by the import check.
    """
    notes: List[str] = []
    env = _python_import_env(worktree)
    probe = (
        "import importlib, sys\n"
        "m = importlib.import_module(sys.argv[1])\n"
        "count = 0\n"
        "for obj in vars(m).values():\n"
        "    routes = getattr(obj, 'routes', None)\n"
        "    if routes is not None:\n"
        "        try: count += len(routes)\n"
        "        except TypeError: pass\n"
        "print(count)\n"
        "raise SystemExit(0 if count > 0 else 2)\n"
    )
    for rel in code_files:
        path = worktree / rel
        if path.suffix != ".py" or not path.exists():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if not _route_like_source(text):
            continue
        module = _module_name_for_python_path(path, worktree)
        if not module:
            continue
        ok, output = _run_command(
            [sys.executable, "-c", probe, module],
            worktree=worktree,
            timeout=timeout,
            env=env,
        )
        if not ok:
            notes.append(
                f"route-probe note for {rel}: module imported but no route/router "
                f"object with registered routes was found (non-blocking best-effort "
                f"app-wiring smoke check; full mount verification stays with "
                f"checkup); {output}"
            )
    return notes


@dataclass
class _FunctionSig:
    min_positional: int
    max_positional: Optional[int]
    keywords: Set[str]
    accepts_kwargs: bool


def _public_function_sigs(path: Path) -> Dict[str, _FunctionSig]:
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"))
    except (OSError, SyntaxError, UnicodeDecodeError):
        return {}
    sigs: Dict[str, _FunctionSig] = {}
    for node in tree.body:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name.startswith("_"):
            continue
        args = node.args
        positional = list(args.posonlyargs) + list(args.args)
        if positional and positional[0].arg in {"self", "cls"}:
            positional = positional[1:]
        required = len(positional) - len(args.defaults)
        keywords = {arg.arg for arg in positional + list(args.kwonlyargs)}
        required += sum(1 for default in args.kw_defaults if default is None)
        sigs[node.name] = _FunctionSig(
            min_positional=max(required, 0),
            max_positional=None if args.vararg else len(positional),
            keywords=keywords,
            accepts_kwargs=args.kwarg is not None,
        )
    return sigs


def _iter_python_files(worktree: Path) -> Iterable[Path]:
    ignored_parts = {".git", ".pdd", "__pycache__", ".tox", ".venv", "venv", "node_modules"}
    for path in worktree.rglob("*.py"):
        if ignored_parts.intersection(path.relative_to(worktree).parts):
            continue
        yield path


def _runtime_missing_symbols(
    worktree: Path,
    module: str,
    names: Sequence[str],
    *,
    timeout: float,
) -> Optional[Set[str]]:
    """Return the subset of ``names`` not importable from ``module``.

    Existence is decided by the interpreter's *actual* export set — import the
    module in a subprocess and test attribute presence (``hasattr``) — rather
    than reconstructing exports from the AST. That makes the check honor
    star-imports, conditional/``try``-guarded definitions, module-level
    ``__getattr__`` (PEP 562), ``__all__`` re-exports, and imported-then-
    re-exported names, none of which an AST scan of top-level ``def``\\ s would
    see. Because this check hard-blocks the PR, that precision matters.

    Returns ``None`` when the module cannot be imported: that breakage is
    already reported by the import check, and a failed import must not be
    mistaken for "every symbol is missing".
    """
    wanted = sorted({n for n in names if n and n != "*"})
    if not wanted:
        return set()
    # Redirect import-time stdout/stderr into a discarded buffer so a chatty
    # module (banners, warnings) can't push the JSON result past
    # ``_run_command``'s output truncation. An import error still propagates
    # after the buffer is restored, so the subprocess exits non-zero -> None.
    probe = (
        "import importlib, sys, json, io, contextlib\n"
        "buf = io.StringIO()\n"
        "with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):\n"
        "    m = importlib.import_module(sys.argv[1])\n"
        "wanted = json.loads(sys.argv[2])\n"
        "missing = [n for n in wanted if not hasattr(m, n)]\n"
        "sys.stdout.write(json.dumps(missing))\n"
    )
    ok, output = _run_command(
        [sys.executable, "-c", probe, module, json.dumps(wanted)],
        worktree=worktree,
        timeout=timeout,
        env=_python_import_env(worktree),
    )
    if not ok:
        return None
    for line in reversed(output.splitlines()):
        stripped = line.strip()
        if not stripped:
            continue
        try:
            return set(json.loads(stripped))
        except ValueError:
            return None
    return set()


def _attr_call_chain(func: ast.Attribute) -> Optional[List[str]]:
    """Flatten a pure ``Name.attr[.attr...]`` access into its dotted parts.

    ``api.build`` -> ``["api", "build"]``; ``pkg.api.build`` ->
    ``["pkg", "api", "build"]``. Returns ``None`` when the root is not a plain
    ``Name`` (e.g. ``get_client().build`` or ``self.x``), so only statically
    resolvable module.attr calls are considered.
    """
    parts: List[str] = []
    cur: ast.expr = func
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if isinstance(cur, ast.Name):
        parts.append(cur.id)
        parts.reverse()
        return parts
    return None


def _rebound_names(tree: ast.Module) -> Set[str]:
    """Names bound by NON-import means anywhere in the file (function/lambda
    params, assignment/for/with/except/comprehension targets, walrus).

    Used as a shadowing guard for alias-style call resolution: ``ast.walk``
    ignores scope, so ``import pkg.api as api`` plus an unrelated
    ``def f(api): api.foo()`` would otherwise be misattributed to the module.

    This is intentionally FILE-scoped, not scope-aware: if an alias root is
    rebound anywhere in the file we skip ALL of its attribute calls — even a
    module-level ``api.build(...)`` that the unrelated ``def f(api)`` does not
    actually shadow. That accepts a false negative (the cross-model checkup
    still reviews the call) in exchange for a guard that is robust by
    construction. A scope-aware resolver would catch that module-level case but
    is a heuristic that could itself false-positive on global/nonlocal/
    class-scope edge cases — and this check HARD-BLOCKS arbitrary external PRs,
    where a wrongful block is strictly worse than a missed catch checkup will
    still find.
    """
    bound: Set[str] = set()

    def add_target(target: ast.AST) -> None:
        if isinstance(target, ast.Name):
            bound.add(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                add_target(elt)
        elif isinstance(target, ast.Starred):
            add_target(target.value)

    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            args = node.args
            for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs):
                bound.add(arg.arg)
            if args.vararg:
                bound.add(args.vararg.arg)
            if args.kwarg:
                bound.add(args.kwarg.arg)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                add_target(target)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            add_target(node.target)
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            add_target(node.target)
        elif isinstance(node, ast.NamedExpr):
            add_target(node.target)
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars is not None:
                    add_target(item.optional_vars)
        elif isinstance(node, ast.ExceptHandler):
            if node.name:
                bound.add(node.name)
        elif isinstance(node, ast.comprehension):
            add_target(node.target)
    return bound


def _resolve_from_import_module(
    rel_caller: str, module: Optional[str], level: int
) -> Optional[str]:
    """Resolve the absolute dotted module a ``from ... import`` targets, including
    RELATIVE imports (``from .api import x`` / ``from ..pkg import y``).

    Relative imports are the normal internal-import style in much of this repo, so
    an absolute-only match (``node.module in module_to_sigs``) was blind to them
    and silently missed every relative caller of a changed module. The resolved
    name is matched against ``module_to_sigs`` keys, which come from
    ``_module_name_for_python_path`` (path-based dotted names) — so resolving the
    relative level against the caller's path-derived package mirrors that naming.

    Returns ``None`` when the relative level escapes the caller's package (an
    invalid import) so the caller falls through to "no finding"; never raises.
    """
    if not level:
        return module
    try:
        pkg_parts = list(Path(rel_caller).parent.parts)
    except (TypeError, ValueError):
        return None
    drop = level - 1
    if drop > len(pkg_parts):
        return None
    base = pkg_parts[: len(pkg_parts) - drop] if drop else pkg_parts
    parts = [*base, module] if module else list(base)
    return ".".join(parts) if parts else None


def _check_caller_compatibility(
    worktree: Path,
    code_files: Sequence[str],
    *,
    timeout: float = 60.0,
) -> Tuple[List[str], List[str]]:
    """Flag repo callers that import a symbol the changed module no longer
    exports, or call a changed public function with incompatible arguments.

    Symbol *existence* is checked against the interpreter's real export set
    (see ``_runtime_missing_symbols``), so existing imports of private helpers,
    classes, constants, and re-exports are never falsely reported as missing.
    *Arity/keyword* checks use the AST signatures of the changed module's
    public functions. Returns ``(failures, notes)``.
    """
    failures: List[str] = []
    notes: List[str] = []
    module_to_sigs: Dict[str, Dict[str, _FunctionSig]] = {}
    for rel in code_files:
        path = worktree / rel
        module = _module_name_for_python_path(path, worktree)
        if not module:
            continue
        module_to_sigs[module] = _public_function_sigs(path)
    if not module_to_sigs:
        return failures, notes

    # Cheap substring pre-filter: a caller can only import one of these modules
    # if its source spells out the module's final path component, so files that
    # cannot match are skipped before the expensive AST parse. The walk itself
    # is bounded by _MAX_CALLER_SCAN_FILES.
    tails = {module.rsplit(".", 1)[-1] for module in module_to_sigs}
    # wanted[module] accumulates every symbol imported from that module across
    # the repo so the runtime existence probe runs once per changed module, not
    # once per caller. import_sites keeps (caller, module, name) for attribution.
    wanted: Dict[str, Set[str]] = {module: set() for module in module_to_sigs}
    import_sites: List[Tuple[str, str, str]] = []
    scanned = 0
    truncated = False

    for py_file in _iter_python_files(worktree):
        if scanned >= _MAX_CALLER_SCAN_FILES:
            truncated = True
            break
        scanned += 1
        try:
            text = py_file.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            # A non-UTF-8 source (e.g. a ``# coding: latin-1`` fixture) raises
            # UnicodeDecodeError, which is a ValueError — NOT an OSError. Without
            # catching it here the whole sweep escapes to run_pre_checkup_gate's
            # top-level handler and fails the gate CLOSED ("infrastructure
            # error") on EVERY PR, triggered by one unrelated repo file. Skip it.
            continue
        if not any(tail in text for tail in tails):
            continue
        try:
            tree = ast.parse(text)
        except SyntaxError:
            continue
        rel_caller = py_file.relative_to(worktree).as_posix()
        imported: Dict[str, Tuple[str, str]] = {}
        module_aliases: Dict[str, str] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom):
                # Resolve relative imports (`from .api import x`) to the absolute
                # dotted name so relative callers are not silently missed.
                resolved_mod = _resolve_from_import_module(
                    rel_caller, node.module, node.level
                )
                if resolved_mod not in module_to_sigs:
                    continue
                sigs = module_to_sigs[resolved_mod]
                for alias in node.names:
                    if alias.name == "*":
                        continue
                    wanted[resolved_mod].add(alias.name)
                    import_sites.append((rel_caller, resolved_mod, alias.name))
                    if alias.name in sigs:
                        imported[alias.asname or alias.name] = (resolved_mod, alias.name)
            elif isinstance(node, ast.Import):
                # `import pkg.api as api` / `import pkg.api` -> map the local
                # access prefix to the module so `api.build(...)` /
                # `pkg.api.build(...)` calls can be checked too.
                for alias in node.names:
                    if alias.name in module_to_sigs:
                        module_aliases[alias.asname or alias.name] = alias.name
        rebound = _rebound_names(tree)
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            module: Optional[str] = None
            name: Optional[str] = None
            if isinstance(node.func, ast.Name):
                target = imported.get(node.func.id)
                if target is not None:
                    module, name = target
            elif isinstance(node.func, ast.Attribute):
                chain = _attr_call_chain(node.func)
                # chain[0] is the access root; skip if it is ever rebound in the
                # file (shadowing guard — ast.walk crosses scope boundaries).
                if chain and len(chain) >= 2 and chain[0] not in rebound:
                    attr = chain[-1]
                    prefix = ".".join(chain[:-1])
                    resolved = module_aliases.get(prefix)
                    if resolved is None and prefix in module_to_sigs:
                        resolved = prefix
                    if resolved is not None:
                        module, name = resolved, attr
                        # A call to a symbol the module no longer exports is a
                        # break too — feed the runtime existence probe.
                        wanted[resolved].add(attr)
                        import_sites.append((rel_caller, resolved, attr))
            if module is None or name is None:
                continue
            sig = module_to_sigs[module].get(name)
            if sig is None:
                # Not a known public function (e.g. an imported class/constant);
                # existence is handled by the runtime probe, no arity check.
                continue
            pos_count = len(node.args)
            kw_names = {kw.arg for kw in node.keywords if kw.arg is not None}
            # A positional ``*args`` spread (``f(*pair)`` / ``f(a, b, *rest)``)
            # makes the static positional count meaningless — the runtime length
            # is unknown — so skip BOTH arity checks when one is present (mirrors
            # the ``**kwargs`` guard below). ``len(node.args)`` counts an
            # ``ast.Starred`` as a single positional arg, which would otherwise
            # false-block valid spread calls; this check HARD-BLOCKS the PR.
            has_star_arg = any(isinstance(a, ast.Starred) for a in node.args)
            if (
                not has_star_arg
                and sig.max_positional is not None
                and pos_count > sig.max_positional
            ):
                failures.append(
                    f"caller-compat failed: {rel_caller} calls "
                    f"{name} with {pos_count} positional args, max {sig.max_positional}"
                )
            if (
                not has_star_arg
                and pos_count < sig.min_positional
                and not any(kw.arg is None for kw in node.keywords)
            ):
                supplied = pos_count + len(kw_names)
                if supplied < sig.min_positional:
                    failures.append(
                        f"caller-compat failed: {rel_caller} calls "
                        f"{name} with too few required args"
                    )
            if not sig.accepts_kwargs:
                bad = sorted(kw_names - sig.keywords)
                if bad:
                    failures.append(
                        f"caller-compat failed: {rel_caller} calls "
                        f"{name} with invalid keyword(s): {', '.join(bad)}"
                    )

    # Existence: ask the interpreter which of the symbols callers actually
    # import are absent from each changed module.
    for module, names in wanted.items():
        if not names:
            continue
        missing = _runtime_missing_symbols(worktree, module, sorted(names), timeout=timeout)
        if not missing:
            # Either nothing missing, or the module failed to import (None) —
            # the latter is already hard-blocked by the import check, so don't
            # treat its symbols as missing here.
            continue
        for caller_rel, site_module, name in import_sites:
            if site_module == module and name in missing:
                failures.append(
                    f"caller-compat failed: {caller_rel} "
                    f"imports missing symbol {name} from {module}"
                )

    if truncated:
        notes.append(
            f"caller-compat scan capped at {_MAX_CALLER_SCAN_FILES} files; "
            f"some callers were not checked"
        )
    return failures, notes


def _targeted_test_candidates(worktree: Path, code_files: Sequence[str]) -> List[str]:
    candidates: Set[str] = set()
    tests_dir = worktree / "tests"
    if not tests_dir.exists():
        return []
    for rel in code_files:
        path = Path(rel)
        if path.suffix != ".py":
            continue
        # A directly-changed test file must itself be selected and run. The
        # stem-based matching below only finds tests *of* a changed module, not
        # a changed test file itself (e.g. `tests/test_flow.py` does not match
        # `test_test_flow.py`), so a failing test edited by the PR would
        # otherwise never run and could pass the gate (#1293: run the targeted
        # tests over the touched modules — which includes touched test files).
        name = path.name
        if (
            (name.startswith("test_") or name.endswith("_test.py"))
            and path.parts
            and path.parts[0] == tests_dir.name
            and (worktree / rel).exists()
        ):
            candidates.add(path.as_posix())
        stem = path.stem
        patterns = [
            f"test_{stem}.py",
            f"test_{stem}_*.py",
            f"test_*_{stem}.py",
        ]
        for pattern in patterns:
            for candidate in tests_dir.rglob(pattern):
                try:
                    candidates.add(candidate.relative_to(worktree).as_posix())
                except ValueError:
                    pass
    return sorted(candidates)


def _quarantined_tests() -> Set[str]:
    raw = os.environ.get(_QUARANTINE_ENV, "")
    return {_norm(piece) for piece in re.split(r"[,\s]+", raw) if piece.strip()}


_JS_TS_TEST_EXTS = {".js", ".jsx", ".ts", ".tsx", ".mjs", ".cjs"}
_JS_TS_TEST_NAME_RE = re.compile(r"\.(test|spec)\.[mc]?[jt]sx?$", re.IGNORECASE)


def _changed_js_ts_tests(code_files: Sequence[str]) -> List[str]:
    """Changed files that look like JS/TS tests (``*.test.ts`` / ``*.spec.js`` /
    a ``__tests__/`` member)."""
    out: Set[str] = set()
    for rel in code_files:
        path = Path(rel)
        if path.suffix.lower() not in _JS_TS_TEST_EXTS:
            continue
        if _JS_TS_TEST_NAME_RE.search(path.name) or "__tests__" in path.parts:
            out.add(_norm(rel))
    return sorted(out)


def _run_targeted_tests(
    worktree: Path,
    code_files: Sequence[str],
    *,
    timeout: float,
) -> Tuple[List[str], List[str]]:
    failures: List[str] = []
    notes: List[str] = []
    # The targeted-test phase runs pytest, so a changed JS/TS test is not
    # executed. Surface that explicitly rather than letting it pass silently
    # (#1293): JS/TS test execution would need a JS runner dispatched against
    # PR-controlled test/config, which the fork-PR-RCE constraint forbids;
    # compile/type errors in the changed test are still caught by the tsc gate.
    js_ts_tests = _changed_js_ts_tests(code_files)
    if js_ts_tests:
        notes.append(
            "targeted-tests note: changed JS/TS test file(s) not run by the gate "
            f"(pytest only; JS test execution is out of scope for the RCE "
            f"constraint): {', '.join(js_ts_tests)}"
        )
    candidates = _targeted_test_candidates(worktree, code_files)
    if not candidates:
        notes.append("targeted-tests skipped: no matching test files found")
        return failures, notes
    quarantine = _quarantined_tests()
    gating = [test for test in candidates if test not in quarantine]
    non_gating = [test for test in candidates if test in quarantine]
    # Exclude slow/networked suites: the gate must never trigger a real LLM
    # call or an e2e/integration run. Hardened env (no live secrets, sanitized
    # PATH) is defence in depth. pytest exit 5 = "no tests collected" (e.g.
    # every candidate filtered out by the marker) is NOT a gate failure.
    env = _python_import_env(worktree)
    pytest_markers = ["-m", "not integration and not e2e and not real"]
    if non_gating:
        ok, output = _run_command(
            [sys.executable, "-m", "pytest", "-q", *pytest_markers, *non_gating],
            worktree=worktree,
            timeout=timeout,
            env=env,
            success_codes=(0, 5),
        )
        status = "passed" if ok else "failed"
        notes.append(f"targeted-tests quarantine {status}: {', '.join(non_gating)} {output}".strip())
    if gating:
        ok, output = _run_command(
            [sys.executable, "-m", "pytest", "-q", *pytest_markers, *gating],
            worktree=worktree,
            timeout=timeout,
            env=env,
            success_codes=(0, 5),
        )
        if not ok:
            failures.append(f"targeted-tests failed for {', '.join(gating)}: {output}")
    else:
        notes.append("targeted-tests gating skipped: all candidates quarantined")
    return failures, notes


def _run_build_smoke(
    worktree: Path,
    changed_files: Sequence[str],
    *,
    base_ref: Optional[str],
    issue_number: Optional[int],
    timeout_per_check: float,
) -> _CheckOutcome:
    if _docs_only(changed_files):
        return _CheckOutcome(
            ok=True,
            messages=["phase=build-smoke skipped: docs-only or empty changed_files"],
        )

    code_files = _changed_code_files(changed_files)
    failures: List[str] = []
    notes: List[str] = []

    artifacts_dir = (
        worktree
        / ".pdd"
        / "pre-checkup-gate"
        / (f"issue-{issue_number}" if issue_number is not None else "local")
    )
    # Pass the FULL changed set (not code_files) to discover_gates: checkup_gates
    # decides which gates to SKIP from the full diff — e.g. it skips every
    # npm-family gate when the PR touches package.json / a package-manager config
    # (corepack-via-packageManager and runner-redirect RCE guards). Stripping
    # non-code files (package.json, pyproject.toml, tsconfig.json) here would
    # hide PR-controlled config from those guards and let a fork PR run gates
    # against poisoned config. R3(a) specifies changed_files for this reason.
    gates = discover_gates(worktree, changed_files, base_ref=base_ref)
    gate_results = run_gates(
        worktree,
        gates,
        artifacts_dir=artifacts_dir,
        round_number=1,
        mode="pre-checkup",
        default_timeout=timeout_per_check,
    )
    failed_gates = [r for r in gate_results if not r.passed]
    failures.extend(
        f"gate {r.gate.name} failed for {r.gate.source}: "
        f"exit={r.exit_code} error={_scrub(r.error)} stderr={_excerpt(r.stderr_excerpt)}"
        for r in failed_gates
    )
    if gates:
        notes.append(f"deterministic-gates ran: {len(gates)}")
    else:
        notes.append("deterministic-gates skipped: no gates discovered")

    failures.extend(_check_python_imports(worktree, code_files, timeout=timeout_per_check))
    notes.extend(_check_route_probe(worktree, code_files, timeout=timeout_per_check))
    caller_failures, caller_notes = _check_caller_compatibility(
        worktree, code_files, timeout=timeout_per_check
    )
    failures.extend(caller_failures)
    notes.extend(caller_notes)
    test_failures, test_notes = _run_targeted_tests(
        worktree,
        code_files,
        timeout=timeout_per_check,
    )
    failures.extend(test_failures)
    notes.extend(test_notes)

    if failures:
        return _CheckOutcome(
            ok=False,
            messages=["phase=build-smoke failures: " + " | ".join(failures)],
        )
    return _CheckOutcome(
        ok=True,
        messages=["phase=build-smoke passed: " + " | ".join(notes)],
    )


def run_pre_checkup_gate(
    worktree: Path,
    changed_files: Sequence[str],
    *,
    base_ref: Optional[str] = None,
    repo_owner: str = "",
    repo_name: str = "",
    issue_number: Optional[int] = None,
    strict: Optional[bool] = None,
    quiet: bool = False,
    timeout_per_check: float = 300.0,
) -> Tuple[bool, str, float]:
    """Run drift-sync then deterministic build/smoke checks before checkup."""
    _ = repo_owner, repo_name
    total_cost = 0.0
    try:
        root = Path(worktree).resolve()
        touched = [_norm(path) for path in changed_files if _norm(path)]
        is_strict = _strict_enabled(strict)

        drift = _run_drift_sync(
            root,
            touched,
            base_ref=base_ref,
            strict=is_strict,
        )
        total_cost += drift.cost
        messages = list(drift.messages)
        if not drift.ok:
            message = "pre_checkup_gate blocked; " + " ; ".join(messages)
            if not quiet:
                print(message)
            return False, message, total_cost

        build = _run_build_smoke(
            root,
            touched,
            base_ref=base_ref,
            issue_number=issue_number,
            timeout_per_check=timeout_per_check,
        )
        messages.extend(build.messages)
        total_cost += build.cost
        passed = build.ok
        prefix = "pre_checkup_gate passed" if passed else "pre_checkup_gate blocked"
        message = prefix + "; " + " ; ".join(messages)
        if not quiet:
            print(message)
        return passed, message, total_cost
    except Exception as exc:
        message = f"pre_checkup_gate blocked; phase=infrastructure error: {_scrub(exc)}"
        if not quiet:
            print(message)
        return False, message, total_cost


__all__ = ["run_pre_checkup_gate"]
