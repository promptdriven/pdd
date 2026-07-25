#!/usr/bin/env python3
"""Generate the PDD/provider artifacts from one versioned catalog manifest.

The manifest intentionally contains only public provider configuration and
model/pricing metadata.  It never contains user credentials, tenant endpoint
URLs, or an executable request template.  The Cloud gateway derives its fixed
request surface from the protocol/profile fields instead.

This script is deliberately dependency-free so both repositories can run a
drift check in hermetic local test environments:

    python scripts/provider_catalog.py --manifest data/provider_catalog.v1.json \
      --cli-csv data/llm_model.csv --cloud-root ../pdd_cloud --check
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import pprint
import sys
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import urlsplit


CSV_COLUMNS = (
    "provider",
    "model",
    "input",
    "output",
    "coding_arena_elo",
    "model_rank_score",
    "model_rank_source",
    "base_url",
    "api_key",
    "max_reasoning_tokens",
    "structured_output",
    "reasoning_type",
    "location",
    "interactive_only",
    "context_limit",
)

PROTOCOLS = frozenset(
    {
        "openai_responses",
        "openai_chat_completions",
        "anthropic_messages",
        "gemini_generate",
        "specialized",
    }
)
AUTH_KINDS = frozenset(
    {"api_key", "multi_field", "cloud_identity", "interactive_subscription"}
)
EXECUTION_PROFILES = frozenset(
    {
        "native_claude",
        "native_gemini",
        "native_glm",
        "opencode_openai_chat",
        "manual_review",
        "local_only",
        "interactive_only",
    }
)


class CatalogError(ValueError):
    """The source manifest is malformed or internally inconsistent."""


def _read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CatalogError(f"Unable to read provider catalog: {path}") from exc
    if not isinstance(value, dict):
        raise CatalogError("Provider catalog root must be an object")
    return value


def _identifier(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if (
        not text
        or len(text) > 64
        or any(ch not in "abcdefghijklmnopqrstuvwxyz0123456789_-" for ch in text)
    ):
        raise CatalogError(f"{field} is invalid")
    if not text[0].isalpha():
        raise CatalogError(f"{field} is invalid")
    return text


def _fixed_https_origin(value: object, field: str) -> str:
    text = str(value or "").strip()
    parsed = urlsplit(text)
    if (
        parsed.scheme != "https"
        or not parsed.hostname
        or parsed.username
        or parsed.password
        or parsed.query
        or parsed.fragment
        or parsed.path not in {"", "/"}
        or parsed.port not in {None, 443}
    ):
        raise CatalogError(f"{field} must be a fixed HTTPS origin")
    return f"https://{parsed.hostname.lower()}"


def _public_text(value: object, field: str, *, maximum: int = 512) -> str:
    text = str(value or "").strip()
    if not text or len(text) > maximum or any(ch in text for ch in "\r\n\0"):
        raise CatalogError(f"{field} is invalid")
    return text


def _github_label(value: object, field: str) -> str:
    label = _public_text(value, field, maximum=64)
    if (
        not label.startswith("pdd-")
        or label != label.lower()
        or any(
            ch not in "abcdefghijklmnopqrstuvwxyz0123456789-"
            for ch in label
        )
    ):
        raise CatalogError(f"{field} is invalid")
    return label


def _model_base_url(value: object, field: str, *, local_only: bool) -> str:
    text = str(value or "").strip()
    parsed = urlsplit(text)
    try:
        port = parsed.port
    except ValueError as exc:
        raise CatalogError(f"{field} must be a fixed HTTPS API base URL") from exc
    is_local_http = (
        local_only
        and parsed.scheme == "http"
        and parsed.hostname in {"localhost", "127.0.0.1", "::1"}
    )
    if (
        not text
        or (parsed.scheme != "https" and not is_local_http)
        or not parsed.hostname
        or parsed.username
        or parsed.password
        or parsed.query
        or parsed.fragment
        or any(part in parsed.path for part in ("//", "..", "\r", "\n"))
        or (parsed.scheme == "https" and port not in {None, 443})
    ):
        raise CatalogError(f"{field} must be a fixed HTTPS API base URL")
    return text.rstrip("/")


def _validate_manifest(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    if manifest.get("schema_version") != 1:
        raise CatalogError("Unsupported provider catalog schema_version")
    _public_text(manifest.get("catalog_version"), "catalog_version", maximum=64)
    providers = manifest.get("providers")
    if not isinstance(providers, list) or not providers:
        raise CatalogError("Provider catalog must contain providers")
    known_ids: set[str] = set()
    known_github_labels: set[str] = set()
    known_model_orders: set[int] = set()
    known_source_rows: set[tuple[str, str]] = set()
    normalized: list[dict[str, Any]] = []
    for raw_provider in providers:
        if not isinstance(raw_provider, dict):
            raise CatalogError("Provider entry must be an object")
        provider = dict(raw_provider)
        provider_id = _identifier(provider.get("id"), "provider id")
        if provider_id in known_ids:
            raise CatalogError(f"Duplicate provider id: {provider_id}")
        known_ids.add(provider_id)
        provider["id"] = provider_id
        provider["display_name"] = _public_text(
            provider.get("display_name"), "display_name"
        )
        source_names = provider.get("csv_providers")
        if not isinstance(source_names, list) or not source_names:
            raise CatalogError(f"Provider {provider_id} must name its CSV providers")
        provider["csv_providers"] = [
            _public_text(value, "csv provider") for value in source_names
        ]
        protocol = str(provider.get("protocol") or "")
        if protocol not in PROTOCOLS:
            raise CatalogError(f"Provider {provider_id} has an unsupported protocol")
        auth = provider.get("auth")
        if not isinstance(auth, dict) or str(auth.get("kind") or "") not in AUTH_KINDS:
            raise CatalogError(f"Provider {provider_id} has an invalid auth schema")
        fields = auth.get("fields")
        if not isinstance(fields, list) or not fields:
            raise CatalogError(f"Provider {provider_id} must declare auth fields")
        field_ids: set[str] = set()
        for field in fields:
            if not isinstance(field, dict):
                raise CatalogError(f"Provider {provider_id} has an invalid auth field")
            field_id = _identifier(field.get("id"), "auth field id")
            if field_id in field_ids:
                raise CatalogError(
                    f"Provider {provider_id} repeats auth field {field_id}"
                )
            field_ids.add(field_id)
            _public_text(field.get("label"), "auth field label", maximum=96)
            if not isinstance(field.get("secret"), bool):
                raise CatalogError(
                    f"Provider {provider_id} auth field secret flag is invalid"
                )
        origin = provider.get("origin")
        if origin is not None:
            provider["origin"] = _fixed_https_origin(
                origin, f"Provider {provider_id} origin"
            )
            provider["origin_reason"] = ""
        else:
            provider["origin_reason"] = _public_text(
                provider.get("origin_reason"), f"Provider {provider_id} origin reason"
            )
        github = provider.get("github")
        if not isinstance(github, dict):
            raise CatalogError(f"Provider {provider_id} must declare GitHub metadata")
        label = _github_label(github.get("label"), "GitHub label")
        if label in known_github_labels:
            raise CatalogError(f"Duplicate GitHub label: {label}")
        known_github_labels.add(label)
        github["label"] = label
        model_labels = github.get("model_labels", {})
        if not isinstance(model_labels, dict):
            raise CatalogError(
                f"Provider {provider_id} model_labels must be an object"
            )
        normalized_model_labels: dict[str, str] = {}
        for raw_label, raw_model in model_labels.items():
            model_label = _github_label(raw_label, "GitHub model label")
            if model_label in known_github_labels:
                raise CatalogError(f"Duplicate GitHub label: {model_label}")
            known_github_labels.add(model_label)
            normalized_model_labels[model_label] = _public_text(
                raw_model, "GitHub model label target", maximum=256
            )
        if normalized_model_labels:
            github["model_labels"] = normalized_model_labels
        else:
            github.pop("model_labels", None)
        execution_profile = str(github.get("execution_profile") or "")
        if execution_profile not in EXECUTION_PROFILES:
            raise CatalogError(f"Provider {provider_id} execution profile is invalid")
        eligible = github.get("eligible")
        if not isinstance(eligible, bool):
            raise CatalogError(f"Provider {provider_id} GitHub eligibility is invalid")
        reason = str(github.get("reason") or "").strip()
        if not eligible and not reason:
            raise CatalogError(f"Provider {provider_id} needs an ineligibility reason")
        if eligible and execution_profile in {
            "manual_review",
            "local_only",
            "interactive_only",
        }:
            raise CatalogError(
                f"Provider {provider_id} cannot be eligible with its execution profile"
            )
        request = provider.get("request")
        if not isinstance(request, dict):
            raise CatalogError(f"Provider {provider_id} request surface is invalid")
        methods = request.get("methods")
        paths = request.get("paths")
        query = request.get("query")
        headers = request.get("headers")
        base_path = str(request.get("base_path") or "")
        if (
            not isinstance(methods, list)
            or not isinstance(paths, list)
            or not isinstance(query, list)
            or not isinstance(headers, list)
            or (base_path and not base_path.startswith("/"))
            or any(part in base_path for part in ("?", "#", "//", "..", "\\r", "\\n"))
        ):
            raise CatalogError(f"Provider {provider_id} request surface is invalid")
        if protocol == "specialized":
            if methods or paths:
                raise CatalogError(
                    f"Provider {provider_id} specialized surface must be explicitly empty"
                )
        elif not methods or not paths:
            raise CatalogError(f"Provider {provider_id} request surface is incomplete")
        for method in methods:
            if str(method) not in {"GET", "POST"}:
                raise CatalogError(f"Provider {provider_id} request method is invalid")
        for path in paths:
            if (
                not isinstance(path, str)
                or not path.startswith("/")
                or any(part in path for part in ("?", "#", "//", "..", "\\r", "\\n"))
            ):
                raise CatalogError(f"Provider {provider_id} request path is invalid")
        for name in [*query, *headers]:
            if (
                not isinstance(name, str)
                or not name
                or len(name) > 64
                or any(
                    ch not in "abcdefghijklmnopqrstuvwxyz0123456789_-" for ch in name
                )
            ):
                raise CatalogError(f"Provider {provider_id} request name is invalid")
        probe = provider.get("probe")
        if not isinstance(probe, dict) or not isinstance(probe.get("method"), str):
            raise CatalogError(f"Provider {provider_id} probe is invalid")
        if protocol != "specialized" and (
            probe.get("method") not in {"GET", "POST"}
            or not isinstance(probe.get("path"), str)
            or not str(probe["path"]).startswith("/")
        ):
            raise CatalogError(f"Provider {provider_id} probe is invalid")
        failure = provider.get("failure")
        if not isinstance(failure, dict) or set(failure) != {
            "unauthorized",
            "forbidden",
            "quota",
            "transient",
        }:
            raise CatalogError(
                f"Provider {provider_id} failure classification is invalid"
            )
        for statuses in failure.values():
            if not isinstance(statuses, list) or any(
                not isinstance(status, int) or status < 100 or status > 599
                for status in statuses
            ):
                raise CatalogError(
                    f"Provider {provider_id} failure classification is invalid"
                )
        models = provider.get("models")
        if not isinstance(models, list):
            raise CatalogError(f"Provider {provider_id} models are invalid")
        provider_models: dict[str, dict[str, Any]] = {}
        for raw_model in models:
            if not isinstance(raw_model, dict):
                raise CatalogError(f"Provider {provider_id} model must be an object")
            row = raw_model.get("csv")
            if not isinstance(row, dict):
                raise CatalogError(f"Provider {provider_id} model lacks CSV data")
            missing = [column for column in CSV_COLUMNS if column not in row]
            if missing:
                raise CatalogError(
                    f"Provider {provider_id} model lacks CSV columns: {missing}"
                )
            source_provider = _public_text(row.get("provider"), "model CSV provider")
            if source_provider not in provider["csv_providers"]:
                raise CatalogError(
                    f"Provider {provider_id} model has an undeclared CSV provider"
                )
            model = _public_text(row.get("model"), "model id", maximum=256)
            if model in provider_models:
                raise CatalogError(
                    f"Provider {provider_id} repeats model id: {model}"
                )
            provider_models[model] = raw_model
            source_key = (source_provider, model)
            if source_key in known_source_rows:
                raise CatalogError(
                    f"Duplicate catalog model: {source_provider}/{model}"
                )
            known_source_rows.add(source_key)
            _public_text(raw_model.get("upstream_model"), "upstream model", maximum=256)
            if not isinstance(raw_model.get("byok_eligible"), bool):
                raise CatalogError(
                    f"Provider {provider_id} model BYOK eligibility is invalid"
                )
            if not isinstance(raw_model.get("order"), int) or raw_model["order"] < 0:
                raise CatalogError(f"Provider {provider_id} model order is invalid")
            if raw_model["order"] in known_model_orders:
                raise CatalogError(
                    f"Duplicate catalog model order: {raw_model['order']}"
                )
            known_model_orders.add(raw_model["order"])
            if raw_model["byok_eligible"] and not eligible:
                raise CatalogError(
                    f"Provider {provider_id} enables a model without an execution profile"
                )
            model_base_url = str(row.get("base_url") or "").strip()
            if model_base_url:
                row["base_url"] = _model_base_url(
                    model_base_url,
                    f"Provider {provider_id} model {model} base_url",
                    local_only=execution_profile == "local_only",
                )
        for model_label, target in github.get("model_labels", {}).items():
            target_model = provider_models.get(target)
            if target_model is None:
                raise CatalogError(
                    f"Provider {provider_id} model label {model_label} "
                    f"targets unknown model {target}"
                )
            if not target_model["byok_eligible"]:
                raise CatalogError(
                    f"Provider {provider_id} model label {model_label} "
                    f"targets an ineligible model"
                )
        normalized.append(provider)
    cloud_columns = manifest.get("cloud_csv_columns")
    cloud_rows = manifest.get("cloud_csv")
    if not isinstance(cloud_columns, list) or not cloud_columns:
        raise CatalogError("cloud_csv_columns is invalid")
    if any(not isinstance(column, str) or not column for column in cloud_columns):
        raise CatalogError("cloud_csv_columns is invalid")
    if not isinstance(cloud_rows, list):
        raise CatalogError("cloud_csv is invalid")
    for row in cloud_rows:
        if not isinstance(row, dict) or any(
            column not in row for column in cloud_columns
        ):
            raise CatalogError("cloud_csv row is invalid")
    return normalized


def _catalog_metadata(
    manifest: dict[str, Any], providers: Iterable[dict[str, Any]], *, source_digest: str
) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "catalog_version": manifest["catalog_version"],
        "source_sha256": source_digest,
        "providers": [
            {
                "id": provider["id"],
                "display_name": provider["display_name"],
                "protocol": provider["protocol"],
                "origin": provider.get("origin"),
                "origin_reason": provider.get("origin_reason", ""),
                "auth": provider["auth"],
                "request": provider.get("request", {}),
                "probe": provider.get("probe", {}),
                "failure": provider.get("failure", {}),
                "github": provider["github"],
                "credential_names": sorted(
                    {
                        name.strip().upper()
                        for entry in provider["models"]
                        for name in str(entry["csv"].get("api_key", "")).split("|")
                        if name.strip()
                    }
                ),
                "models": [
                    {
                        "model": entry["csv"]["model"],
                        "upstream_model": entry["upstream_model"],
                        "capabilities": entry.get("capabilities", []),
                        "context_limit": entry["csv"].get("context_limit", ""),
                        "input": entry["csv"].get("input", ""),
                        "output": entry["csv"].get("output", ""),
                        "reasoning_type": entry["csv"].get("reasoning_type", ""),
                        "byok_eligible": entry["byok_eligible"],
                        **(
                            {"base_url": entry["csv"]["base_url"]}
                            if entry["csv"].get("base_url")
                            else {}
                        ),
                    }
                    for entry in provider["models"]
                ],
            }
            for provider in providers
        ],
    }


def _csv_bytes(
    rows: Iterable[dict[str, Any]], columns: Iterable[str] = CSV_COLUMNS
) -> bytes:
    import io

    buffer = io.StringIO(newline="")
    fieldnames = tuple(columns)
    writer = csv.DictWriter(buffer, fieldnames=fieldnames, lineterminator="\n")
    writer.writeheader()
    for row in rows:
        writer.writerow({column: str(row.get(column, "")) for column in fieldnames})
    return buffer.getvalue().encode("utf-8")


def _python_metadata_bytes(metadata: dict[str, Any]) -> bytes:
    encoded = pprint.pformat(metadata, width=100, sort_dicts=True)
    return (
        "# Generated by pdd/scripts/provider_catalog.py; do not edit.\n"
        "from __future__ import annotations\n\n"
        f"CATALOG = {encoded}\n"
    ).encode("utf-8")


def _typescript_metadata_bytes(metadata: dict[str, Any]) -> bytes:
    encoded = json.dumps(metadata, indent=2, sort_keys=True, ensure_ascii=False)
    return (
        "// Generated by pdd/scripts/provider_catalog.py; do not edit.\n"
        "export const providerCatalog = "
        f"{encoded} as const;\n"
        "export type CatalogProvider = (typeof providerCatalog.providers)[number];\n"
    ).encode("utf-8")


def _write_or_check(path: Path, content: bytes, *, check: bool) -> bool:
    if check:
        try:
            return path.read_bytes() == content
        except OSError:
            return False
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)
    return True


def generate(
    manifest_path: Path,
    cli_csv: Path,
    cloud_root: Path,
    *,
    check: bool,
) -> list[Path]:
    manifest = _read_json(manifest_path)
    providers = _validate_manifest(manifest)
    source_digest = source_sha256(manifest_path)
    metadata = _catalog_metadata(manifest, providers, source_digest=source_digest)
    all_models = sorted(
        (entry for provider in providers for entry in provider["models"]),
        key=lambda entry: entry["order"],
    )
    source_rows = [entry["csv"] for entry in all_models]
    targets = {
        cli_csv: _csv_bytes(source_rows),
        cloud_root / "extensions/github_pdd_app/llm_model_cloud.csv": _csv_bytes(
            manifest["cloud_csv"], manifest["cloud_csv_columns"]
        ),
        cloud_root / "extensions/github_pdd_app/provider_catalog.generated.json": (
            manifest_path.read_bytes()
        ),
        cloud_root
        / "extensions/github_pdd_app/src/generated/provider_catalog.py": _python_metadata_bytes(
            metadata
        ),
        cloud_root
        / "frontend/src/generated/providerCatalog.ts": _typescript_metadata_bytes(
            metadata
        ),
    }
    stale = [
        path
        for path, content in targets.items()
        if not _write_or_check(path, content, check=check)
    ]
    if stale:
        rendered = ", ".join(str(path) for path in stale)
        raise CatalogError(f"Generated provider catalog files are stale: {rendered}")
    return list(targets)


def source_sha256(manifest_path: Path) -> str:
    return hashlib.sha256(manifest_path.read_bytes()).hexdigest()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--cli-csv", type=Path, required=True)
    parser.add_argument("--cloud-root", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        generate(args.manifest, args.cli_csv, args.cloud_root, check=args.check)
    except CatalogError as exc:
        print(f"provider catalog: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
