"""ChatGPT/Codex subscription support for the inner ``llm_invoke`` path.

PDD can fall back to a flat-rate **ChatGPT subscription** for LLM calls when no
API-key provider is available (e.g. ``ANTHROPIC_API_KEY`` is missing or rate
limited). This is the feature requested in issue #1269 and it closes the
``--force`` failure class in #1254 / #1135 where the inner ``llm_invoke`` path
hard-required ``ANTHROPIC_API_KEY``.

The subscription is reached through litellm's ``chatgpt/`` provider, which calls
``https://chatgpt.com/backend-api/codex`` using the OAuth token that the
``codex`` CLI writes when a user runs ``codex login`` (ChatGPT sign-in).

Two shapes have to be reconciled:

* The ``codex`` CLI stores its token in ``$CODEX_HOME/auth.json`` (default
  ``~/.codex/auth.json``) with the OAuth fields **nested** under a ``"tokens"``
  object.
* litellm's ChatGPT authenticator reads ``$CHATGPT_TOKEN_DIR/auth.json``
  (default ``~/.config/litellm/chatgpt``) and expects the OAuth fields at the
  **top level**.

:func:`bridge_codex_auth_for_litellm` flattens the former into the latter so a
user (or the cloud worker) only has to provide the codex ``auth.json`` once.

There are also two known quirks of the subscription backend that this module
handles:

* litellm returns an *empty* response for ``chatgpt/`` models on the pinned
  version (upstream BerriAI/litellm#25429); :func:`apply_litellm_chatgpt_output_patch`
  applies the PR #27562 fix at runtime without forking litellm.
* the backend ignores ``response_format``/``json_schema``;
  :func:`build_chatgpt_schema_instruction` returns a prompt that coerces JSON
  instead.

Everything here is best-effort and never raises into the caller — a failure
just means the ``chatgpt/`` model is skipped like any other unavailable
provider.

ToS note: this is bring-your-own-subscription. Each user authenticates their
own ChatGPT account; PDD never pools or shares one subscription across users.
"""

from __future__ import annotations

import json
import logging
import os
import stat
from pathlib import Path
from typing import Any, Dict, Optional

logger = logging.getLogger(__name__)

# litellm routes any model whose name starts with this prefix through the
# ChatGPT subscription backend (chatgpt.com/backend-api/codex).
CHATGPT_MODEL_PREFIX = "chatgpt/"

# OAuth fields litellm's ChatGPT authenticator consumes from auth.json.
_TOKEN_FIELDS = ("access_token", "refresh_token", "id_token", "account_id")


def is_chatgpt_subscription_model(model_name: Any) -> bool:
    """Return ``True`` for models routed through the ChatGPT subscription backend."""
    return str(model_name or "").lower().startswith(CHATGPT_MODEL_PREFIX)


def _codex_home() -> Path:
    """Resolve the codex CLI home directory (honours ``CODEX_HOME``)."""
    env_home = os.environ.get("CODEX_HOME")
    if env_home:
        return Path(env_home).expanduser()
    return Path.home() / ".codex"


def _codex_auth_path() -> Path:
    """Path to the codex CLI's ``auth.json``."""
    return _codex_home() / "auth.json"


def _flatten_codex_tokens(auth: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Lift the OAuth fields to the top level litellm expects.

    Accepts both the codex CLI shape (fields nested under ``"tokens"``) and an
    already-flat shape. Returns ``None`` when no usable ``access_token`` is
    present.
    """
    if not isinstance(auth, dict):
        return None
    source = auth.get("tokens") if isinstance(auth.get("tokens"), dict) else auth
    flat = {key: source.get(key) for key in _TOKEN_FIELDS if source.get(key)}
    if not flat.get("access_token"):
        return None
    return flat


def _bridged_token_dir() -> Path:
    """Stable, private directory PDD writes the flattened auth.json into."""
    override = os.environ.get("PDD_CHATGPT_TOKEN_DIR")
    if override:
        return Path(override).expanduser()
    return Path.home() / ".cache" / "pdd" / "chatgpt"


def _write_private_json(path: Path, payload: Dict[str, Any]) -> None:
    """Write ``payload`` as JSON with 0600 perms in a 0700 directory."""
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        os.chmod(path.parent, stat.S_IRWXU)  # 0700
    except OSError:
        pass
    path.write_text(json.dumps(payload))
    try:
        os.chmod(path, stat.S_IRUSR | stat.S_IWUSR)  # 0600
    except OSError:
        pass


def _auth_filename() -> str:
    """The auth filename litellm's ChatGPT authenticator reads (honors CHATGPT_AUTH_FILE)."""
    return os.environ.get("CHATGPT_AUTH_FILE", "auth.json")


def _token_dir_has_usable_auth(token_dir: Path) -> bool:
    """True only when ``token_dir`` holds an auth file with a usable access_token.

    Existence alone is NOT enough — litellm needs a real token bundle, so a
    garbage/empty file must read as 'no usable auth' (otherwise the --force
    safety gate in ``_ensure_api_key`` is bypassed and litellm fails at call
    time).
    """
    auth_file = token_dir / _auth_filename()
    if not auth_file.is_file():
        return False
    try:
        return _flatten_codex_tokens(json.loads(auth_file.read_text())) is not None
    except Exception:
        return False


def bridge_codex_auth_for_litellm() -> bool:
    """Make a ``codex login`` token usable by litellm's ``chatgpt/`` provider.

    Idempotent and best-effort. Returns ``True`` only when a token with a usable
    ``access_token`` is staged where litellm will read it
    (``$CHATGPT_TOKEN_DIR/$CHATGPT_AUTH_FILE``). Never raises.

    Resolution order:

    1. If the user pointed ``CHATGPT_TOKEN_DIR`` at a directory other than PDD's
       own bridged dir AND it holds a *usable* auth file, respect it untouched.
       (A present-but-invalid file is NOT treated as usable — that would bypass
       the ``--force`` credential gate.)
    2. Otherwise read ``$CODEX_HOME/auth.json``, flatten the nested ``tokens``
       object, and write it (under the ``CHATGPT_AUTH_FILE`` name) to a private
       PDD-managed directory whose path is exported via ``CHATGPT_TOKEN_DIR``.

    The bridged file is refreshed when the source codex ``auth.json`` is newer,
    so token rotations performed by ``codex`` are picked up on the next call.
    """
    try:
        dest_dir = _bridged_token_dir()
        auth_name = _auth_filename()
        dest = dest_dir / auth_name

        # 1. Respect a CHATGPT_TOKEN_DIR the user pointed elsewhere themselves,
        #    but ONLY when it actually holds a usable token (existence alone is
        #    insufficient — see _token_dir_has_usable_auth).
        existing_dir = os.environ.get("CHATGPT_TOKEN_DIR")
        if existing_dir and Path(existing_dir).expanduser() != dest_dir:
            if _token_dir_has_usable_auth(Path(existing_dir).expanduser()):
                return True
            # Configured but unusable: fall through and populate from codex below.

        source = _codex_auth_path()
        if not source.is_file():
            # No codex token to bridge; a previously staged *usable* file still works.
            if _token_dir_has_usable_auth(dest_dir):
                os.environ["CHATGPT_TOKEN_DIR"] = str(dest_dir)
                return True
            return False

        # 2. (Re)stage from the codex token, refreshing when the source has
        #    rotated since we last wrote the bridged copy.
        if not (dest.is_file() and dest.stat().st_mtime >= source.stat().st_mtime):
            flat = _flatten_codex_tokens(json.loads(source.read_text()))
            if flat is None:
                # Source unusable; only succeed if a prior usable staged copy
                # exists — and if so, export CHATGPT_TOKEN_DIR so litellm can
                # actually find it (the bug: returning True without exporting).
                if _token_dir_has_usable_auth(dest_dir):
                    os.environ["CHATGPT_TOKEN_DIR"] = str(dest_dir)
                    return True
                return False
            _write_private_json(dest, flat)
            logger.debug(
                "Bridged codex auth from %s to %s for litellm chatgpt/ provider.", source, dest
            )

        # Final guard: only claim success if what we staged is actually usable.
        if not _token_dir_has_usable_auth(dest_dir):
            return False
        os.environ["CHATGPT_TOKEN_DIR"] = str(dest_dir)
        return True
    except Exception as exc:  # pragma: no cover - defensive; never break callers
        logger.debug("Codex auth bridge skipped (%s): %s", type(exc).__name__, exc)
        return False


def has_codex_subscription_auth() -> bool:
    """Return ``True`` when a usable ChatGPT subscription token is available.

    Checks an explicitly-configured ``CHATGPT_TOKEN_DIR`` (honoring
    ``CHATGPT_AUTH_FILE``) first, then the codex CLI's ``auth.json``. "Usable"
    means a real ``access_token`` is present — a garbage/empty file reads as
    unavailable. Used by the credential check so a ``chatgpt/`` model is skipped
    cleanly in non-interactive (``PDD_FORCE``) runs instead of hanging litellm on
    an interactive device-login flow.
    """
    try:
        existing_dir = os.environ.get("CHATGPT_TOKEN_DIR")
        if existing_dir and _token_dir_has_usable_auth(Path(existing_dir).expanduser()):
            return True
        # Also honor a token PDD previously staged in its private bridge dir:
        # the runtime bridge treats that staged copy as usable, so setup/auth
        # detection must agree (otherwise a working subscription is hidden from
        # setup/curation/smoke while llm_invoke can use it).
        if _token_dir_has_usable_auth(_bridged_token_dir()):
            return True
        source = _codex_auth_path()
        if source.is_file():
            return _flatten_codex_tokens(json.loads(source.read_text())) is not None
    except Exception as exc:  # pragma: no cover - defensive
        logger.debug("Codex auth detection skipped (%s): %s", type(exc).__name__, exc)
    return False

class _RawResponseProxy:
    """Wrap an httpx-style response, overriding only ``.text``.

    Used by :func:`apply_litellm_chatgpt_output_patch` to feed litellm's own
    transform a body whose ``response.completed`` event has its ``output`` array
    repopulated, while delegating headers/status to the real response.
    """

    def __init__(self, inner: Any, text: str) -> None:
        self._inner = inner
        self._text = text

    @property
    def text(self) -> str:
        return self._text

    def __getattr__(self, name: str) -> Any:  # pragma: no cover - thin delegate
        return getattr(self._inner, name)


# SSE event-type strings emitted by the Codex backend. These equal litellm's
# ResponsesAPIStreamEvents enum *values*; kept as plain strings so the splice is
# testable without importing litellm.
_SSE_OUTPUT_ITEM_DONE = "response.output_item.done"
_SSE_RESPONSE_COMPLETED = "response.completed"


def _strip_sse_data(line: str) -> Optional[str]:
    """Return the payload of an SSE ``data:`` line, else None.

    Prefers litellm's own stripper (handles odd framing) and falls back to a
    manual ``data:`` strip so this stays usable/testable when litellm internals
    are unavailable.
    """
    try:
        from litellm.utils import CustomStreamWrapper
        stripped = CustomStreamWrapper._strip_sse_data_from_chunk(line)
        if stripped is not None:
            return stripped
    except Exception:
        pass
    line = line.strip()
    return line[len("data:"):] if line.startswith("data:") else None


def _collapse_codex_output(collected: list) -> list:
    """Collapse collected ``output_item.done`` items to the single answer message.

    Codex (gpt-5.x) can emit several message items — e.g. an empty
    ``phase='commentary'`` preamble plus the real ``phase='final_answer'``.
    litellm's responses->chat transform mishandles multiple/empty message items
    and yields a response with no usable ``.choices`` (issue #1269). Prefer the
    ``final_answer`` message (else the last non-empty), matching the
    single-message shape litellm converts correctly. Fall back to the raw items
    only if no message carried text.
    """
    def _item_text(item: Dict[str, Any]) -> str:
        return "".join(
            part.get("text", "")
            for part in (item.get("content") or [])
            if isinstance(part, dict)
        )

    messages = [it for it in collected if isinstance(it, dict) and it.get("type") == "message"]
    nonempty = [it for it in messages if _item_text(it).strip()]
    if nonempty:
        finals = [it for it in nonempty if it.get("phase") == "final_answer"]
        return [finals[-1] if finals else nonempty[-1]]
    return collected


def splice_codex_output_into_sse(
    body_text: str,
    item_done_type: Any = _SSE_OUTPUT_ITEM_DONE,
    completed_type: Any = _SSE_RESPONSE_COMPLETED,
) -> Optional[str]:
    """Repair an empty ``response.completed.output`` in a Codex SSE body.

    The Codex backend streams content via ``response.output_item.done`` events
    and sends a ``response.completed`` event whose ``output`` array is empty
    (upstream BerriAI/litellm#25429). This collects the done items and, if the
    completed event's ``output`` is empty, splices in the collapsed output (the
    single usable message — see :func:`_collapse_codex_output`). Returns the
    rewritten body, or ``None`` when there is nothing to fix. Pure string->string;
    safe to unit-test with synthetic SSE.
    """
    lines = body_text.splitlines()
    collected: list = []
    completed_idx = None
    completed_payload = None
    for idx, raw_line in enumerate(lines):
        stripped = _strip_sse_data(raw_line)
        if not stripped:
            continue
        stripped = stripped.strip()
        if not stripped or stripped == "[DONE]":
            continue
        try:
            parsed = json.loads(stripped)
        except (ValueError, TypeError):
            continue
        if not isinstance(parsed, dict):
            continue
        event_type = parsed.get("type")
        if event_type == item_done_type:
            item = parsed.get("item")
            if isinstance(item, dict):
                collected.append(item)
        elif event_type == completed_type:
            completed_idx = idx
            completed_payload = parsed
    if completed_idx is None or completed_payload is None or not collected:
        return None
    response_obj = completed_payload.get("response")
    if not isinstance(response_obj, dict) or response_obj.get("output"):
        return None  # nothing to fix — backend already populated output
    response_obj = dict(response_obj)
    response_obj["output"] = _collapse_codex_output(collected)
    completed_payload = dict(completed_payload)
    completed_payload["response"] = response_obj
    lines[completed_idx] = "data: " + json.dumps(completed_payload)
    return "\n".join(lines)


def apply_litellm_chatgpt_output_patch() -> bool:
    """Work around litellm's empty ``chatgpt/`` Responses output (upstream #25429).

    The Codex backend streams content via ``response.output_item.done`` SSE
    events and sends a ``response.completed`` event whose ``output`` array is
    empty. litellm's non-streaming parser only reads ``response.completed`` and
    therefore returns an empty response, which then crashes the chat-completions
    bridge with ``'ResponsesAPIResponse' object has no attribute 'output'``.

    This applies the fix from litellm PR #27562 without forking litellm: it
    wraps ``ChatGPTResponsesAPIConfig.transform_response_api_response`` so the
    collected ``output_item.done`` items are spliced into the completed event
    before litellm's own (version-correct) construction runs. Idempotent,
    version-gated, and never raises — a failure just leaves litellm untouched.

    Returns ``True`` if the patch is in place (already or newly applied).
    """
    try:
        from litellm.llms.chatgpt.responses import transformation as _t
    except Exception:
        return False

    cfg = getattr(_t, "ChatGPTResponsesAPIConfig", None)
    if cfg is None:
        return False
    if getattr(cfg, "_pdd_output_item_patch", False):
        return True
    if not hasattr(cfg, "transform_response_api_response"):
        return False

    try:
        from litellm.types.llms.openai import ResponsesAPIStreamEvents
        from litellm.utils import CustomStreamWrapper

        item_done = ResponsesAPIStreamEvents.OUTPUT_ITEM_DONE
        completed = ResponsesAPIStreamEvents.RESPONSE_COMPLETED
    except Exception:
        return False

    original = cfg.transform_response_api_response

    def patched(self, model, raw_response, logging_obj):  # noqa: ANN001
        # Splice logic lives in module-level splice_codex_output_into_sse() so it
        # is unit-testable with synthetic SSE (issue #1269). Pass the resolved
        # enum members so matching is identical to litellm's own event types.
        try:
            new_body = splice_codex_output_into_sse(
                raw_response.text or "", item_done_type=item_done, completed_type=completed
            )
        except Exception:  # pragma: no cover - defensive; fall back to original
            new_body = None
        if new_body is not None:
            raw_response = _RawResponseProxy(raw_response, new_body)
        return original(self, model, raw_response, logging_obj)

    try:
        cfg.transform_response_api_response = patched
        cfg._pdd_output_item_patch = True
    except Exception:  # pragma: no cover - defensive
        return False
    logger.debug("Applied litellm chatgpt/ empty-output workaround (PR #27562).")
    return True


def build_chatgpt_schema_instruction(schema: Dict[str, Any]) -> str:
    """Return a prompt instruction that coerces JSON output from the backend.

    The ChatGPT subscription backend ignores ``response_format`` / ``json_schema``
    (it returns prose), so structured output is enforced by instructing the
    model in-band, mirroring the existing Groq handling in ``llm_invoke``.
    """
    return (
        "\n\nYou must respond with a single valid JSON object matching this schema:\n"
        f"```json\n{json.dumps(schema, indent=2)}\n```\n"
        "Respond ONLY with the JSON object — no prose, no markdown fences, no commentary."
    )


def inject_chatgpt_schema_instruction(messages: Any, schema: Optional[Dict[str, Any]]) -> Any:
    """Inject the JSON-coercion instruction into a (non-batch) ``messages`` list.

    Appends :func:`build_chatgpt_schema_instruction` to an existing leading
    ``system`` message, else inserts a new ``system`` message. Returns the
    (mutated) list. No-op when ``schema`` is None or ``messages`` is empty / not a
    flat list of dicts. Used for BOTH the initial structured call and the
    retry/repair paths so a ``chatgpt/`` retry never loses the schema (issue
    #1269) — the subscription backend ignores ``response_format``, so the
    in-prompt schema is the only enforcement.
    """
    if schema is None or not isinstance(messages, list) or not messages:
        return messages
    first = messages[0]
    if not isinstance(first, dict):
        return messages
    instruction = build_chatgpt_schema_instruction(schema)
    if first.get("role") == "system":
        first["content"] = (first.get("content") or "") + instruction
    else:
        messages.insert(0, {"role": "system", "content": instruction})
    return messages
