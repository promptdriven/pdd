#!/usr/bin/env python
"""
Probe: can PDD use a ChatGPT/Codex *subscription* as an LLM provider via LiteLLM?

Context: issue #1269 (use codex subscription, reference openclaw) + #1254/#1135
(`pdd sync` fails in --force mode when ANTHROPIC_API_KEY is unavailable).
Goal: a Codex-subscription fallback when Anthropic is down.

Run:  /opt/anaconda3/bin/python _codex_subscription_probe.py
Requires: a local `codex login` (ChatGPT sign-in) so ~/.codex/auth.json exists.
This makes REAL calls billed to YOUR personal ChatGPT subscription (flat-rate).
Do NOT point this at a shared/pooled subscription — that is OpenAI-ToS grey/red.

Findings (litellm 1.82.6, PDD's pin; gpt-5.3-codex), 2026-05-29:
  * Auth works: ~/.codex/auth.json {tokens:{access_token,refresh_token,id_token,account_id}}
    must be shimmed to top-level for litellm's authenticator (CHATGPT_TOKEN_DIR).
  * litellm.completion() (PDD's path) on chatgpt/* returns EMPTY output on 1.82.6
    -> upstream bug BerriAI/litellm#25429 (filed 2026-05-29; still repro on 1.85.1).
    Root cause: codex backend sends output via `response.output_item.done` SSE events
    and an empty `response.completed.output`; litellm's non-stream parser misses it.
  * The 12-line additive fix from PR #27562 (monkey-patched below) makes completion()
    return real content.
  * BUT the subscription backend IGNORES json_schema/response_format (returns prose).
    Structured output must be PROMPT-COERCED ("return ONLY JSON ...") -> that works.
"""
import json
import os
import tempfile
import warnings

warnings.filterwarnings("ignore")

MODEL = os.environ.get("PROBE_MODEL", "chatgpt/gpt-5.3-codex")


def _shim_codex_auth() -> str:
    """Lift ~/.codex/auth.json's nested `tokens` to the top-level shape litellm wants.

    Returns a temp dir suitable for CHATGPT_TOKEN_DIR. Carries refresh_token so
    litellm can refresh if the access_token has expired.
    """
    src = os.path.expanduser("~/.codex/auth.json")
    data = json.load(open(src))
    tokens = data.get("tokens") or {}
    shimmed = {k: tokens.get(k) for k in ("access_token", "refresh_token", "id_token", "account_id")}
    if not shimmed["access_token"]:
        raise SystemExit("No access_token in ~/.codex/auth.json — run `codex login` first.")
    tmp = tempfile.mkdtemp(prefix="pdd_codex_probe_")
    json.dump(shimmed, open(os.path.join(tmp, "auth.json"), "w"))
    return tmp


def _apply_pr_27562_patch() -> None:
    """Monkey-patch litellm with PR #27562: aggregate output_item.done into completed.output."""
    import litellm  # noqa: F401
    from litellm.llms.chatgpt.responses import transformation as T
    from litellm.types.llms.openai import ResponsesAPIStreamEvents, ResponsesAPIResponse
    from litellm.litellm_core_utils.streaming_handler import CustomStreamWrapper
    from litellm.litellm_core_utils.llm_response_utils.convert_dict_to_response import (
        _safe_convert_created_field,
    )

    def transform_response_api_response(self, model, raw_response, logging_obj):
        collected: list = []
        completed = None
        for chunk in raw_response.text.splitlines():
            stripped = CustomStreamWrapper._strip_sse_data_from_chunk(chunk)
            if not stripped:
                continue
            try:
                parsed = json.loads(stripped)
            except Exception:
                continue
            if not isinstance(parsed, dict):
                continue
            event_type = parsed.get("type")
            if event_type == ResponsesAPIStreamEvents.OUTPUT_ITEM_DONE:
                item = parsed.get("item")
                if isinstance(item, dict):
                    collected.append(item)
                continue
            if event_type == ResponsesAPIStreamEvents.RESPONSE_COMPLETED:
                payload = parsed.get("response")
                if isinstance(payload, dict):
                    payload = dict(payload)
                    if not payload.get("output") and collected:
                        payload["output"] = collected
                    if "created_at" in payload:
                        payload["created_at"] = _safe_convert_created_field(payload["created_at"])
                    completed = ResponsesAPIResponse(**payload)
        if completed is None:
            raise ValueError("chatgpt: no response.completed event assembled")
        return completed

    T.ChatGPTResponsesAPIConfig.transform_response_api_response = transform_response_api_response


def main() -> None:
    os.environ["CHATGPT_TOKEN_DIR"] = _shim_codex_auth()
    _apply_pr_27562_patch()
    import litellm
    import importlib.metadata

    print(f"=== model: {MODEL} | litellm: {importlib.metadata.version('litellm')} ===\n")

    print("[1] completion() bridge, prompt-coerced JSON (the recommended PDD path):")
    r = litellm.completion(
        model=MODEL,
        messages=[{
            "role": "user",
            "content": "Return ONLY a JSON object with keys country, capital, "
                       "population_estimate (int), fun_fact for France. No prose, no markdown.",
        }],
    )
    content = r.choices[0].message.content
    cleaned = content.strip().removeprefix("```json").removeprefix("```").removesuffix("```").strip()
    parsed = json.loads(cleaned)
    print("    parsed:", parsed)
    print("    tokens:", getattr(r, "usage", None))
    print("\n✅ Subscription call works end-to-end (auth + patched bridge + prompt-coerced JSON).")


if __name__ == "__main__":
    main()
