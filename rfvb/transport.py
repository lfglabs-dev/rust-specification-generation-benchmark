"""Minimal OpenAI-compatible chat-completions transport with retries."""
from __future__ import annotations

import json
import time
import urllib.error
import urllib.request
from dataclasses import dataclass


@dataclass
class ChatConfig:
    base_url: str
    model: str
    api_key: str | None = None
    temperature: float | None = 0.0
    max_tokens: int = 16384
    timeout: int = 600
    retries: int = 6
    backoff: float = 5.0
    extra_body: dict | None = None
    stream: bool = False  # SSE streaming: keeps proxies with idle timeouts (e.g. 100 s) from cutting long generations


class TransportError(RuntimeError):
    pass


def chat(cfg: ChatConfig, messages: list[dict], tools: list[dict] | None = None) -> dict:
    body = {"model": cfg.model, "messages": messages, "max_tokens": cfg.max_tokens}
    if cfg.temperature is not None:
        body["temperature"] = cfg.temperature
    if tools:
        body["tools"] = tools
        body["tool_choice"] = "auto"
    if cfg.extra_body:
        body.update(cfg.extra_body)
    if cfg.stream:
        body["stream"] = True
        body["stream_options"] = {"include_usage": True}
    data = json.dumps(body).encode("utf-8")
    headers = {"Content-Type": "application/json", "User-Agent": "rfvb/1.0"}
    if cfg.api_key:
        headers["Authorization"] = f"Bearer {cfg.api_key}"
    url = cfg.base_url.rstrip("/") + "/chat/completions"
    last = None
    for attempt in range(cfg.retries + 1):
        req = urllib.request.Request(url, data=data, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=cfg.timeout) as resp:
                if cfg.stream:
                    return _read_stream(resp)
                return json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", "replace")[:2000]
            last = f"HTTP {exc.code}: {detail}"
            overflow = any(k in detail.lower() for k in ("context", "maximum", "too long", "too many tokens"))
            if exc.code in (401, 403, 404, 422) or (exc.code == 400 and overflow):
                # context overflow / bad request: not retryable
                raise TransportError(last) from exc
            # other 400s seen from gateways (e.g. an empty upstream reply that the
            # proxy fails to parse) are transient: retry them like 5xx
        except (urllib.error.URLError, TimeoutError, ConnectionError, json.JSONDecodeError) as exc:
            last = f"{type(exc).__name__}: {exc}"
        time.sleep(cfg.backoff * (2 ** attempt))
    raise TransportError(f"request failed after {cfg.retries + 1} attempts: {last}")


def _read_stream(resp) -> dict:
    """Assemble an SSE chat-completions stream into a non-streaming response dict."""
    content, reasoning, calls, usage, finish, model = [], [], {}, None, None, None
    for raw in resp:
        line = raw.decode("utf-8", "replace").strip()
        if not line.startswith("data:"):
            continue
        payload = line[5:].strip()
        if payload == "[DONE]":
            break
        chunk = json.loads(payload)
        model = chunk.get("model") or model
        if chunk.get("usage"):
            usage = chunk["usage"]
        for ch in chunk.get("choices") or []:
            d = ch.get("delta") or {}
            if d.get("content"):
                content.append(d["content"])
            r = d.get("reasoning_content") or d.get("reasoning")
            if isinstance(r, str) and r:
                reasoning.append(r)
            for tc in d.get("tool_calls") or []:
                idx = tc.get("index")
                if idx is None:  # e.g. Gemini: whole calls without an index; a new id starts a new call
                    idx = next((i for i, c in calls.items() if tc.get("id") and c["id"] == tc.get("id")), None)
                    if idx is None:
                        idx = len(calls) if (tc.get("id") or not calls) else max(calls)
                slot = calls.setdefault(idx, {"id": None, "type": "function", "function": {"name": "", "arguments": ""}})
                if tc.get("id"):
                    slot["id"] = tc["id"]
                for key, val in tc.items():  # provider extensions, e.g. Gemini's extra_content.google.thought_signature
                    if key not in ("index", "id", "type", "function") and val is not None:
                        slot[key] = val
                f = tc.get("function") or {}
                if f.get("name"):
                    slot["function"]["name"] += f["name"]
                if f.get("arguments"):
                    slot["function"]["arguments"] += f["arguments"]
            if ch.get("finish_reason"):
                finish = ch["finish_reason"]
    if finish is None and not content and not calls:
        raise json.JSONDecodeError("stream ended without a completion", "", 0)
    msg = {"role": "assistant", "content": "".join(content) or None}
    if reasoning:
        msg["reasoning_content"] = "".join(reasoning)
    if calls:
        msg["tool_calls"] = [calls[i] for i in sorted(calls)]
    return {"model": model, "choices": [{"index": 0, "message": msg, "finish_reason": finish}], "usage": usage}
