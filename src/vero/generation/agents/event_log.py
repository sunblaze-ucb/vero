"""Event-log plumbing shared by every Agent backend.

Every agent emits a canonical stream of events during a run. We persist them two ways:

- ``agent_events.jsonl`` — one JSON object per line, structured, full fidelity, no truncation. This is the authoritative replay format.
- ``agent.log`` — human-readable line-per-event rendering, useful for ``tail -f`` while a run is in flight. Truncated content is fine here; callers can always fall back to the JSONL.

The logger is the ONLY place that should touch either file; individual agents just call ``log.*()``.

Event kinds carried by agents today:

- ``run_start`` — once per run; records agent name, model, turn budget, sandbox dir.
- ``thinking`` — agent chain-of-thought block (Claude-only today).
- ``text`` — agent's user-visible assistant message.
- ``tool_use`` — agent invoked a tool; carries tool name + input.
- ``tool_result`` — tool returned; carries error flag + content.
- ``raw`` — fall-through for backend-specific events we don't (yet) have a canonical shape for. Agents should prefer a specific kind when available.
- ``run_error`` — terminal error (exception during the run).
- ``run_end`` — once per run; summary (ok, turns, cost).

Downstream analysis scripts can rely on the jsonl schema being stable.
"""

from __future__ import annotations

import json
import traceback
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from loguru import logger


def _utc_iso() -> str:
    return (
        datetime.now(timezone.utc)
        .isoformat(timespec="milliseconds")
        .replace("+00:00", "Z")
    )


class EventLogger:
    """Persist full-fidelity events to a sandbox dir, plus a readable log."""

    def __init__(
        self,
        *,
        agent: str,
        sandbox_dir: Path,
        jsonl_name: str = "agent_events.jsonl",
        text_name: str = "agent.log",
        mirror_to_stderr: bool = True,
        text_truncate: int | None = 4000,
    ):
        self.agent = agent
        self.sandbox_dir = Path(sandbox_dir).resolve()
        self.sandbox_dir.mkdir(parents=True, exist_ok=True)
        self.jsonl_path = self.sandbox_dir / jsonl_name
        self.text_path = self.sandbox_dir / text_name
        self._jsonl_fh = self.jsonl_path.open("w", encoding="utf-8", buffering=1)
        self._text_fh = self.text_path.open("w", encoding="utf-8", buffering=1)
        self.mirror_to_stderr = mirror_to_stderr
        # ``None`` → no truncation. Used only for the human-readable mirror;
        # JSONL is always stored in full.
        self.text_truncate = text_truncate

    # ─── lifecycle ─────────────────────────────────────────────

    def close(self) -> None:
        try:
            self._jsonl_fh.close()
        finally:
            self._text_fh.close()

    def __enter__(self) -> "EventLogger":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        if exc is not None:
            self.log(
                "run_error",
                error_type=exc_type.__name__ if exc_type else "UnknownError",
                message=str(exc),
                traceback="".join(traceback.format_exception(exc_type, exc, tb)),
            )
        self.close()

    # ─── core emitter ──────────────────────────────────────────

    def log(self, kind: str, **payload: Any) -> None:
        """Write one event. ``payload`` is serialized verbatim."""
        event = {
            "ts": _utc_iso(),
            "agent": self.agent,
            "kind": kind,
            **payload,
        }
        # Authoritative JSONL — full content.
        try:
            line = json.dumps(event, ensure_ascii=False, default=_json_default)
        except (TypeError, ValueError):
            line = json.dumps(
                {**event, "payload_repr": repr(payload), "_json_fallback": True},
                ensure_ascii=False,
            )
        self._jsonl_fh.write(line + "\n")

        # Human-readable mirror.
        rendered = self._render(event)
        self._text_fh.write(rendered + "\n")
        if self.mirror_to_stderr:
            logger.info(rendered)

    # ─── convenience wrappers ──────────────────────────────────

    def run_start(self, **payload: Any) -> None:
        self.log("run_start", **payload)

    def run_end(self, **payload: Any) -> None:
        self.log("run_end", **payload)

    def thinking(self, text: str) -> None:
        self.log("thinking", text=text)

    def text(self, text: str) -> None:
        self.log("text", text=text)

    def tool_use(self, name: str, input: Any, *, id: str | None = None) -> None:
        self.log("tool_use", name=name, input=input, id=id)

    def tool_result(
        self, *, is_error: bool, content: Any, tool_use_id: str | None = None
    ) -> None:
        self.log(
            "tool_result",
            is_error=is_error,
            content=content,
            tool_use_id=tool_use_id,
        )

    def raw(self, **payload: Any) -> None:
        """Fall-through for backend-specific events (codex's `item_started` etc)."""
        self.log("raw", **payload)

    def error(self, message: str, **payload: Any) -> None:
        self.log("run_error", message=message, **payload)

    # ─── rendering ─────────────────────────────────────────────

    def _render(self, event: dict) -> str:
        kind = event["kind"]
        ts = event["ts"]
        body = {k: v for k, v in event.items() if k not in {"ts", "agent", "kind"}}
        # Per-kind compact renderings; everything else falls back to JSON.
        if kind == "thinking":
            return self._trim(f"[{ts}] [thinking] {body.get('text', '')}")
        if kind == "text":
            return self._trim(f"[{ts}] [text] {body.get('text', '')}")
        if kind == "tool_use":
            name = body.get("name", "?")
            tool_input = body.get("input", "")
            return self._trim(f"[{ts}] [tool_use] {name} input={tool_input}")
        if kind == "tool_result":
            is_err = body.get("is_error", False)
            content = body.get("content", "")
            tag = "ERR" if is_err else "ok"
            return self._trim(f"[{ts}] [tool_result:{tag}] {content}")
        if kind == "run_start":
            return f"[{ts}] [run_start] {json.dumps(body, default=_json_default)}"
        if kind == "run_end":
            return f"[{ts}] [run_end] {json.dumps(body, default=_json_default)}"
        if kind == "run_error":
            msg = body.get("message") or body.get("error_type", "")
            return self._trim(f"[{ts}] [run_error] {msg}")
        # raw / unknown kinds
        return self._trim(f"[{ts}] [{kind}] {json.dumps(body, default=_json_default)}")

    def _trim(self, s: str) -> str:
        if self.text_truncate is None or len(s) <= self.text_truncate:
            return s
        return s[: self.text_truncate] + f"… [+{len(s) - self.text_truncate} chars]"


def _json_default(o: Any) -> Any:
    """Best-effort JSON fallback for types we don't own (pydantic models, etc)."""
    if hasattr(o, "model_dump"):
        try:
            return o.model_dump()
        except Exception:  # noqa: BLE001
            pass
    if hasattr(o, "__dict__"):
        return {k: v for k, v in o.__dict__.items() if not k.startswith("_")}
    return repr(o)
