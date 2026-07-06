"""Agent callers for the curation pipeline.

Claude is the historical backend for this pipeline. Codex support is provided
through the local ``codex exec`` CLI so curation can run when Claude is not
available. Codex does not have Claude Code's native Skill tool, so stage skill
documents are inlined into the prompt before launch.
"""

from __future__ import annotations

import asyncio
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from claude_agent_sdk import (
    AssistantMessage,
    ClaudeAgentOptions,
    ResultMessage,
    TextBlock,
    ThinkingBlock,
    ToolResultBlock,
    ToolUseBlock,
    query,
)
from loguru import logger


def _find_repo_root() -> Path:
    """Walk up from this file to find the repo root (contains .claude/)."""
    cur = Path(__file__).resolve()
    for _ in range(10):
        cur = cur.parent
        if (cur / ".claude" / "skills").exists():
            return cur
    raise FileNotFoundError("Could not find repo root with .claude/skills/")


REPO_ROOT = _find_repo_root()
_CODEX_REASONING_EFFORTS = {"low", "medium", "high", "xhigh"}


def _ensure_skill_tool(tools: list[str]) -> list[str]:
    """Return ``tools`` with ``"Skill"`` appended if not already present."""
    if "Skill" in tools:
        return tools
    return [*tools, "Skill"]


def build_lean_mcp_servers(lean_project_path: str | None = None) -> dict:
    """Build MCP server configs for Lean tooling.

    Returns a dict suitable for ``ClaudeAgentOptions.mcp_servers``.
    """
    servers: dict = {}

    lsp_args = ["lean-lsp-mcp"]
    if lean_project_path:
        lsp_args.extend(["--lean-project-path", lean_project_path])
    servers["lean-lsp"] = {
        "type": "stdio",
        "command": "uvx",
        "args": lsp_args,
    }

    servers["lean-explore"] = {
        "type": "stdio",
        "command": "uvx",
        "args": ["lean-explore", "mcp", "serve"],
    }

    return servers


async def call_agent(
    *,
    model: str,
    permission_mode: str,
    prompt: str,
    tools: list[str],
    max_turns: int,
    resume_session_id: str | None = None,
    api_key: str | None = None,
    api_base_url: str | None = None,
    mcp_servers: dict | None = None,
    agent_kind: str = "claude",
    codex_auth_mode: str = "api",
    codex_sandbox_mode: str = "danger-full-access",
    codex_timeout_seconds: int = 1800,
    codex_network_access: bool = False,
    codex_model_reasoning_effort: str | None = None,
) -> tuple[list[str], str | None]:
    """Call the configured curation agent backend.

    Returns (text_responses, session_id). ``agent_kind="claude"`` preserves the
    original Claude Agent SDK behavior. ``agent_kind="codex"`` runs ``codex
    exec`` and inlines any referenced curation skills into the prompt.
    """

    if agent_kind == "claude":
        return await _call_claude_agent(
            model=model,
            permission_mode=permission_mode,
            prompt=prompt,
            tools=tools,
            max_turns=max_turns,
            resume_session_id=resume_session_id,
            api_key=api_key,
            api_base_url=api_base_url,
            mcp_servers=mcp_servers,
        )
    if agent_kind == "codex":
        return await _call_codex_agent(
            model=model,
            permission_mode=permission_mode,
            prompt=prompt,
            tools=tools,
            max_turns=max_turns,
            resume_session_id=resume_session_id,
            api_key=api_key,
            api_base_url=api_base_url,
            mcp_servers=mcp_servers,
            codex_auth_mode=codex_auth_mode,
            codex_sandbox_mode=codex_sandbox_mode,
            codex_timeout_seconds=codex_timeout_seconds,
            codex_network_access=codex_network_access,
            codex_model_reasoning_effort=codex_model_reasoning_effort,
        )
    raise ValueError(f"unsupported curation agent_kind: {agent_kind!r}")


async def _call_claude_agent(
    *,
    model: str,
    permission_mode: str,
    prompt: str,
    tools: list[str],
    max_turns: int,
    resume_session_id: str | None = None,
    api_key: str | None = None,
    api_base_url: str | None = None,
    mcp_servers: dict | None = None,
) -> tuple[list[str], str | None]:
    """Call the Claude Agent SDK."""
    system_prompt: dict = {"type": "preset", "preset": "claude_code"}

    # When running inside an active Claude Code session, the inherited
    # CLAUDE_CODE_* env vars cause the nested SDK subprocess to refuse to
    # launch. Pop them for the duration of this call.
    _leaked = (
        "CLAUDECODE",
        "CLAUDE_CODE_ENTRYPOINT",
        "CLAUDE_CODE_SSE_PORT",
        "CLAUDE_CODE_OAUTH_TOKEN",
    )
    _env_to_restore = ("HOME",)
    _saved: dict[str, str] = {}
    for k in _leaked:
        v = os.environ.pop(k, None)
        if v is not None:
            _saved[k] = v
    for k in _env_to_restore:
        v = os.environ.get(k)
        if v is not None:
            _saved[k] = v

    env: dict[str, str] = {}
    isolated_home: Path | None = None
    if api_key:
        env["ANTHROPIC_API_KEY"] = api_key
        env["ANTHROPIC_AUTH_TOKEN"] = api_key
        os.environ["ANTHROPIC_API_KEY"] = api_key
        os.environ["ANTHROPIC_AUTH_TOKEN"] = api_key
        isolated_home = Path(tempfile.mkdtemp(prefix="claude-api-key-home-"))
        (isolated_home / ".claude").mkdir()
        env["HOME"] = str(isolated_home)
        os.environ["HOME"] = str(isolated_home)
    if api_base_url:
        env["ANTHROPIC_BASE_URL"] = api_base_url
        os.environ["ANTHROPIC_BASE_URL"] = api_base_url

    env["CLAUDE_CODE_DISABLE_EXPERIMENTAL_BETAS"] = "1"
    env["ENABLE_TOOL_SEARCH"] = "0"
    os.environ["CLAUDE_CODE_DISABLE_EXPERIMENTAL_BETAS"] = "1"
    os.environ["ENABLE_TOOL_SEARCH"] = "0"
    env.setdefault("CLAUDE_CODE_MAX_OUTPUT_TOKENS", "65536")
    os.environ.setdefault("CLAUDE_CODE_MAX_OUTPUT_TOKENS", "65536")

    allowed_tools = _ensure_skill_tool(tools)

    env.setdefault("MAX_THINKING_TOKENS", "32000")
    os.environ.setdefault("MAX_THINKING_TOKENS", "32000")
    options = ClaudeAgentOptions(
        system_prompt=system_prompt,
        max_turns=max_turns,
        allowed_tools=allowed_tools,
        permission_mode=permission_mode,
        cwd=str(REPO_ROOT),
        model=model,
        resume=resume_session_id,
        env=env,
        mcp_servers=mcp_servers or {},
        setting_sources=["project"],
        thinking={"type": "enabled", "budget_tokens": 32000},
    )

    action = "Resuming" if resume_session_id else "Calling"
    logger.info(
        f"{action} Claude agent: tools={allowed_tools}, "
        f"model={model}, max_turns={max_turns}, cwd={REPO_ROOT}"
    )

    texts: list[str] = []
    session_id: str | None = None

    try:
        async for message in query(prompt=prompt, options=options):
            if isinstance(message, AssistantMessage):
                for block in message.content:
                    if isinstance(block, TextBlock):
                        texts.append(block.text)
                        logger.info("[text] {}", block.text)
                    elif isinstance(block, ThinkingBlock):
                        logger.debug("[thinking] {}", block.thinking)
                    elif isinstance(block, ToolUseBlock):
                        logger.info("[tool_use] {} | input={}", block.name, block.input)
                    elif isinstance(block, ToolResultBlock):
                        logger.info(
                            "[tool_result] id={} error={} | {}",
                            block.tool_use_id,
                            block.is_error,
                            block.content,
                        )
            elif isinstance(message, ResultMessage):
                session_id = message.session_id
                logger.info(
                    f"Agent finished: turns={message.num_turns}, "
                    f"session_id={session_id}, is_error={message.is_error}"
                )
    finally:
        for k, v in _saved.items():
            os.environ[k] = v
        if isolated_home is not None and isolated_home.exists():
            shutil.rmtree(isolated_home, ignore_errors=True)

    return texts, session_id


async def _call_codex_agent(
    *,
    model: str,
    permission_mode: str,
    prompt: str,
    tools: list[str],
    max_turns: int,
    resume_session_id: str | None = None,
    api_key: str | None = None,
    api_base_url: str | None = None,
    mcp_servers: dict | None = None,
    codex_auth_mode: str = "api",
    codex_sandbox_mode: str = "danger-full-access",
    codex_timeout_seconds: int = 1800,
    codex_network_access: bool = False,
    codex_model_reasoning_effort: str | None = None,
) -> tuple[list[str], str | None]:
    """Call Codex CLI as a curation backend."""

    del permission_mode, tools, max_turns

    if mcp_servers:
        logger.warning(
            "Codex curation backend ignores Claude MCP servers; prompts should use "
            "`lake env lean`/`lake build` directly for Lean checks."
        )

    command = _build_codex_command(
        model=model,
        sandbox_mode=codex_sandbox_mode,
        network_access=codex_network_access,
        model_reasoning_effort=codex_model_reasoning_effort,
    )
    env, temp_home = _build_codex_env(
        auth_mode=codex_auth_mode,
        api_key=api_key,
        api_base_url=api_base_url,
    )
    full_prompt = _build_codex_prompt(
        prompt=prompt,
        resume_session_id=resume_session_id,
        mcp_servers=bool(mcp_servers),
    )

    action = "Resuming" if resume_session_id else "Calling"
    logger.info(
        "{} Codex agent: auth_mode={}, model={}, sandbox={}, reasoning_effort={}, cwd={}, timeout={}s",
        action,
        codex_auth_mode,
        model or "(codex default)",
        codex_sandbox_mode,
        codex_model_reasoning_effort,
        REPO_ROOT,
        codex_timeout_seconds,
    )

    try:
        return await asyncio.to_thread(
            _run_codex_process,
            command=command,
            prompt=full_prompt,
            env=env,
            timeout_seconds=codex_timeout_seconds,
        )
    finally:
        if temp_home is not None:
            shutil.rmtree(temp_home, ignore_errors=True)


def _build_codex_command(
    *,
    model: str,
    sandbox_mode: str,
    network_access: bool,
    model_reasoning_effort: str | None = None,
) -> list[str]:
    codex_bin = shutil.which("codex")
    if codex_bin is None:
        raise FileNotFoundError("codex CLI not found on PATH")

    cmd = [
        codex_bin,
        "exec",
        "--json",
        "--skip-git-repo-check",
        "--cd",
        str(REPO_ROOT.parent),
    ]
    if sandbox_mode == "workspace-write":
        cmd.append("--full-auto")
        if network_access:
            cmd.extend(["-c", "sandbox_workspace_write.network_access=true"])
    elif sandbox_mode == "read-only":
        cmd.extend(["--sandbox", "read-only"])
    elif sandbox_mode == "danger-full-access":
        cmd.append("--dangerously-bypass-approvals-and-sandbox")
    else:
        raise ValueError(f"unsupported codex_sandbox_mode: {sandbox_mode!r}")

    if model.strip():
        cmd.extend(["-m", model.strip()])
    if model_reasoning_effort is not None:
        effort = model_reasoning_effort.strip()
        if effort and effort not in _CODEX_REASONING_EFFORTS:
            raise ValueError(f"unsupported codex_model_reasoning_effort: {effort!r}")
        if effort:
            cmd.extend(["-c", f'model_reasoning_effort="{effort}"'])
    cmd.append("-")
    return cmd


def _build_codex_env(
    *,
    auth_mode: str,
    api_key: str | None,
    api_base_url: str | None,
) -> tuple[dict[str, str], Path | None]:
    env = os.environ.copy()
    temp_home: Path | None = None

    if auth_mode == "local":
        # Local subscription mode must not inherit drained proxy/API keys.
        source_codex_home = _local_codex_home_from_env(env)
        for key in (
            "CODEX_API_KEY",
            "OPENAI_API_KEY",
            "CODEX_HOME",
            "CODEX_AGENT_API_KEY",
            "CODEX_AGENT_BASE_URL",
            "LLM_API_KEY",
            "LLM_API_BASE",
            "ANTHROPIC_API_KEY",
            "ANTHROPIC_AUTH_TOKEN",
            "ANTHROPIC_BASE_URL",
            "CLAUDE_API_KEY",
            "CLAUDE_CODE_OAUTH_TOKEN",
        ):
            env.pop(key, None)
        local_home = _copy_local_codex_home(source_codex_home)
        if local_home is not None:
            env["CODEX_HOME"] = str(local_home)
            temp_home = local_home
        return env, temp_home

    if auth_mode != "api":
        raise ValueError(f"unsupported codex_auth_mode: {auth_mode!r}")

    resolved_key = (
        api_key
        or env.get("CODEX_AGENT_API_KEY")
        or env.get("LLM_API_KEY")
        or env.get("OPENAI_API_KEY")
    )
    if not resolved_key:
        raise ValueError(
            "codex_auth_mode='api' requires api_key, CODEX_AGENT_API_KEY, "
            "LLM_API_KEY, or OPENAI_API_KEY"
        )

    temp_home = Path(tempfile.mkdtemp(prefix="codex-curation-home-"))
    env["CODEX_HOME"] = str(temp_home)
    env["CODEX_API_KEY"] = resolved_key
    env["OPENAI_API_KEY"] = resolved_key
    (temp_home / "auth.json").write_text(
        json.dumps({"OPENAI_API_KEY": resolved_key}),
        encoding="utf-8",
    )

    base_url = (
        api_base_url or env.get("CODEX_AGENT_BASE_URL") or env.get("LLM_API_BASE")
    )
    if base_url:
        (temp_home / "config.toml").write_text(
            "\n".join(
                [
                    'model_provider = "litellm"',
                    "",
                    "[model_providers.litellm]",
                    'name = "LiteLLM"',
                    f'base_url = "{base_url.rstrip("/")}/v1"',
                    'env_key = "OPENAI_API_KEY"',
                    "",
                ]
            ),
            encoding="utf-8",
        )
    return env, temp_home


def _local_codex_home_from_env(env: dict[str, str]) -> Path | None:
    configured = env.get("CODEX_HOME")
    if configured:
        return Path(configured).expanduser()
    home = env.get("HOME")
    if not home:
        return None
    return Path(home).expanduser() / ".codex"


def _copy_local_codex_home(source_home: Path | None) -> Path | None:
    """Copy local Codex auth/config into a writable temporary CODEX_HOME.

    Nested curation executors can run inside a Codex sandbox where the user's
    normal home is readable enough for auth but not writable enough for Codex's
    app-server/runtime state. A temporary CODEX_HOME preserves local login while
    giving the CLI a writable runtime directory.
    """

    if source_home is None or not source_home.exists():
        return None

    temp_home = Path(tempfile.mkdtemp(prefix="codex-curation-local-home-"))
    copied = False
    for rel in ("auth.json", "config.toml", "version.json", "models_cache.json"):
        src = source_home / rel
        if src.is_file():
            shutil.copy2(src, temp_home / rel)
            copied = True
    rules_src = source_home / "rules"
    if rules_src.is_dir():
        shutil.copytree(rules_src, temp_home / "rules", dirs_exist_ok=True)
        copied = True
    if not copied:
        shutil.rmtree(temp_home, ignore_errors=True)
        return None
    return temp_home


def _build_codex_prompt(
    *,
    prompt: str,
    resume_session_id: str | None,
    mcp_servers: bool,
) -> str:
    skills = _collect_referenced_skills(prompt)
    parts: list[str] = [
        "You are running as the Codex backend for the repo-level VCG curation pipeline.",
        "Claude Code Skill documents referenced by the stage are inlined below; do not try to invoke a Skill tool.",
        "Use the filesystem and shell tools available to Codex to complete the stage exactly as requested.",
        "Codex shell commands in this environment are non-interactive. Do not run commands that require stdin after launch, such as `python -`, `cat > file`, REPLs, or commands followed by a separate stdin write. Prefer `python -c '...'`, existing scripts, direct file edits, or fully self-contained `bash -lc` one-liners.",
    ]
    if resume_session_id:
        parts.append(
            "A previous Claude/Codex session id was recorded, but Codex curation "
            "resumes from files on disk. Inspect the workspace and continue from "
            "the current artifacts."
        )
    if mcp_servers:
        parts.append(
            "Lean MCP tools are not attached in Codex mode. Use `lake env lean`, "
            "`lake build`, and scoped shell commands for validation."
        )
    if skills:
        parts.append("\n## Inlined Curation Skills")
        for name, content in skills:
            parts.append(f"\n### {name}\n\n{content}")
    parts.append("\n## Stage Prompt\n\n" + prompt)
    return "\n\n".join(parts)


def _collect_referenced_skills(prompt: str) -> list[tuple[str, str]]:
    skill_names = set(re.findall(r"`(vero-[A-Za-z0-9_-]+)`", prompt))
    skill_names.update(re.findall(r"\b(vero-[A-Za-z0-9_-]+)\b", prompt))
    results: list[tuple[str, str]] = []
    for name in sorted(skill_names):
        path = REPO_ROOT / ".claude" / "skills" / name / "SKILL.md"
        if not path.exists():
            continue
        try:
            content = path.read_text(encoding="utf-8")
        except OSError as exc:
            logger.warning("Could not read skill {} at {}: {}", name, path, exc)
            continue
        results.append((name, content))
    return results


def _run_codex_process(
    *,
    command: list[str],
    prompt: str,
    env: dict[str, str],
    timeout_seconds: int,
) -> tuple[list[str], str | None]:
    stderr_lines: list[str] = []
    stdout_lines: list[str] = []
    texts: list[str] = []
    session_id: str | None = None
    last_error: str | None = None

    proc = subprocess.Popen(
        command,
        cwd=str(REPO_ROOT),
        env=env,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )

    try:
        stdout, stderr = proc.communicate(
            input=prompt,
            timeout=timeout_seconds if timeout_seconds > 0 else None,
        )
    except subprocess.TimeoutExpired as exc:
        proc.kill()
        stdout, stderr = proc.communicate()
        stdout_lines.extend((stdout or "").splitlines())
        stderr_lines.extend((stderr or "").splitlines())
        for line in stderr_lines:
            logger.debug("[codex stderr] {}", line)
        raise TimeoutError(f"Codex agent timed out after {timeout_seconds}s") from exc

    stdout_lines.extend((stdout or "").splitlines())
    stderr_lines.extend((stderr or "").splitlines())
    for line in stderr_lines:
        logger.debug("[codex stderr] {}", line)
    for line in stdout_lines:
        event = _parse_codex_event(line)
        if event is not None:
            maybe_session_id = _extract_codex_session_id(event)
            if maybe_session_id:
                session_id = maybe_session_id
            text = _extract_codex_text(event)
            if text:
                texts.append(text)
                logger.info("[codex text] {}", text)
            error = _extract_codex_error(event)
            if error:
                last_error = error
                logger.warning("[codex error] {}", error)

    return_code = proc.returncode
    if return_code != 0:
        tail = "\n".join(stderr_lines[-40:] or stdout_lines[-40:])
        detail = last_error or tail or f"exit code {return_code}"
        raise RuntimeError(
            f"Codex agent failed with exit code {return_code}:\n{detail}"
        )

    logger.info("Codex agent finished: session_id={}", session_id)
    return texts, session_id


def _parse_codex_event(line: str) -> dict[str, Any] | None:
    try:
        event = json.loads(line)
    except json.JSONDecodeError:
        logger.debug("[codex stdout] {}", line)
        return None
    return event if isinstance(event, dict) else None


def _extract_codex_session_id(event: dict[str, Any]) -> str | None:
    if event.get("type") == "thread.started":
        thread_id = event.get("thread_id")
        return str(thread_id) if thread_id else None
    for key in ("session_id", "thread_id", "conversation_id"):
        value = event.get(key)
        if value:
            return str(value)
    return None


def _extract_codex_text(event: dict[str, Any]) -> str:
    item = event.get("item")
    if isinstance(item, dict) and item.get("type") == "agent_message":
        text = item.get("text")
        if isinstance(text, str) and text:
            return text
    msg = event.get("msg")
    if isinstance(msg, dict):
        message = msg.get("message")
        if isinstance(message, str) and message:
            return message
        content = msg.get("content")
        if isinstance(content, str) and content:
            return content
    for key in ("text", "message", "content"):
        value = event.get(key)
        if isinstance(value, str) and value:
            return value
    return ""


def _extract_codex_error(event: dict[str, Any]) -> str:
    if event.get("type") != "error":
        return ""
    error = event.get("error")
    if isinstance(error, str):
        return error
    if isinstance(error, dict):
        return json.dumps(error, ensure_ascii=False)
    return json.dumps(event, ensure_ascii=False)
