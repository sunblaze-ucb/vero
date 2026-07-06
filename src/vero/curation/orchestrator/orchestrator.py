"""Translation orchestrator — launches the orchestrator agent.

The Python harness sets up the workspace, builds the orchestrator prompt,
and calls ``call_agent()`` with access to both standard tools and custom
orchestration tools (available via Bash → dispatch.py).
"""

from __future__ import annotations

from pathlib import Path

from loguru import logger

from vero.curation.orchestrator.models import OrchestratorState
from vero.curation.orchestrator.prompt import build_orchestrator_prompt
from vero.curation.orchestrator.tools import load_state, save_state
from vero.curation.stages.base import StageContext


class TranslationOrchestrator:
    """Launches the orchestrator agent for the translate stage."""

    def __init__(
        self,
        ctx: StageContext,
        project_dir: Path,
        max_concurrent: int = 4,
        max_retries: int = 2,
    ) -> None:
        self.ctx = ctx
        self.project_dir = project_dir
        self.max_concurrent = max_concurrent
        self.max_retries = max_retries

    async def run(self) -> OrchestratorState:
        """Run the orchestrator agent."""
        from vero.curation.agent import build_lean_mcp_servers, call_agent

        config = self.ctx.config
        workspace = config.workspace

        # Initialize state
        state = load_state(workspace)
        save_state(workspace, state)

        language = config.source_language.value if config.source_language else "dafny"

        prompt = build_orchestrator_prompt(
            workspace=workspace,
            project_dir=self.project_dir,
            source_dir=self.ctx.source_dir,
            language=language,
            max_concurrent=self.max_concurrent,
        )

        mcp_servers = None
        if config.enable_lean_mcp:
            mcp_servers = build_lean_mcp_servers(str(self.project_dir))

        logger.info(
            f"[orchestrator] Starting orchestrator agent "
            f"(project={self.project_dir}, max_concurrent={self.max_concurrent})"
        )

        _, session_id = await call_agent(
            model=config.model,
            permission_mode=config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
            max_turns=config.max_turns_orchestrator,
            api_key=config.api_key,
            api_base_url=config.api_base_url,
            mcp_servers=mcp_servers,
            **config.agent_kwargs,
        )

        # Reload state after orchestrator finishes
        state = load_state(workspace)

        logger.info(
            f"[orchestrator] Finished: "
            f"{len(state.completed)}/{len(state.units)} modules completed, "
            f"{len(state.failed)} failed"
        )

        return state
