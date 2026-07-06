"""GenerationRunner — orchestrate sandbox creation, agent run, artifact extract."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from loguru import logger

from vero.generation.agents.base import Agent, AgentResult, create_agent
from vero.generation.benchmark import Benchmark
from vero.generation.extractor import Artifact, extract, write_artifact
from vero.generation.sandbox import SandboxResult, create_sandbox

Mode = Literal["proof", "codeproof"]


@dataclass
class GenerationResult:
    sandbox: SandboxResult
    agent: AgentResult
    artifact: Artifact
    artifact_path: Path


def run_generation(
    benchmark_dir: Path,
    sandbox_dir: Path,
    *,
    mode: Mode,
    agent: Agent | None = None,
    agent_kind: str = "claude",
    model: str | None = None,
    max_turns: int = 40,
    overwrite: bool = False,
) -> GenerationResult:
    """Build a sandbox, run the agent, extract artifacts. Returns the full result."""
    logger.info("creating sandbox at {}", sandbox_dir)
    bench = Benchmark(Path(benchmark_dir).resolve())
    sandbox = create_sandbox(benchmark_dir, sandbox_dir, mode=mode, overwrite=overwrite)

    if agent is None:
        agent = create_agent(agent_kind, model=model, max_turns=max_turns)

    logger.info(
        "running agent {} (model={}) in sandbox {}",
        agent.name,
        getattr(agent, "model", "?"),
        sandbox.sandbox_dir,
    )
    agent_result = agent.run(
        sandbox_dir=sandbox.sandbox_dir,
        instruction_file=sandbox.instruction_file,
    )
    logger.info(
        "agent finished: ok={} turns={} cost={}",
        agent_result.ok,
        agent_result.num_turns,
        agent_result.total_cost_usd,
    )

    artifact = extract(sandbox.sandbox_dir, bench, mode=mode)
    artifact_path = sandbox.sandbox_dir / "artifact.json"
    write_artifact(artifact, artifact_path)
    logger.info(
        "wrote artifact with {} slots to {}", len(artifact.slots), artifact_path
    )

    return GenerationResult(
        sandbox=sandbox,
        agent=agent_result,
        artifact=artifact,
        artifact_path=artifact_path,
    )
