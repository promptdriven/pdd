import type { PipelineStage, StageStatus } from "@/lib/types";

export type PipelineRunStepId =
  | "setup"
  | "tts-script"
  | "tts-render"
  | "audio-sync"
  | "specs"
  | "veo"
  | "compositions"
  | "render"
  | "stitch"
  | "audit";

export type PipelineRunStep = {
  id: PipelineRunStepId;
  label: string;
  stage: PipelineStage;
  mode: "setup" | "sse" | "job" | "sync";
  endpoint: string;
  body?: Record<string, unknown>;
};

export type PipelineStageStatusEntry = {
  status: StageStatus;
  error?: string | null;
  lastJobId?: string | null;
  updatedAt?: string | null;
};

export type PipelineRenderStatusSnapshot = {
  fullVideo?: {
    exists: boolean;
    stale?: boolean;
    updatedAtMs?: number;
  };
};

const PIPELINE_RUN_SEQUENCE: PipelineRunStep[] = [
  {
    id: "setup",
    label: "Extract Sections",
    stage: "setup",
    mode: "setup",
    endpoint: "/api/pipeline/setup/extract-sections",
  },
  {
    id: "tts-script",
    label: "Generate TTS Script",
    stage: "tts-script",
    mode: "sse",
    endpoint: "/api/pipeline/tts-script/run",
  },
  {
    id: "tts-render",
    label: "Render Audio",
    stage: "tts-render",
    mode: "sse",
    endpoint: "/api/pipeline/tts-render/run",
  },
  {
    id: "audio-sync",
    label: "Run Audio Sync",
    stage: "audio-sync",
    mode: "sse",
    endpoint: "/api/pipeline/audio-sync/run",
  },
  {
    id: "specs",
    label: "Generate Specs",
    stage: "specs",
    mode: "sse",
    endpoint: "/api/pipeline/specs/run",
  },
  {
    id: "veo",
    label: "Generate Veo Clips",
    stage: "veo",
    mode: "sse",
    endpoint: "/api/pipeline/veo/run",
  },
  {
    id: "compositions",
    label: "Generate Compositions",
    stage: "compositions",
    mode: "sse",
    endpoint: "/api/pipeline/compositions/run",
  },
  {
    id: "render",
    label: "Render Sections",
    stage: "render",
    mode: "job",
    endpoint: "/api/pipeline/render/run",
  },
  {
    id: "stitch",
    label: "Stitch Full Video",
    stage: "render",
    mode: "sync",
    endpoint: "/api/pipeline/stitch/run",
  },
  {
    id: "audit",
    label: "Audit All Sections",
    stage: "audit",
    mode: "sse",
    endpoint: "/api/pipeline/audit/run",
  },
];

const START_STEP_BY_STAGE: Record<PipelineStage, PipelineRunStepId> = {
  setup: "setup",
  script: "tts-script",
  "tts-script": "tts-script",
  "tts-render": "tts-render",
  "audio-sync": "audio-sync",
  specs: "specs",
  veo: "veo",
  compositions: "compositions",
  render: "render",
  audit: "audit",
};

const STAGE_LABELS: Record<PipelineStage, string> = {
  setup: "Setup",
  script: "Script",
  "tts-script": "TTS Script",
  "tts-render": "TTS Render",
  "audio-sync": "Audio Sync",
  specs: "Specs",
  veo: "Veo",
  compositions: "Compositions",
  render: "Render",
  audit: "Audit",
};

const STEP_DEPENDENCIES: Record<PipelineRunStepId, PipelineRunStepId[]> = {
  setup: [],
  "tts-script": ["setup"],
  "tts-render": ["tts-script"],
  "audio-sync": ["tts-render"],
  specs: ["tts-script", "audio-sync"],
  veo: ["specs"],
  compositions: ["audio-sync", "specs", "veo"],
  render: ["compositions"],
  stitch: ["render"],
  audit: ["render"],
};

function toTimestampMs(value: string | number | null | undefined): number | null {
  if (typeof value === "number" && Number.isFinite(value)) {
    return value;
  }

  if (typeof value !== "string" || value.trim().length === 0) {
    return null;
  }

  const parsed = Date.parse(value);
  return Number.isNaN(parsed) ? null : parsed;
}

function getStepUpdatedAtMs(
  step: PipelineRunStep,
  stageStatuses?: Partial<Record<PipelineStage, PipelineStageStatusEntry>>,
  renderStatus?: PipelineRenderStatusSnapshot | null
): number | null {
  if (step.id === "stitch") {
    return toTimestampMs(renderStatus?.fullVideo?.updatedAtMs);
  }

  return toTimestampMs(stageStatuses?.[step.stage]?.updatedAt);
}

function isStepStale(
  step: PipelineRunStep,
  stageStatuses?: Partial<Record<PipelineStage, PipelineStageStatusEntry>>,
  renderStatus?: PipelineRenderStatusSnapshot | null
): boolean {
  const dependencyIds = STEP_DEPENDENCIES[step.id];
  if (!dependencyIds.length) {
    return false;
  }

  const currentUpdatedAtMs = getStepUpdatedAtMs(step, stageStatuses, renderStatus);

  return dependencyIds.some((dependencyId) => {
    const dependencyStep = PIPELINE_RUN_SEQUENCE.find((candidate) => candidate.id === dependencyId);
    if (!dependencyStep) {
      return false;
    }

    const dependencyUpdatedAtMs = getStepUpdatedAtMs(
      dependencyStep,
      stageStatuses,
      renderStatus
    );
    if (dependencyUpdatedAtMs == null) {
      return false;
    }

    if (currentUpdatedAtMs == null) {
      return true;
    }

    return dependencyUpdatedAtMs > currentUpdatedAtMs;
  });
}

function isStepAlreadyDone(
  step: PipelineRunStep,
  stageStatuses?: Partial<Record<PipelineStage, PipelineStageStatusEntry>>,
  renderStatus?: PipelineRenderStatusSnapshot | null
): boolean {
  if (step.id === "stitch") {
    if (!renderStatus?.fullVideo?.exists || renderStatus.fullVideo?.stale) {
      return false;
    }

    return !isStepStale(step, stageStatuses, renderStatus);
  }

  if (stageStatuses?.[step.stage]?.status !== "done") {
    return false;
  }

  return !isStepStale(step, stageStatuses, renderStatus);
}

export function resolvePipelineRunPlan(
  activeStage: PipelineStage,
  options?: {
    stageStatuses?: Partial<Record<PipelineStage, PipelineStageStatusEntry>>;
    renderStatus?: PipelineRenderStatusSnapshot | null;
  }
): PipelineRunStep[] {
  const startId = START_STEP_BY_STAGE[activeStage];
  const startIndex = PIPELINE_RUN_SEQUENCE.findIndex((step) => step.id === startId);

  if (startIndex === -1) {
    return PIPELINE_RUN_SEQUENCE;
  }

  const sliced = PIPELINE_RUN_SEQUENCE.slice(startIndex);
  const stageStatuses = options?.stageStatuses;
  const renderStatus = options?.renderStatus;

  if (!stageStatuses && !renderStatus) {
    return sliced;
  }

  const firstPendingIndex = sliced.findIndex(
    (step) => !isStepAlreadyDone(step, stageStatuses, renderStatus)
  );

  if (firstPendingIndex === -1) {
    return [];
  }

  return sliced.slice(firstPendingIndex);
}

export function resolveRunRemainingButtonLabel({
  activeStage,
  isRunning,
  currentStepLabel,
  hasError,
  hasRemainingSteps = true,
}: {
  activeStage: PipelineStage;
  isRunning: boolean;
  currentStepLabel: string | null;
  hasError: boolean;
  hasRemainingSteps?: boolean;
}): string {
  if (isRunning) {
    return currentStepLabel ? `Running ${currentStepLabel}…` : "Running Pipeline…";
  }

  if (hasError) {
    return `Resume From ${STAGE_LABELS[activeStage]} →`;
  }

  if (!hasRemainingSteps) {
    return "All Remaining Stages Complete";
  }

  return "Run Remaining Stages →";
}

export function getPipelineAutomationDescription(activeStage: PipelineStage): string {
  if (activeStage === "setup") {
    return "Extracts sections from the script, saves them to the project, then runs the remaining automated stages from the current script and project configuration.";
  }

  if (activeStage === "script") {
    return "Runs the remaining automated stages from here using the current script. Setup extraction is not rerun, and manual review-only stops are skipped.";
  }

  return "Runs the remaining automated stages from here and stops on the first hard error.";
}

export function getPipelineAutomationPlanSummary(plan: PipelineRunStep[]): string {
  if (!plan.length) {
    return "Nothing to run.";
  }

  return `Will run: ${plan.map((step) => step.label).join(" -> ")}`;
}
