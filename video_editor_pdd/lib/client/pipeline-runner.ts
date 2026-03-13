import type { PipelineStage } from "@/lib/types";

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

export function resolvePipelineRunPlan(activeStage: PipelineStage): PipelineRunStep[] {
  const startId = START_STEP_BY_STAGE[activeStage];
  const startIndex = PIPELINE_RUN_SEQUENCE.findIndex((step) => step.id === startId);

  if (startIndex === -1) {
    return PIPELINE_RUN_SEQUENCE;
  }

  return PIPELINE_RUN_SEQUENCE.slice(startIndex);
}

export function resolveRunRemainingButtonLabel({
  activeStage,
  isRunning,
  currentStepLabel,
  hasError,
}: {
  activeStage: PipelineStage;
  isRunning: boolean;
  currentStepLabel: string | null;
  hasError: boolean;
}): string {
  if (isRunning) {
    return currentStepLabel ? `Running ${currentStepLabel}…` : "Running Pipeline…";
  }

  if (hasError) {
    return `Resume From ${STAGE_LABELS[activeStage]} →`;
  }

  return "Run Remaining Stages →";
}

export function getPipelineAutomationDescription(activeStage: PipelineStage): string {
  if (activeStage === "setup") {
    return "Runs the remaining automated stages from here using the current script and project configuration.";
  }

  if (activeStage === "script") {
    return "Runs the remaining automated stages from here using the current script. Manual review-only stops are skipped.";
  }

  return "Runs the remaining automated stages from here and stops on the first hard error.";
}
