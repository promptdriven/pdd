import {
  getPipelineAutomationDescription,
  getPipelineAutomationPlanSummary,
  resolvePipelineRunPlan,
  resolveRunRemainingButtonLabel,
  type PipelineStageStatusEntry,
} from "@/lib/client/pipeline-runner";

const makeStatuses = (
  overrides: Partial<Record<string, PipelineStageStatusEntry>> = {}
): Record<string, PipelineStageStatusEntry> => ({
  setup: { status: "not_started", updatedAt: null },
  script: { status: "not_started", updatedAt: null },
  "tts-script": { status: "not_started", updatedAt: null },
  "tts-render": { status: "not_started", updatedAt: null },
  "audio-sync": { status: "not_started", updatedAt: null },
  specs: { status: "not_started", updatedAt: null },
  veo: { status: "not_started", updatedAt: null },
  compositions: { status: "not_started", updatedAt: null },
  render: { status: "not_started", updatedAt: null },
  audit: { status: "not_started", updatedAt: null },
  ...overrides,
});

describe("resolvePipelineRunPlan", () => {
  it("starts at setup when the pipeline is at stage 1", () => {
    expect(resolvePipelineRunPlan("setup").map((step) => step.id)).toEqual([
      "setup",
      "tts-script",
      "tts-render",
      "audio-sync",
      "specs",
      "veo",
      "compositions",
      "render",
      "stitch",
      "audit",
    ]);
  });

  it("skips the manual script review stop when resuming from stage 2", () => {
    expect(resolvePipelineRunPlan("script").map((step) => step.id)).toEqual([
      "tts-script",
      "tts-render",
      "audio-sync",
      "specs",
      "veo",
      "compositions",
      "render",
      "stitch",
      "audit",
    ]);
  });

  it("resumes from render with stitch and audit still pending", () => {
    expect(resolvePipelineRunPlan("render").map((step) => step.id)).toEqual([
      "render",
      "stitch",
      "audit",
    ]);
  });

  it("keeps audit as a rerunnable final step", () => {
    expect(resolvePipelineRunPlan("audit").map((step) => step.id)).toEqual(["audit"]);
  });

  it("skips already-complete compositions when resuming from stage 8", () => {
    expect(
      resolvePipelineRunPlan("compositions", {
        stageStatuses: makeStatuses({
          compositions: { status: "done", updatedAt: "2026-03-13T21:00:00.000Z" },
        }),
      }).map((step) => step.id)
    ).toEqual(["render", "stitch", "audit"]);
  });

  it("skips render and stitch when a fresh full video already exists", () => {
    expect(
      resolvePipelineRunPlan("render", {
        stageStatuses: makeStatuses({
          render: { status: "done", updatedAt: "2026-03-13T22:00:00.000Z" },
        }),
        renderStatus: {
          fullVideo: {
            exists: true,
            stale: false,
            updatedAtMs: Date.parse("2026-03-13T22:05:00.000Z"),
          },
        },
      }).map((step) => step.id)
    ).toEqual(["audit"]);
  });

  it("returns an empty plan when all remaining work is complete", () => {
    expect(
      resolvePipelineRunPlan("audit", {
        stageStatuses: makeStatuses({
          audit: { status: "done", updatedAt: "2026-03-13T23:00:00.000Z" },
        }),
      })
    ).toEqual([]);
  });

  it("reruns compositions when newer specs or Veo clips make them stale", () => {
    expect(
      resolvePipelineRunPlan("compositions", {
        stageStatuses: makeStatuses({
          specs: { status: "done", updatedAt: "2026-03-13T23:47:09.425Z" },
          veo: { status: "done", updatedAt: "2026-03-13T23:50:47.344Z" },
          compositions: { status: "done", updatedAt: "2026-03-13T21:47:24.446Z" },
        }),
      }).map((step) => step.id)
    ).toEqual(["compositions", "render", "stitch", "audit"]);
  });

  it("reruns render when compositions are newer than the last render", () => {
    expect(
      resolvePipelineRunPlan("render", {
        stageStatuses: makeStatuses({
          compositions: { status: "done", updatedAt: "2026-03-13T23:50:47.344Z" },
          render: { status: "done", updatedAt: "2026-03-13T22:11:10.685Z" },
        }),
        renderStatus: {
          fullVideo: {
            exists: true,
            stale: false,
            updatedAtMs: Date.parse("2026-03-13T22:12:00.000Z"),
          },
        },
      }).map((step) => step.id)
    ).toEqual(["render", "stitch", "audit"]);
  });
});

describe("resolveRunRemainingButtonLabel", () => {
  it("uses a neutral label before execution starts", () => {
    expect(
      resolveRunRemainingButtonLabel({
        activeStage: "specs",
        isRunning: false,
        currentStepLabel: null,
        hasError: false,
      })
    ).toBe("Run Remaining Stages →");
  });

  it("shows the running step label while orchestration is active", () => {
    expect(
      resolveRunRemainingButtonLabel({
        activeStage: "specs",
        isRunning: true,
        currentStepLabel: "Generate Specs",
        hasError: false,
      })
    ).toBe("Running Generate Specs…");
  });

  it("offers a resume label after a failure", () => {
    expect(
      resolveRunRemainingButtonLabel({
        activeStage: "compositions",
        isRunning: false,
        currentStepLabel: null,
        hasError: true,
      })
    ).toBe("Resume From Compositions →");
  });

  it("shows a completion label when nothing remains", () => {
    expect(
      resolveRunRemainingButtonLabel({
        activeStage: "audit",
        isRunning: false,
        currentStepLabel: null,
        hasError: false,
        hasRemainingSteps: false,
      })
    ).toBe("All Remaining Stages Complete");
  });
});

describe("getPipelineAutomationDescription", () => {
  it("explains that setup automation extracts and saves sections before continuing", () => {
    expect(getPipelineAutomationDescription("setup")).toContain(
      "Extracts sections from the script, saves them to the project"
    );
  });

  it("explains that script-stage automation does not rerun setup extraction", () => {
    expect(getPipelineAutomationDescription("script")).toContain(
      "Setup extraction is not rerun"
    );
  });

  it("keeps later-stage automation focused on remaining steps", () => {
    expect(getPipelineAutomationDescription("compositions")).toBe(
      "Runs the remaining automated stages from here and stops on the first hard error."
    );
  });
});

describe("getPipelineAutomationPlanSummary", () => {
  it("shows the actual setup-first run plan", () => {
    const plan = resolvePipelineRunPlan("setup");
    expect(getPipelineAutomationPlanSummary(plan)).toBe(
      "Will run: Extract Sections -> Generate TTS Script -> Render Audio -> Run Audio Sync -> Generate Specs -> Generate Veo Clips -> Generate Compositions -> Render Sections -> Stitch Full Video -> Audit All Sections"
    );
  });

  it("shows a later-stage plan without setup when resuming from script", () => {
    const plan = resolvePipelineRunPlan("script");
    expect(getPipelineAutomationPlanSummary(plan)).toBe(
      "Will run: Generate TTS Script -> Render Audio -> Run Audio Sync -> Generate Specs -> Generate Veo Clips -> Generate Compositions -> Render Sections -> Stitch Full Video -> Audit All Sections"
    );
  });

  it("reports when nothing remains to run", () => {
    expect(getPipelineAutomationPlanSummary([])).toBe("Nothing to run.");
  });
});
