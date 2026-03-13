import {
  resolvePipelineRunPlan,
  resolveRunRemainingButtonLabel,
} from "@/lib/client/pipeline-runner";

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
});
