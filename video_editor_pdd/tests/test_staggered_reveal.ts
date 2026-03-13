import { resolveBoundedStagger } from "../remotion/src/remotion/_shared/staggered-reveal";

describe("resolveBoundedStagger", () => {
  it("compresses the cadence so the full reveal fits inside the declared phase window", () => {
    const schedule = resolveBoundedStagger({
      itemCount: "Animation Section".length,
      startFrame: 5,
      endFrame: 20,
      desiredStepFrames: 1.5,
      defaultFadeFrames: 5,
    });

    const lastItemEnd =
      5 + ("Animation Section".length - 1) * schedule.stepFrames + schedule.fadeFrames;

    expect(schedule.stepFrames).toBeLessThan(1.5);
    expect(schedule.fadeFrames).toBeGreaterThan(0);
    expect(lastItemEnd).toBeLessThanOrEqual(20);
  });

  it("preserves the desired cadence when it already fits", () => {
    const schedule = resolveBoundedStagger({
      itemCount: 4,
      startFrame: 10,
      endFrame: 30,
      desiredStepFrames: 2,
      defaultFadeFrames: 4,
    });

    expect(schedule.stepFrames).toBe(2);
    expect(schedule.fadeFrames).toBe(4);
  });
});
