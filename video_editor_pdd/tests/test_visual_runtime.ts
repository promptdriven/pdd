import {
  buildSlotScaledSequenceContext,
  computeSlotScaledFrame,
} from "../lib/visual-runtime";

describe("computeSlotScaledFrame", () => {
  it("scales a slot-local frame into the intrinsic visual duration", () => {
    expect(
      computeSlotScaledFrame({
        localFrame: 26,
        slotDurationInFrames: 32,
        intrinsicDurationInFrames: 90,
      })
    ).toBe(75);
  });

  it("returns frame 0 for degenerate slot or intrinsic durations", () => {
    expect(
      computeSlotScaledFrame({
        localFrame: 0,
        slotDurationInFrames: 1,
        intrinsicDurationInFrames: 90,
      })
    ).toBe(0);

    expect(
      computeSlotScaledFrame({
        localFrame: 10,
        slotDurationInFrames: 32,
        intrinsicDurationInFrames: 1,
      })
    ).toBe(0);
  });
});

describe("buildSlotScaledSequenceContext", () => {
  it("resets sequence offsets so late visuals can use their full intrinsic frame range", () => {
    const result = buildSlotScaledSequenceContext(
      {
        cumulatedFrom: 294,
        relativeFrom: 294,
        durationInFrames: 32,
        parentFrom: 0,
        id: "late-visual",
        height: null,
        width: null,
        premounting: false,
        postmounting: false,
        premountDisplay: null,
        postmountDisplay: null,
      },
      90
    );

    expect(result).toEqual(
      expect.objectContaining({
        cumulatedFrom: 0,
        relativeFrom: 0,
        parentFrom: 0,
        durationInFrames: 90,
      })
    );
  });

  it("returns null when no parent sequence context exists", () => {
    expect(buildSlotScaledSequenceContext(null, 90)).toBeNull();
  });
});
