import {
  buildSlotScaledSequenceContext,
  computeSlotScaledFrame,
} from "../lib/visual-runtime";
import fs from "fs";
import path from "path";

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

describe("shared Remotion runtime", () => {
  const source = fs.readFileSync(
    path.join(
      process.cwd(),
      "remotion/src/remotion/_shared/visual-runtime.tsx"
    ),
    "utf8"
  );

  it("reuses the slot-scaling helpers instead of duplicating the logic inline", () => {
    expect(source).toMatch(/computeSlotScaledFrame/);
    expect(source).toMatch(/buildSlotScaledSequenceContext/);
  });

  it("resets sequence offsets for scaled visuals so late slots can reach their intrinsic frames", () => {
    expect(source).toMatch(/cumulatedFrom:\s*0/);
    expect(source).toMatch(/relativeFrom:\s*0/);
    expect(source).toMatch(/parentFrom:\s*0/);
  });

  it("exports a visual contract provider alongside media aliases", () => {
    expect(source).toMatch(/VisualContractProvider/);
    expect(source).toMatch(/VisualContractContext/);
  });

  it("exposes a helper that resolves media aliases into staticFile-ready asset URLs", () => {
    expect(source).toMatch(/useVisualMediaAssetSrc/);
    expect(source).toMatch(/staticFile/);
  });

  it("exposes a hook for reading structured visual contract data", () => {
    expect(source).toMatch(/useVisualContractData/);
  });

  it("falls back to media aliases stored on the structured visual contract when no provider media is passed", () => {
    expect(source).toMatch(/contract\?\.mediaAliases/);
    expect(source).toMatch(/media\?\.\[key\].*contractMedia\?\.\[key\]/s);
  });
});
