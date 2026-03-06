import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 98.424;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(5.0),
  VISUAL_01_START: s2f(18.08),
  VISUAL_01_END: s2f(23.08),
  VISUAL_02_START: s2f(32.7),
  VISUAL_02_END: s2f(37.7),
  VISUAL_03_START: s2f(85.86),
  VISUAL_03_END: s2f(90.86),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "Part5CompoundTitleCard",
    desc: "Title card introducing Part 5: Compound Returns",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "Part5CompoundStatCalloutMaintenance",
    desc: "80-90% of software cost is maintenance, not features or launch",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "Part5CompoundStatCalloutCisq",
    desc: "$2.41T cost of poor software quality, technical debt is #1 driver",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "Part5CompoundSplitPatchingVsPdd",
    desc: "Split view comparing patching debt accumulation vs generation debt resets",
  },
];

export const Part5CompoundReturnsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart5CompoundReturnsProps: z.infer<
  typeof Part5CompoundReturnsProps
> = {
  showTitle: true,
};

export type Part5CompoundReturnsPropsType = z.infer<
  typeof Part5CompoundReturnsProps
>;
