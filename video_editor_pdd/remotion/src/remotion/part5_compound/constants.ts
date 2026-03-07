import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 98.424;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(6.0),
  VISUAL_01_START: s2f(6.0),
  VISUAL_01_END: s2f(20.0),
  VISUAL_02_START: s2f(20.0),
  VISUAL_02_END: s2f(34.0),
  VISUAL_03_START: s2f(34.0),
  VISUAL_03_END: s2f(56.0),
  VISUAL_04_START: s2f(56.0),
  VISUAL_04_END: s2f(76.0),
  VISUAL_05_START: s2f(76.0),
  VISUAL_05_END: s2f(90.0),
  VISUAL_06_START: s2f(0.0),
  VISUAL_06_END: s2f(98.424),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "01_title_card",
    desc: "Part 5 Compound Returns title card with section heading",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "03_stat_callout_maintenance",
    desc: "Stat callout on maintenance cost reduction through compound specification",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "05_stat_callout_cisq",
    desc: "CISQ stat callout highlighting cost of poor software quality",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "06_compound_debt_chart",
    desc: "Chart showing compound debt accumulation vs PDD debt resets over time",
  },
  {
    start: BEATS.VISUAL_04_START,
    end: BEATS.VISUAL_04_END,
    id: "08_split_patching_vs_pdd",
    desc: "Split view comparing patching debt accumulation vs generation debt resets",
  },
  {
    start: BEATS.VISUAL_05_START,
    end: BEATS.VISUAL_05_END,
    id: "10_quote_card",
    desc: "Quote card: We're at that moment for code",
  },
  {
    start: BEATS.VISUAL_06_START,
    end: BEATS.VISUAL_06_END,
    id: "11_subtitle_track",
    desc: "Word-by-word subtitle track for full Part 5 narration",
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
