import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 96.912;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(5.0),
  VISUAL_01_START: s2f(25.38),
  VISUAL_01_END: s2f(30.38),
  VISUAL_02_START: s2f(26.32),
  VISUAL_02_END: s2f(31.32),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "part4_precision_split_prompt_detail_vs_tests",
    desc: "Split view comparing prompt detail level to test coverage",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "part4_precision_stat_callout_prompt_compression",
    desc: "Stat callout on prompt compression effectiveness",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "part4_precision_title_card",
    desc: "Title card introducing Part 4: The Precision Tradeoff",
  },
];

export const Part4PrecisionTradeoffProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart4PrecisionTradeoffProps: z.infer<
  typeof Part4PrecisionTradeoffProps
> = {
  showTitle: true,
};

export type Part4PrecisionTradeoffPropsType = z.infer<
  typeof Part4PrecisionTradeoffProps
>;
