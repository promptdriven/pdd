import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 180;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(6.0),
  VISUAL_01_START: s2f(6.0),
  VISUAL_01_END: s2f(45.0),
  VISUAL_02_START: s2f(45.0),
  VISUAL_02_END: s2f(70.0),
  VISUAL_03_START: s2f(70.0),
  VISUAL_03_END: s2f(110.0),
  VISUAL_04_START: s2f(110.0),
  VISUAL_04_END: s2f(150.0),
  VISUAL_05_START: s2f(0.0),
  VISUAL_05_END: s2f(180.0),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "01_title_card",
    desc: "Part 4 Precision title card with eyebrow label and radial glow",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "03_precision_cost_ucurve",
    desc: "U-curve chart showing cost vs precision tradeoff with danger zones",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "04_stat_callout_prompt_compression",
    desc: "Stat callout on prompt compression ratios and specification density",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "05_split_prompt_detail_vs_tests",
    desc: "Split view comparing prompt detail level to test coverage",
  },
  {
    start: BEATS.VISUAL_04_START,
    end: BEATS.VISUAL_04_END,
    id: "07_spectrum_slider",
    desc: "Spectrum slider showing precision tradeoff across project types",
  },
  {
    start: BEATS.VISUAL_05_START,
    end: BEATS.VISUAL_05_END,
    id: "10_subtitle_track",
    desc: "Word-by-word subtitle track spanning full Part 4 narration",
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
