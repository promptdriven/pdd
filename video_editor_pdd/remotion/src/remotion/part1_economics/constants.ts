import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 382.176;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(5.0),
  VISUAL_01_START: s2f(5.0),
  VISUAL_01_END: s2f(95.0),
  VISUAL_02_START: s2f(95.0),
  VISUAL_02_END: s2f(103.0),
  VISUAL_03_START: s2f(103.0),
  VISUAL_03_END: s2f(113.0),
  VISUAL_04_START: s2f(113.0),
  VISUAL_04_END: s2f(143.0),
  VISUAL_05_START: s2f(143.0),
  VISUAL_05_END: s2f(155.0),
  VISUAL_06_START: s2f(155.0),
  VISUAL_06_END: s2f(180.0),
  VISUAL_07_START: s2f(180.0),
  VISUAL_07_END: s2f(187.0),
  VISUAL_08_START: s2f(187.0),
  VISUAL_08_END: s2f(195.0),
  VISUAL_09_START: s2f(0.0),
  VISUAL_09_END: s2f(382.176),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "01_title_card",
    desc: "Part 1 Economics title card with eyebrow label and horizontal rule",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "03_cost_crossover_chart",
    desc: "Animated cost crossover chart showing patching vs generation economics",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "04_stat_callout_github",
    desc: "GitHub Copilot study stat callout — 55% faster task completion",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "06_stat_callout_uplevel",
    desc: "Uplevel study stat callout — AI-assisted developer productivity gains",
  },
  {
    start: BEATS.VISUAL_04_START,
    end: BEATS.VISUAL_04_END,
    id: "07_stat_callout_gitclear",
    desc: "GitClear analysis of 150M lines shows code churn has doubled",
  },
  {
    start: BEATS.VISUAL_05_START,
    end: BEATS.VISUAL_05_END,
    id: "09_context_degradation_chart",
    desc: "Context window fill vs capability degradation bar chart",
  },
  {
    start: BEATS.VISUAL_06_START,
    end: BEATS.VISUAL_06_END,
    id: "10_split_perception_reality",
    desc: "Split view contrasting developer perception vs measured reality",
  },
  {
    start: BEATS.VISUAL_07_START,
    end: BEATS.VISUAL_07_END,
    id: "12_regeneration_infographic",
    desc: "Compression ratio and U-curve showing regeneration economics",
  },
  {
    start: BEATS.VISUAL_08_START,
    end: BEATS.VISUAL_08_END,
    id: "13_crossover_zoom",
    desc: "Zoom into cost crossover point where generation beats patching",
  },
  {
    start: BEATS.VISUAL_09_START,
    end: BEATS.VISUAL_09_END,
    id: "14_subtitle_track",
    desc: "Word-by-word subtitle track spanning full Part 1 narration",
  },
];

export const Part1EconomicsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsProps: z.infer<typeof Part1EconomicsProps> = {
  showTitle: true,
};

export type Part1EconomicsPropsType = z.infer<typeof Part1EconomicsProps>;
