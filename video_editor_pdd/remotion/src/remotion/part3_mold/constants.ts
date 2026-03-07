import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 280.728;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(8.0),
  VISUAL_01_START: s2f(8.0),
  VISUAL_01_END: s2f(45.0),
  VISUAL_02_START: s2f(45.0),
  VISUAL_02_END: s2f(80.0),
  VISUAL_03_START: s2f(80.0),
  VISUAL_03_END: s2f(130.0),
  VISUAL_04_START: s2f(130.0),
  VISUAL_04_END: s2f(165.0),
  VISUAL_05_START: s2f(165.0),
  VISUAL_05_END: s2f(220.0),
  VISUAL_06_START: s2f(220.0),
  VISUAL_06_END: s2f(270.0),
  VISUAL_07_START: s2f(0.0),
  VISUAL_07_END: s2f(280.728),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "01_title_card",
    desc: "Part 3 Mold title card with section heading",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "03_stat_callout_coderabbit",
    desc: "CodeRabbit stat callout highlighting AI code review adoption",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "04_stat_callout_dora",
    desc: "DORA metrics stat callout showing deployment frequency gains",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "06_split_prompt_vs_code",
    desc: "Split view comparing prompt specification to generated code",
  },
  {
    start: BEATS.VISUAL_04_START,
    end: BEATS.VISUAL_04_END,
    id: "08_stat_callout_nl_context",
    desc: "Natural language context stat callout on prompt compression ratios",
  },
  {
    start: BEATS.VISUAL_05_START,
    end: BEATS.VISUAL_05_END,
    id: "10_ratchet_infographic",
    desc: "Ratchet infographic showing iterative quality improvement with pawl mechanism",
  },
  {
    start: BEATS.VISUAL_06_START,
    end: BEATS.VISUAL_06_END,
    id: "12_three_pillars_diagram",
    desc: "Three pillars diagram illustrating specification, generation, and verification",
  },
  {
    start: BEATS.VISUAL_07_START,
    end: BEATS.VISUAL_07_END,
    id: "13_subtitle_track",
    desc: "Word-by-word subtitle track spanning full Part 3 narration",
  },
];

export const Part3MoldThreePartsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsProps: z.infer<
  typeof Part3MoldThreePartsProps
> = {
  showTitle: true,
};

export type Part3MoldThreePartsPropsType = z.infer<
  typeof Part3MoldThreePartsProps
>;
