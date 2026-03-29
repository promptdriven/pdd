import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 33.180;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(16.760),
  VISUAL_01_START: s2f(0.000),
  VISUAL_01_END: s2f(16.760),
  VISUAL_02_START: s2f(0.000),
  VISUAL_02_END: s2f(16.760),
  VISUAL_03_START: s2f(0.000),
  VISUAL_03_END: s2f(16.760),
  VISUAL_04_START: s2f(17.100),
  VISUAL_04_END: s2f(28.280),
  VISUAL_05_START: s2f(17.100),
  VISUAL_05_END: s2f(28.280),
  VISUAL_06_START: s2f(28.380),
  VISUAL_06_END: s2f(33.180),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "02_legacy_codebase_reveal", desc: "02 legacy codebase reveal", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "04_source_of_truth_label", desc: "04 source of truth label", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "01_section_title_card", desc: "01 section title card", lane: 1 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "03_module_highlight_terminal", desc: "03 module highlight terminal", lane: 1 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_module_glow_spread", desc: "05 module glow spread", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_no_big_bang_callout", desc: "06 no big bang callout", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_gradual_migration_insight", desc: "07 gradual migration insight", lane: 1 },
];

export const WhereToStartSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultWhereToStartSectionProps: z.infer<typeof WhereToStartSectionProps> = {
  showTitle: true,
};

export type WhereToStartSectionPropsType = z.infer<typeof WhereToStartSectionProps>;
