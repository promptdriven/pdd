import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 32.080;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(15.120),
  VISUAL_01_START: s2f(0.000),
  VISUAL_01_END: s2f(15.120),
  VISUAL_02_START: s2f(15.460),
  VISUAL_02_END: s2f(26.240),
  VISUAL_03_START: s2f(26.240),
  VISUAL_03_END: s2f(32.080),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_legacy_codebase_reveal", desc: "02 legacy codebase reveal", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "04_source_of_truth_shift", desc: "04 source of truth shift", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "07_transition_to_closing", desc: "07 transition to closing", lane: 0 },
];

export const WhereToStartSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultWhereToStartSectionProps: z.infer<typeof WhereToStartSectionProps> = {
  showTitle: true,
};

export type WhereToStartSectionPropsType = z.infer<typeof WhereToStartSectionProps>;
