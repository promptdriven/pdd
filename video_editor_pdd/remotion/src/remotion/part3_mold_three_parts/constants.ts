import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 344.160;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(344.160),
  VISUAL_00_END: s2f(344.160),
  VISUAL_01_START: s2f(344.160),
  VISUAL_01_END: s2f(344.160),
  VISUAL_02_START: s2f(344.160),
  VISUAL_02_END: s2f(344.160),
  VISUAL_03_START: s2f(344.160),
  VISUAL_03_END: s2f(344.160),
  VISUAL_04_START: s2f(344.160),
  VISUAL_04_END: s2f(344.160),
  VISUAL_05_START: s2f(344.160),
  VISUAL_05_END: s2f(344.160),
  VISUAL_06_START: s2f(344.160),
  VISUAL_06_END: s2f(344.160),
  VISUAL_07_START: s2f(336.915),
  VISUAL_07_END: s2f(344.160),
  VISUAL_08_START: s2f(344.160),
  VISUAL_08_END: s2f(344.160),
  VISUAL_09_START: s2f(344.160),
  VISUAL_09_END: s2f(344.160),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_mold_cross_section", desc: "02 mold cross section", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_test_walls_constraint", desc: "03 test walls constraint", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_research_annotations_ai_quality", desc: "04 research annotations ai quality", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_bug_adds_wall", desc: "05 bug adds wall", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_ratchet_split_comparison", desc: "06 ratchet split comparison", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_five_generations_z3", desc: "07 five generations z3", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_prompt_capital_specification", desc: "08 prompt capital specification", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_grounding_feedback_loop", desc: "09 grounding feedback loop", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_three_components_table", desc: "10 three components table", lane: 0 },
];

export const Part3MoldThreePartsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsSectionProps: z.infer<typeof Part3MoldThreePartsSectionProps> = {
  showTitle: true,
};

export type Part3MoldThreePartsSectionPropsType = z.infer<typeof Part3MoldThreePartsSectionProps>;
