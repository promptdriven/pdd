import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 344.448;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(252.035),
  VISUAL_00_END: s2f(253.328),
  VISUAL_01_START: s2f(253.328),
  VISUAL_01_END: s2f(256.559),
  VISUAL_02_START: s2f(256.559),
  VISUAL_02_END: s2f(260.436),
  VISUAL_03_START: s2f(260.436),
  VISUAL_03_END: s2f(265.283),
  VISUAL_04_START: s2f(265.283),
  VISUAL_04_END: s2f(267.868),
  VISUAL_05_START: s2f(267.868),
  VISUAL_05_END: s2f(273.038),
  VISUAL_06_START: s2f(273.038),
  VISUAL_06_END: s2f(300.503),
  VISUAL_07_START: s2f(300.503),
  VISUAL_07_END: s2f(329.584),
  VISUAL_08_START: s2f(329.584),
  VISUAL_08_END: s2f(339.278),
  VISUAL_09_START: s2f(339.278),
  VISUAL_09_END: s2f(344.448),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "Section 3.1: Part 3 Title Card — The Mold Has Three Parts" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_mold_cross_section", desc: "Section 3.2: Mold Cross-Section — Three Regions Illuminate" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_test_walls_constraint", desc: "Section 3.3: Test Walls Constraint — Liquid Meets Boundaries" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_research_annotations_ai_quality", desc: "Section 3.4: Research Annotations — AI Code Quality Data" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_bug_adds_wall", desc: "Section 3.5: Bug Adds Wall — The Developer's Terminal Moment" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_ratchet_split_comparison", desc: "Section 3.6: Ratchet Split Comparison — Traditional vs PDD Bug Workflow" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_five_generations_z3", desc: "Section 3.7: Five Generations + Z3 — Generate, Select, Prove" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_prompt_capital_specification", desc: "Section 3.8: Prompt Capital — The Specification That Governs" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_grounding_feedback_loop", desc: "Section 3.9: Grounding Feedback Loop — Material Flowing Back" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_three_components_table", desc: "Section 3.10: Three Components Table — The Complete Specification" },
];

export const Part3MoldThreePartsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsSectionProps: z.infer<typeof Part3MoldThreePartsSectionProps> = {
  showTitle: true,
};

export type Part3MoldThreePartsSectionPropsType = z.infer<typeof Part3MoldThreePartsSectionProps>;
