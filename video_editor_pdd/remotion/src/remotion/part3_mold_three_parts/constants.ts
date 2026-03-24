import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 344.160;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(29.420),
  VISUAL_01_START: s2f(29.760),
  VISUAL_01_END: s2f(59.300),
  VISUAL_02_START: s2f(59.880),
  VISUAL_02_END: s2f(68.600),
  VISUAL_03_START: s2f(68.820),
  VISUAL_03_END: s2f(96.560),
  VISUAL_04_START: s2f(68.820),
  VISUAL_04_END: s2f(112.180),
  VISUAL_05_START: s2f(112.400),
  VISUAL_05_END: s2f(126.180),
  VISUAL_06_START: s2f(126.180),
  VISUAL_06_END: s2f(144.080),
  VISUAL_07_START: s2f(135.500),
  VISUAL_07_END: s2f(161.920),
  VISUAL_08_START: s2f(144.300),
  VISUAL_08_END: s2f(161.920),
  VISUAL_09_START: s2f(162.140),
  VISUAL_09_END: s2f(180.100),
  VISUAL_10_START: s2f(180.360),
  VISUAL_10_END: s2f(206.620),
  VISUAL_11_START: s2f(206.620),
  VISUAL_11_END: s2f(230.360),
  VISUAL_12_START: s2f(230.600),
  VISUAL_12_END: s2f(254.060),
  VISUAL_13_START: s2f(254.400),
  VISUAL_13_END: s2f(271.640),
  VISUAL_14_START: s2f(271.980),
  VISUAL_14_END: s2f(298.820),
  VISUAL_15_START: s2f(299.120),
  VISUAL_15_END: s2f(303.620),
  VISUAL_16_START: s2f(304.820),
  VISUAL_16_END: s2f(330.700),
  VISUAL_17_START: s2f(330.980),
  VISUAL_17_END: s2f(344.160),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_mold_cross_section", desc: "02 mold cross section", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_test_walls_illuminate", desc: "03 test walls illuminate", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_liquid_hits_wall", desc: "04 liquid hits wall", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_research_annotations", desc: "05 research annotations", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_bug_add_wall", desc: "06 bug add wall", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_ratchet_timelapse", desc: "07 ratchet timelapse", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_traditional_vs_pdd_split", desc: "08 traditional vs pdd split", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_bug_fork_diagram", desc: "09 bug fork diagram", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_five_generations", desc: "10 five generations", lane: 0 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "11_z3_formal_proof", desc: "11 z3 formal proof", lane: 0 },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "12_module_level_aside", desc: "12 module level aside", lane: 0 },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "13_prompt_nozzle", desc: "13 prompt nozzle", lane: 0 },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "14_prompt_ratio", desc: "14 prompt ratio", lane: 0 },
  { start: BEATS.VISUAL_14_START, end: BEATS.VISUAL_14_END, id: "15_context_window_comparison", desc: "15 context window comparison", lane: 0 },
  { start: BEATS.VISUAL_15_START, end: BEATS.VISUAL_15_END, id: "16_grounding_material", desc: "16 grounding material", lane: 0 },
  { start: BEATS.VISUAL_16_START, end: BEATS.VISUAL_16_END, id: "17_grounding_feedback_loop", desc: "17 grounding feedback loop", lane: 0 },
  { start: BEATS.VISUAL_17_START, end: BEATS.VISUAL_17_END, id: "18_three_components_table", desc: "18 three components table", lane: 0 },
];

export const Part3MoldThreePartsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsSectionProps: z.infer<typeof Part3MoldThreePartsSectionProps> = {
  showTitle: true,
};

export type Part3MoldThreePartsSectionPropsType = z.infer<typeof Part3MoldThreePartsSectionProps>;
