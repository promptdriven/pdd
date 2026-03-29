import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 365.800;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(63.640),
  VISUAL_01_START: s2f(47.460),
  VISUAL_01_END: s2f(63.640),
  VISUAL_02_START: s2f(63.880),
  VISUAL_02_END: s2f(71.780),
  VISUAL_03_START: s2f(72.040),
  VISUAL_03_END: s2f(121.000),
  VISUAL_04_START: s2f(127.460),
  VISUAL_04_END: s2f(148.000),
  VISUAL_05_START: s2f(148.460),
  VISUAL_05_END: s2f(158.460),
  VISUAL_06_START: s2f(158.800),
  VISUAL_06_END: s2f(167.820),
  VISUAL_07_START: s2f(168.200),
  VISUAL_07_END: s2f(184.560),
  VISUAL_08_START: s2f(184.760),
  VISUAL_08_END: s2f(202.860),
  VISUAL_09_START: s2f(202.960),
  VISUAL_09_END: s2f(228.420),
  VISUAL_10_START: s2f(228.420),
  VISUAL_10_END: s2f(248.500),
  VISUAL_11_START: s2f(248.700),
  VISUAL_11_END: s2f(270.480),
  VISUAL_12_START: s2f(270.480),
  VISUAL_12_END: s2f(318.060),
  VISUAL_13_START: s2f(318.640),
  VISUAL_13_END: s2f(344.000),
  VISUAL_14_START: s2f(344.420),
  VISUAL_14_END: s2f(353.520),
  VISUAL_15_START: s2f(353.520),
  VISUAL_15_END: s2f(362.260),
  VISUAL_16_START: s2f(356.205),
  VISUAL_16_END: s2f(365.800),
  VISUAL_17_START: s2f(362.420),
  VISUAL_17_END: s2f(365.800),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 1 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_mold_cross_section", desc: "02 mold cross section", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_mold_walls_illuminate", desc: "03 mold walls illuminate", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_liquid_injection", desc: "04 liquid injection", lane: 1 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_bug_adds_wall", desc: "05 bug adds wall", lane: 1 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_ratchet_timelapse", desc: "06 ratchet timelapse", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_split_traditional_vs_pdd", desc: "07 split traditional vs pdd", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_bug_fork_road", desc: "08 bug fork road", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_five_generations", desc: "09 five generations", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_z3_formal_proof", desc: "10 z3 formal proof", lane: 1 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "11_module_boundary", desc: "11 module boundary", lane: 1 },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "12_prompt_nozzle", desc: "12 prompt nozzle", lane: 0 },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "13_prompt_ratio", desc: "13 prompt ratio", lane: 0 },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "15_grounding_styles", desc: "15 grounding styles", lane: 1 },
  { start: BEATS.VISUAL_14_START, end: BEATS.VISUAL_14_END, id: "16_three_components_pullback", desc: "16 three components pullback", lane: 0 },
  { start: BEATS.VISUAL_15_START, end: BEATS.VISUAL_15_END, id: "17_component_table", desc: "17 component table", lane: 0 },
  { start: BEATS.VISUAL_16_START, end: BEATS.VISUAL_16_END, id: "14_veo_grounding_material", desc: "14 veo grounding material", lane: 0 },
  { start: BEATS.VISUAL_17_START, end: BEATS.VISUAL_17_END, id: "18_code_output_finale", desc: "18 code output finale", lane: 0 },
];

export const Part3MoldPartsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldPartsSectionProps: z.infer<typeof Part3MoldPartsSectionProps> = {
  showTitle: true,
};

export type Part3MoldPartsSectionPropsType = z.infer<typeof Part3MoldPartsSectionProps>;
