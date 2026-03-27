import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 228.140;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(56.580),
  VISUAL_01_START: s2f(56.580),
  VISUAL_01_END: s2f(76.340),
  VISUAL_02_START: s2f(92.640),
  VISUAL_02_END: s2f(120.060),
  VISUAL_03_START: s2f(120.060),
  VISUAL_03_END: s2f(142.280),
  VISUAL_04_START: s2f(120.060),
  VISUAL_04_END: s2f(142.280),
  VISUAL_05_START: s2f(142.440),
  VISUAL_05_END: s2f(179.300),
  VISUAL_06_START: s2f(179.480),
  VISUAL_06_END: s2f(192.660),
  VISUAL_07_START: s2f(188.463),
  VISUAL_07_END: s2f(228.140),
  VISUAL_08_START: s2f(188.463),
  VISUAL_08_END: s2f(228.140),
  VISUAL_09_START: s2f(189.472),
  VISUAL_09_END: s2f(228.140),
  VISUAL_10_START: s2f(192.840),
  VISUAL_10_END: s2f(216.140),
  VISUAL_11_START: s2f(195.076),
  VISUAL_11_END: s2f(228.140),
  VISUAL_12_START: s2f(204.807),
  VISUAL_12_END: s2f(228.140),
  VISUAL_13_START: s2f(211.330),
  VISUAL_13_END: s2f(228.140),
  VISUAL_14_START: s2f(213.881),
  VISUAL_14_END: s2f(228.140),
  VISUAL_15_START: s2f(216.300),
  VISUAL_15_END: s2f(228.140),
  VISUAL_16_START: s2f(216.300),
  VISUAL_16_END: s2f(228.140),
  VISUAL_17_START: s2f(216.300),
  VISUAL_17_END: s2f(228.140),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 1 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "04_mold_production_counter", desc: "04 mold production counter", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "07_split_craftsman_vs_mold", desc: "07 split craftsman vs mold", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "11_schematic_density_zoom", desc: "11 schematic density zoom", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "12_verilog_synthesis", desc: "12 verilog synthesis", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "13_triple_synthesis_equivalence", desc: "13 triple synthesis equivalence", lane: 1 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "14_synopsys_pdd_equivalence", desc: "14 synopsys pdd equivalence", lane: 1 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_veo_craftsman_carving", desc: "08 veo craftsman carving", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_veo_mold_plastic_flow", desc: "09 veo mold plastic flow", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "02_factory_floor_wide", desc: "02 factory floor wide", lane: 0 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "15_abstraction_staircase", desc: "15 abstraction staircase", lane: 1 },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "03_injection_molding_closeup", desc: "03 injection molding closeup", lane: 0 },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "05_defect_and_mold_fix", desc: "05 defect and mold fix", lane: 0 },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "06_new_parts_eject", desc: "06 new parts eject", lane: 0 },
  { start: BEATS.VISUAL_14_START, end: BEATS.VISUAL_14_END, id: "10_veo_1980s_chip_lab", desc: "10 veo 1980s chip lab", lane: 0 },
  { start: BEATS.VISUAL_15_START, end: BEATS.VISUAL_15_END, id: "16_billion_gate_unreviewable", desc: "16 billion gate unreviewable", lane: 0 },
  { start: BEATS.VISUAL_16_START, end: BEATS.VISUAL_16_END, id: "17_review_spec_verify_output", desc: "17 review spec verify output", lane: 0 },
  { start: BEATS.VISUAL_17_START, end: BEATS.VISUAL_17_END, id: "18_prompt_mold_finale", desc: "18 prompt mold finale", lane: 1 },
];

export const Part2ParadigmShiftSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftSectionProps: z.infer<typeof Part2ParadigmShiftSectionProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftSectionPropsType = z.infer<typeof Part2ParadigmShiftSectionProps>;
