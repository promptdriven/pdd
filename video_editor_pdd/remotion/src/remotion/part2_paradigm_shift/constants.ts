import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 227.480;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(48.620),
  VISUAL_01_START: s2f(67.800),
  VISUAL_01_END: s2f(78.420),
  VISUAL_02_START: s2f(85.560),
  VISUAL_02_END: s2f(110.300),
  VISUAL_03_START: s2f(117.120),
  VISUAL_03_END: s2f(152.820),
  VISUAL_04_START: s2f(153.860),
  VISUAL_04_END: s2f(190.660),
  VISUAL_05_START: s2f(176.246),
  VISUAL_05_END: s2f(227.480),
  VISUAL_06_START: s2f(176.246),
  VISUAL_06_END: s2f(227.480),
  VISUAL_07_START: s2f(188.924),
  VISUAL_07_END: s2f(227.480),
  VISUAL_08_START: s2f(190.800),
  VISUAL_08_END: s2f(214.100),
  VISUAL_09_START: s2f(200.318),
  VISUAL_09_END: s2f(227.480),
  VISUAL_10_START: s2f(208.746),
  VISUAL_10_END: s2f(227.480),
  VISUAL_11_START: s2f(213.870),
  VISUAL_11_END: s2f(227.480),
  VISUAL_12_START: s2f(214.260),
  VISUAL_12_END: s2f(227.480),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 1 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "04_mold_production_counter", desc: "04 mold production counter", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "06_split_craftsman_vs_mold", desc: "06 split craftsman vs mold", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "10_verilog_synthesis_triple", desc: "10 verilog synthesis triple", lane: 1 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "11_synopsys_pdd_equivalence", desc: "11 synopsys pdd equivalence", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "07_craftsman_carving", desc: "07 craftsman carving", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "08_mold_producing_parts", desc: "08 mold producing parts", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "02_factory_floor_wide", desc: "02 factory floor wide", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "12_abstraction_staircase", desc: "12 abstraction staircase", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "03_injection_molding_closeup", desc: "03 injection molding closeup", lane: 0 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "05_defect_and_mold_fix", desc: "05 defect and mold fix", lane: 0 },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "09_1980s_chip_lab", desc: "09 1980s chip lab", lane: 0 },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "13_billion_gate_unreviewable", desc: "13 billion gate unreviewable", lane: 0 },
];

export const Part2ParadigmShiftSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftSectionProps: z.infer<typeof Part2ParadigmShiftSectionProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftSectionPropsType = z.infer<typeof Part2ParadigmShiftSectionProps>;
