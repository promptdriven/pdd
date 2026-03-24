import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 227.480;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(227.480),
  VISUAL_01_START: s2f(227.480),
  VISUAL_01_END: s2f(227.480),
  VISUAL_02_START: s2f(227.480),
  VISUAL_02_END: s2f(227.480),
  VISUAL_03_START: s2f(227.480),
  VISUAL_03_END: s2f(227.480),
  VISUAL_04_START: s2f(227.480),
  VISUAL_04_END: s2f(227.480),
  VISUAL_05_START: s2f(227.480),
  VISUAL_05_END: s2f(227.480),
  VISUAL_06_START: s2f(227.480),
  VISUAL_06_END: s2f(227.480),
  VISUAL_07_START: s2f(227.480),
  VISUAL_07_END: s2f(227.480),
  VISUAL_08_START: s2f(227.480),
  VISUAL_08_END: s2f(227.480),
  VISUAL_09_START: s2f(227.480),
  VISUAL_09_END: s2f(227.480),
  VISUAL_10_START: s2f(227.480),
  VISUAL_10_END: s2f(227.480),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_factory_floor_intro", desc: "02 factory floor intro", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_injection_molding_process", desc: "03 injection molding process", lane: 1 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_defect_fix_the_mold", desc: "04 defect fix the mold", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_value_migration_split", desc: "05 value migration split", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_chip_design_history", desc: "06 chip design history", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_verilog_synthesis_triple", desc: "07 verilog synthesis triple", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_synopsys_pdd_equivalence", desc: "08 synopsys pdd equivalence", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_abstraction_staircase", desc: "09 abstraction staircase", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_netlist_zoom_unreviewable", desc: "10 netlist zoom unreviewable", lane: 0 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "11_prompt_replaces_review", desc: "11 prompt replaces review", lane: 0 },
];

export const Part2ParadigmShiftSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftSectionProps: z.infer<typeof Part2ParadigmShiftSectionProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftSectionPropsType = z.infer<typeof Part2ParadigmShiftSectionProps>;
