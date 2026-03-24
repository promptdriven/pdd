import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 227.480;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(2.840),
  VISUAL_01_START: s2f(48.820),
  VISUAL_01_END: s2f(67.460),
  VISUAL_02_START: s2f(59.060),
  VISUAL_02_END: s2f(76.940),
  VISUAL_03_START: s2f(85.560),
  VISUAL_03_END: s2f(110.300),
  VISUAL_04_START: s2f(110.480),
  VISUAL_04_END: s2f(139.640),
  VISUAL_05_START: s2f(139.840),
  VISUAL_05_END: s2f(178.040),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "03_factory_floor_intro", desc: "03 factory floor intro", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "04_injection_molding_process", desc: "04 injection molding process", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "06_craftsman_vs_mold", desc: "06 craftsman vs mold", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "09_1980s_chip_lab", desc: "09 1980s chip lab", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "10_verilog_synthesis_triple", desc: "10 verilog synthesis triple", lane: 0 },
];

export const Part2ParadigmShiftSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftSectionProps: z.infer<typeof Part2ParadigmShiftSectionProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftSectionPropsType = z.infer<typeof Part2ParadigmShiftSectionProps>;
