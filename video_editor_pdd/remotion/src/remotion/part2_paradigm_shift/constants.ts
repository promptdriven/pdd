import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 228.053;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(2.335),
  VISUAL_01_START: s2f(2.335),
  VISUAL_01_END: s2f(5.448),
  VISUAL_02_START: s2f(5.448),
  VISUAL_02_END: s2f(8.173),
  VISUAL_03_START: s2f(8.173),
  VISUAL_03_END: s2f(228.053),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "02_factory_floor_intro", desc: "Section 2.2: Factory Floor Intro — Industrial Setting" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "03_injection_molding_process", desc: "Section 2.3: Injection Molding Process — Mold Opens, Parts Eject" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "06_chip_design_history", desc: "Section 2.6: Chip Design History — 1980s Electronics Lab" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "part2_paradigm_shift_main", desc: "Part2 Paradigm Shift Main" },
];

export const Part2ParadigmShiftSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftSectionProps: z.infer<typeof Part2ParadigmShiftSectionProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftSectionPropsType = z.infer<typeof Part2ParadigmShiftSectionProps>;
