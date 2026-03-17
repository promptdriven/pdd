import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 228.053;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(182.014),
  VISUAL_00_END: s2f(183.442),
  VISUAL_01_START: s2f(183.442),
  VISUAL_01_END: s2f(185.583),
  VISUAL_02_START: s2f(185.583),
  VISUAL_02_END: s2f(188.438),
  VISUAL_03_START: s2f(188.438),
  VISUAL_03_END: s2f(193.435),
  VISUAL_04_START: s2f(193.435),
  VISUAL_04_END: s2f(199.145),
  VISUAL_05_START: s2f(199.145),
  VISUAL_05_END: s2f(201.643),
  VISUAL_06_START: s2f(201.643),
  VISUAL_06_END: s2f(208.067),
  VISUAL_07_START: s2f(208.067),
  VISUAL_07_END: s2f(212.350),
  VISUAL_08_START: s2f(212.350),
  VISUAL_08_END: s2f(218.060),
  VISUAL_09_START: s2f(218.060),
  VISUAL_09_END: s2f(223.771),
  VISUAL_10_START: s2f(223.771),
  VISUAL_10_END: s2f(228.053),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "Section 2.1: Part 2 Title Card — The Paradigm Shift" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_factory_floor_intro", desc: "Section 2.2: Factory Floor Intro — Industrial Setting" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_injection_molding_process", desc: "Section 2.3: Injection Molding Process — Mold Opens, Parts Eject" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_defect_fix_the_mold", desc: "Section 2.4: Defect → Fix the Mold — Not the Part" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_value_migration_split", desc: "Section 2.5: Value Migration Split — Crafting vs Molding" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_chip_design_history", desc: "Section 2.6: Chip Design History — 1980s Electronics Lab" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_verilog_synthesis_triple", desc: "Section 2.7: Verilog Synthesis Triple — Non-Deterministic Output" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_synopsys_pdd_equivalence", desc: "Section 2.8: Synopsys ↔ PDD Equivalence — Same Architecture" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_abstraction_staircase", desc: "Section 2.9: Abstraction Staircase — Chip Design Levels Through Decades" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_netlist_zoom_unreviewable", desc: "Section 2.10: Netlist Zoom — Unreviewable at Scale" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "11_prompt_replaces_review", desc: "Section 2.11: Prompt Replaces Review — Spec + Tests vs. Code Review" },
];

export const Part2ParadigmShiftSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftSectionProps: z.infer<typeof Part2ParadigmShiftSectionProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftSectionPropsType = z.infer<typeof Part2ParadigmShiftSectionProps>;
