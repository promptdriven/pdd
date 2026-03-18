import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 0.427;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.093),
  VISUAL_00_END: s2f(0.127),
  VISUAL_01_START: s2f(0.127),
  VISUAL_01_END: s2f(0.160),
  VISUAL_02_START: s2f(0.160),
  VISUAL_02_END: s2f(0.193),
  VISUAL_03_START: s2f(0.193),
  VISUAL_03_END: s2f(0.227),
  VISUAL_04_START: s2f(0.227),
  VISUAL_04_END: s2f(0.260),
  VISUAL_05_START: s2f(0.260),
  VISUAL_05_END: s2f(0.293),
  VISUAL_06_START: s2f(0.293),
  VISUAL_06_END: s2f(0.327),
  VISUAL_07_START: s2f(0.327),
  VISUAL_07_END: s2f(0.360),
  VISUAL_08_START: s2f(0.360),
  VISUAL_08_END: s2f(0.393),
  VISUAL_09_START: s2f(0.393),
  VISUAL_09_END: s2f(0.427),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "Section 1.0: Part 1 Section Title — The Economics of Darning" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_sock_economics_chart", desc: "Section 1.1: Sock Economics Chart — Labor Cost vs Garment Cost" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_code_cost_triple_line", desc: "Section 1.2: Code Cost Triple-Line Chart — Generate vs Patch vs Total" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_research_annotations", desc: "Section 1.3: Research Annotations — Stacking the Evidence" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_context_window_shrink", desc: "Section 1.4: Context Window Shrink — The AI Blindspot" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_two_by_two_grid", desc: "Section 1.5: Two-by-Two Grid — Why Studies Contradict" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_split_context_comparison", desc: "Section 1.6: Split Context Comparison — Agentic Patching vs PDD Regeneration" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_developer_patching_montage", desc: "Section 1.7: Developer Patching Montage — Still Darning" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_crossing_lines_moment", desc: "Section 1.8: Crossing Lines Moment — Generation Beats Total Cost" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_double_meter_insight", desc: "Section 1.9: Double Meter Insight — The Key Insight Beat" },
];

export const Part1EconomicsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsSectionProps: z.infer<typeof Part1EconomicsSectionProps> = {
  showTitle: true,
};

export type Part1EconomicsSectionPropsType = z.infer<typeof Part1EconomicsSectionProps>;
