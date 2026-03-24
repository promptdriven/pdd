import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 455.440;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(0.520),
  VISUAL_01_START: s2f(0.740),
  VISUAL_01_END: s2f(19.860),
  VISUAL_02_START: s2f(19.860),
  VISUAL_02_END: s2f(86.960),
  VISUAL_03_START: s2f(86.960),
  VISUAL_03_END: s2f(158.500),
  VISUAL_04_START: s2f(158.500),
  VISUAL_04_END: s2f(212.320),
  VISUAL_05_START: s2f(212.320),
  VISUAL_05_END: s2f(255.580),
  VISUAL_06_START: s2f(277.540),
  VISUAL_06_END: s2f(321.080),
  VISUAL_07_START: s2f(321.300),
  VISUAL_07_END: s2f(331.820),
  VISUAL_08_START: s2f(321.080),
  VISUAL_08_END: s2f(455.440),
  VISUAL_09_START: s2f(455.440),
  VISUAL_09_END: s2f(455.440),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_sock_economics_chart", desc: "02 sock economics chart", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_code_cost_triple_line", desc: "03 code cost triple line", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_research_annotations", desc: "04 research annotations", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_context_window_shrink", desc: "05 context window shrink", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_two_by_two_grid", desc: "06 two by two grid", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_split_context_comparison", desc: "07 split context comparison", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_developer_patching_montage", desc: "08 developer patching montage", lane: 1 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_crossing_lines_moment", desc: "09 crossing lines moment", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_double_meter_insight", desc: "10 double meter insight", lane: 0 },
];

export const Part1EconomicsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsSectionProps: z.infer<typeof Part1EconomicsSectionProps> = {
  showTitle: true,
};

export type Part1EconomicsSectionPropsType = z.infer<typeof Part1EconomicsSectionProps>;
