import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 486.060;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(22.820),
  VISUAL_01_START: s2f(23.060),
  VISUAL_01_END: s2f(29.920),
  VISUAL_02_START: s2f(30.160),
  VISUAL_02_END: s2f(72.900),
  VISUAL_03_START: s2f(72.900),
  VISUAL_03_END: s2f(114.020),
  VISUAL_04_START: s2f(114.020),
  VISUAL_04_END: s2f(142.680),
  VISUAL_05_START: s2f(137.000),
  VISUAL_05_END: s2f(156.780),
  VISUAL_06_START: s2f(142.920),
  VISUAL_06_END: s2f(199.020),
  VISUAL_07_START: s2f(199.020),
  VISUAL_07_END: s2f(239.480),
  VISUAL_08_START: s2f(228.740),
  VISUAL_08_END: s2f(239.480),
  VISUAL_09_START: s2f(239.480),
  VISUAL_09_END: s2f(260.260),
  VISUAL_10_START: s2f(260.260),
  VISUAL_10_END: s2f(313.500),
  VISUAL_11_START: s2f(314.820),
  VISUAL_11_END: s2f(368.980),
  VISUAL_12_START: s2f(368.980),
  VISUAL_12_END: s2f(410.660),
  VISUAL_13_START: s2f(393.100),
  VISUAL_13_END: s2f(410.660),
  VISUAL_14_START: s2f(411.080),
  VISUAL_14_END: s2f(430.800),
  VISUAL_15_START: s2f(423.780),
  VISUAL_15_END: s2f(430.800),
  VISUAL_16_START: s2f(474.300),
  VISUAL_16_END: s2f(486.060),
  VISUAL_17_START: s2f(474.300),
  VISUAL_17_END: s2f(486.060),
  VISUAL_18_START: s2f(478.157),
  VISUAL_18_END: s2f(486.060),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_sock_price_chart", desc: "02 sock price chart", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_code_cost_chart", desc: "03 code cost chart", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_research_annotations", desc: "04 research annotations", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_code_churn_annotations", desc: "05 code churn annotations", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_debt_layers_zoom", desc: "06 debt layers zoom", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_context_window_shrink", desc: "07 context window shrink", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_performance_vs_context", desc: "08 performance vs context", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "08_context_rot_return", desc: "08 context rot return", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "09_two_by_two_grid", desc: "09 two by two grid", lane: 0 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "10_fork_codebase_size", desc: "10 fork codebase size", lane: 0 },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "11_patching_vs_regeneration", desc: "11 patching vs regeneration", lane: 0 },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "12_context_compression", desc: "12 context compression", lane: 0 },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "13_crossing_lines_moment", desc: "13 crossing lines moment", lane: 0 },
  { start: BEATS.VISUAL_14_START, end: BEATS.VISUAL_14_END, id: "14_split_developer_grandma", desc: "14 split developer grandma", lane: 0 },
  { start: BEATS.VISUAL_15_START, end: BEATS.VISUAL_15_END, id: "17_developer_codebase_zoomout", desc: "17 developer codebase zoomout", lane: 1 },
  { start: BEATS.VISUAL_16_START, end: BEATS.VISUAL_16_END, id: "18_key_insight_stillness", desc: "18 key insight stillness", lane: 0 },
  { start: BEATS.VISUAL_17_START, end: BEATS.VISUAL_17_END, id: "19_double_meter_insight", desc: "19 double meter insight", lane: 0 },
  { start: BEATS.VISUAL_18_START, end: BEATS.VISUAL_18_END, id: "20_try_it_yourself", desc: "20 try it yourself", lane: 0 },
];

export const Part1EconomicsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsSectionProps: z.infer<typeof Part1EconomicsSectionProps> = {
  showTitle: true,
};

export type Part1EconomicsSectionPropsType = z.infer<typeof Part1EconomicsSectionProps>;
