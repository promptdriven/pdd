import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 455.440;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(23.020),
  VISUAL_01_START: s2f(23.940),
  VISUAL_01_END: s2f(43.280),
  VISUAL_02_START: s2f(43.520),
  VISUAL_02_END: s2f(97.240),
  VISUAL_03_START: s2f(97.460),
  VISUAL_03_END: s2f(164.220),
  VISUAL_04_START: s2f(164.220),
  VISUAL_04_END: s2f(212.320),
  VISUAL_05_START: s2f(212.320),
  VISUAL_05_END: s2f(255.580),
  VISUAL_06_START: s2f(255.580),
  VISUAL_06_END: s2f(321.080),
  VISUAL_07_START: s2f(321.300),
  VISUAL_07_END: s2f(387.960),
  VISUAL_08_START: s2f(388.100),
  VISUAL_08_END: s2f(431.140),
  VISUAL_09_START: s2f(431.360),
  VISUAL_09_END: s2f(447.880),
  VISUAL_10_START: s2f(441.120),
  VISUAL_10_END: s2f(455.440),
  VISUAL_11_START: s2f(448.180),
  VISUAL_11_END: s2f(455.440),
  VISUAL_12_START: s2f(448.180),
  VISUAL_12_END: s2f(455.440),
  VISUAL_13_START: s2f(448.180),
  VISUAL_13_END: s2f(455.440),
  VISUAL_14_START: s2f(448.449),
  VISUAL_14_END: s2f(455.440),
  VISUAL_15_START: s2f(450.490),
  VISUAL_15_END: s2f(455.440),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_sock_price_chart", desc: "02 sock price chart", lane: 1 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_code_cost_chart", desc: "03 code cost chart", lane: 1 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_research_annotations", desc: "04 research annotations", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_context_window_shrink", desc: "05 context window shrink", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_performance_vs_context", desc: "06 performance vs context", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_two_by_two_grid", desc: "07 two by two grid", lane: 1 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_fork_codebase_size", desc: "08 fork codebase size", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_patching_vs_regeneration_split", desc: "09 patching vs regeneration split", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_crossing_lines_moment", desc: "10 crossing lines moment", lane: 0 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "15_double_meter_insight", desc: "15 double meter insight", lane: 1 },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "11_developer_darning_split", desc: "11 developer darning split", lane: 0 },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "12_developer_cursor_coding", desc: "12 developer cursor coding", lane: 0 },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "13_grandmother_darning_expert", desc: "13 grandmother darning expert", lane: 0 },
  { start: BEATS.VISUAL_14_START, end: BEATS.VISUAL_14_END, id: "14_key_insight_stillness", desc: "14 key insight stillness", lane: 0 },
  { start: BEATS.VISUAL_15_START, end: BEATS.VISUAL_15_END, id: "16_try_it_yourself", desc: "16 try it yourself", lane: 0 },
];

export const Part1EconomicsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsSectionProps: z.infer<typeof Part1EconomicsSectionProps> = {
  showTitle: true,
};

export type Part1EconomicsSectionPropsType = z.infer<typeof Part1EconomicsSectionProps>;
