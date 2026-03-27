import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 119.180;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(27.080),
  VISUAL_01_START: s2f(0.000),
  VISUAL_01_END: s2f(27.080),
  VISUAL_02_START: s2f(27.440),
  VISUAL_02_END: s2f(43.200),
  VISUAL_03_START: s2f(43.840),
  VISUAL_03_END: s2f(65.660),
  VISUAL_04_START: s2f(66.060),
  VISUAL_04_END: s2f(74.880),
  VISUAL_05_START: s2f(87.760),
  VISUAL_05_END: s2f(97.360),
  VISUAL_06_START: s2f(97.360),
  VISUAL_06_END: s2f(119.180),
  VISUAL_07_START: s2f(109.700),
  VISUAL_07_END: s2f(119.180),
  VISUAL_08_START: s2f(110.352),
  VISUAL_08_END: s2f(119.180),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 1 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_maintenance_pie_chart", desc: "02 maintenance pie chart", lane: 1 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_compound_debt_curve", desc: "03 compound debt curve", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_diverging_cost_curves", desc: "04 diverging cost curves", lane: 1 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_investment_comparison_table", desc: "05 investment comparison table", lane: 1 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "08_economics_crossing_callback", desc: "08 economics crossing callback", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "09_contrarian_quote_card", desc: "09 contrarian quote card", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "07_veo_developer_cursor_callback", desc: "07 veo developer cursor callback", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "06_veo_grandmother_socks_callback", desc: "06 veo grandmother socks callback", lane: 0 },
];

export const Part5CompoundReturnsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart5CompoundReturnsSectionProps: z.infer<typeof Part5CompoundReturnsSectionProps> = {
  showTitle: true,
};

export type Part5CompoundReturnsSectionPropsType = z.infer<typeof Part5CompoundReturnsSectionProps>;
