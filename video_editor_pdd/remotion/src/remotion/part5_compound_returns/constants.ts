import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 115.322;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(4.522),
  VISUAL_01_START: s2f(4.522),
  VISUAL_01_END: s2f(20.351),
  VISUAL_02_START: s2f(20.351),
  VISUAL_02_END: s2f(33.918),
  VISUAL_03_START: s2f(33.918),
  VISUAL_03_END: s2f(49.747),
  VISUAL_04_START: s2f(49.747),
  VISUAL_04_END: s2f(65.575),
  VISUAL_05_START: s2f(65.575),
  VISUAL_05_END: s2f(79.142),
  VISUAL_06_START: s2f(79.142),
  VISUAL_06_END: s2f(90.448),
  VISUAL_07_START: s2f(90.448),
  VISUAL_07_END: s2f(101.754),
  VISUAL_08_START: s2f(101.754),
  VISUAL_08_END: s2f(108.538),
  VISUAL_09_START: s2f(108.538),
  VISUAL_09_END: s2f(115.322),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "Section 5.1: Part 5 Title Card — Compound Returns" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_maintenance_pie_chart", desc: "Section 5.2: Maintenance Pie Chart — Where the Money Goes" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_compound_debt_curve", desc: "Section 5.3: Compound Debt Curve — The Math of Accumulation" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_diverging_cost_curves", desc: "Section 5.4: Diverging Cost Curves — The Compounding Gap" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_investment_comparison_table", desc: "Section 5.5: Investment Comparison Table — Compounds For You" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_sock_callback_split", desc: "Section 5.6: Sock Callback — Split Screen Emotional Payoff" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_economics_crossing_callback", desc: "Section 5.7: Economics Crossing Callback — The Chart Returns" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_contrarian_quote_card", desc: "Section 5.8: Contrarian Quote Card — The Bet" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_grandmother_realization", desc: "Section 5.9: Grandmother Realization — Setting Down the Needle" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_developer_prompt_shift", desc: "Section 5.10: Developer Prompt Shift — Closing the Diff" },
];

export const Part5CompoundReturnsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart5CompoundReturnsSectionProps: z.infer<typeof Part5CompoundReturnsSectionProps> = {
  showTitle: true,
};

export type Part5CompoundReturnsSectionPropsType = z.infer<typeof Part5CompoundReturnsSectionProps>;
