import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 112.085;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(103.078),
  VISUAL_00_END: s2f(103.449),
  VISUAL_01_START: s2f(103.449),
  VISUAL_01_END: s2f(105.306),
  VISUAL_02_START: s2f(105.306),
  VISUAL_02_END: s2f(106.699),
  VISUAL_03_START: s2f(106.699),
  VISUAL_03_END: s2f(107.999),
  VISUAL_04_START: s2f(107.999),
  VISUAL_04_END: s2f(108.928),
  VISUAL_05_START: s2f(108.928),
  VISUAL_05_END: s2f(109.485),
  VISUAL_06_START: s2f(109.485),
  VISUAL_06_END: s2f(110.971),
  VISUAL_07_START: s2f(110.971),
  VISUAL_07_END: s2f(112.085),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "Section 4.1: Part 4 Title Card — The Precision Tradeoff" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_printer_vs_mold_split", desc: "Section 4.2: 3D Printer vs Injection Mold — Two Precision Paradigms" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_precision_tradeoff_curve", desc: "Section 4.3: Precision Tradeoff Curve — Tests vs Prompt Precision" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_prompt_comparison_split", desc: "Section 4.4: Prompt Comparison — Dense vs Minimal Prompt Files" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_test_accumulation_insight", desc: "Section 4.5: Test Accumulation Insight — Why Walls Simplify Prompts Over Time" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_takeaway_callout", desc: "Section 4.6: Takeaway Callout — \"More Walls, Less You Specify\"" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_embedded_code_document", desc: "Section 4.7: Embedded Code Document — The Fluid Boundary Between Prompt and Code" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_prompt_code_spectrum", desc: "Section 4.8: Prompt-Code Spectrum — The Fluid Boundary" },
];

export const Part4PrecisionTradeoffSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart4PrecisionTradeoffSectionProps: z.infer<typeof Part4PrecisionTradeoffSectionProps> = {
  showTitle: true,
};

export type Part4PrecisionTradeoffSectionPropsType = z.infer<typeof Part4PrecisionTradeoffSectionProps>;
