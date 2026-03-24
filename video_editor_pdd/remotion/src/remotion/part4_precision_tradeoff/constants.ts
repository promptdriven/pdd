import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 111.840;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(111.840),
  VISUAL_00_END: s2f(111.840),
  VISUAL_01_START: s2f(109.868),
  VISUAL_01_END: s2f(111.840),
  VISUAL_02_START: s2f(111.840),
  VISUAL_02_END: s2f(111.840),
  VISUAL_03_START: s2f(111.840),
  VISUAL_03_END: s2f(111.840),
  VISUAL_04_START: s2f(111.840),
  VISUAL_04_END: s2f(111.840),
  VISUAL_05_START: s2f(111.840),
  VISUAL_05_END: s2f(111.840),
  VISUAL_06_START: s2f(111.840),
  VISUAL_06_END: s2f(111.840),
  VISUAL_07_START: s2f(111.840),
  VISUAL_07_END: s2f(111.840),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_printer_vs_mold_split", desc: "02 printer vs mold split", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_precision_tradeoff_curve", desc: "03 precision tradeoff curve", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_prompt_comparison_split", desc: "04 prompt comparison split", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_test_accumulation_insight", desc: "05 test accumulation insight", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_takeaway_callout", desc: "06 takeaway callout", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_embedded_code_document", desc: "07 embedded code document", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_prompt_code_spectrum", desc: "08 prompt code spectrum", lane: 0 },
];

export const Part4PrecisionTradeoffSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart4PrecisionTradeoffSectionProps: z.infer<typeof Part4PrecisionTradeoffSectionProps> = {
  showTitle: true,
};

export type Part4PrecisionTradeoffSectionPropsType = z.infer<typeof Part4PrecisionTradeoffSectionProps>;
