import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 111.840;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(6.620),
  VISUAL_01_START: s2f(6.840),
  VISUAL_01_END: s2f(26.580),
  VISUAL_02_START: s2f(26.800),
  VISUAL_02_END: s2f(47.000),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_printer_vs_mold_split", desc: "02 printer vs mold split", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_precision_tradeoff_curve", desc: "03 precision tradeoff curve", lane: 0 },
];

export const Part4PrecisionTradeoffSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart4PrecisionTradeoffSectionProps: z.infer<typeof Part4PrecisionTradeoffSectionProps> = {
  showTitle: true,
};

export type Part4PrecisionTradeoffSectionPropsType = z.infer<typeof Part4PrecisionTradeoffSectionProps>;
