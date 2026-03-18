import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 0.363;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(0.067),
  VISUAL_01_START: s2f(0.067),
  VISUAL_01_END: s2f(0.127),
  VISUAL_02_START: s2f(0.127),
  VISUAL_02_END: s2f(0.169),
  VISUAL_03_START: s2f(0.169),
  VISUAL_03_END: s2f(0.211),
  VISUAL_04_START: s2f(0.211),
  VISUAL_04_END: s2f(0.278),
  VISUAL_05_START: s2f(0.278),
  VISUAL_05_END: s2f(0.320),
  VISUAL_06_START: s2f(0.320),
  VISUAL_06_END: s2f(0.363),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_split_screen_hook", desc: "Section 0.1: Split Screen Hook — Developer Meets Grandmother" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_zoom_out_accumulated", desc: "Section 0.2: Zoom Out — Accumulated Weight" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_grandmother_lamplight", desc: "Section 0.3: Grandmother by Lamplight — The Craft" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_sock_toss", desc: "Section 0.4: Sock Toss — Economics in Action" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_code_blink", desc: "Section 0.5: Code Blink — Delete and Regenerate" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_still_patching_beat", desc: "Section 0.6: \"So Why Are We Still Patching?\" — The Beat" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_pdd_title_card", desc: "Section 0.7: PDD Title Card — The Promise" },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
