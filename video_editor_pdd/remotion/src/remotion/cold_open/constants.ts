import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 17.540;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(4.176),
  VISUAL_01_START: s2f(4.176),
  VISUAL_01_END: s2f(8.352),
  VISUAL_02_START: s2f(8.352),
  VISUAL_02_END: s2f(12.529),
  VISUAL_03_START: s2f(12.529),
  VISUAL_03_END: s2f(15.034),
  VISUAL_04_START: s2f(15.034),
  VISUAL_04_END: s2f(16.705),
  VISUAL_05_START: s2f(16.705),
  VISUAL_05_END: s2f(17.540),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_split_screen_hook", desc: "Section 0.1: Split Screen Hook" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_developer_ai_edit", desc: "Section 0.1a: Developer AI Edit" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_grandmother_darning", desc: "Section 0.1b: Grandmother Darning by Lamplight" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "05_sock_toss", desc: "Section 0.3: Sock Toss" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "06_code_blink_patched", desc: "Section 0.4: Cursor Blink on Patched Code" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "07_code_regeneration", desc: "Section 0.5: Code Regeneration" },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
