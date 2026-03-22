import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 17.540;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(3.184),
  VISUAL_01_START: s2f(3.184),
  VISUAL_01_END: s2f(6.369),
  VISUAL_02_START: s2f(6.369),
  VISUAL_02_END: s2f(9.553),
  VISUAL_03_START: s2f(9.553),
  VISUAL_03_END: s2f(12.738),
  VISUAL_04_START: s2f(12.738),
  VISUAL_04_END: s2f(14.649),
  VISUAL_05_START: s2f(14.649),
  VISUAL_05_END: s2f(15.922),
  VISUAL_06_START: s2f(15.922),
  VISUAL_06_END: s2f(16.559),
  VISUAL_07_START: s2f(16.559),
  VISUAL_07_END: s2f(17.540),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_split_screen_hook", desc: "Section 0.1: Split Screen Hook — Developer vs Grandmother" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_developer_ai_edit", desc: "Section 0.1a: Developer AI Edit — Companion Clip" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_grandmother_darning", desc: "Section 0.1b: Grandmother Darning — Companion Clip" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_zoom_out_accumulated", desc: "Section 0.2: Zoom Out — Accumulated Patches Reveal" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_sock_toss", desc: "Section 0.3: Sock Toss — She Stopped" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_code_blink_patched", desc: "Section 0.4: Code Blink — Delete and Regenerate" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_code_regeneration", desc: "Section 0.4b: Code Regeneration Hold — The Cursor Blinks" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_pdd_title_card", desc: "Section 0.5: PDD Title Card — Prompt-Driven Development" },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
