import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 17.540;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(2.300),
  VISUAL_01_START: s2f(2.300),
  VISUAL_01_END: s2f(4.601),
  VISUAL_02_START: s2f(4.601),
  VISUAL_02_END: s2f(6.613),
  VISUAL_03_START: s2f(6.613),
  VISUAL_03_END: s2f(8.339),
  VISUAL_04_START: s2f(8.339),
  VISUAL_04_END: s2f(10.639),
  VISUAL_05_START: s2f(10.639),
  VISUAL_05_END: s2f(12.077),
  VISUAL_06_START: s2f(12.077),
  VISUAL_06_END: s2f(14.665),
  VISUAL_07_START: s2f(14.665),
  VISUAL_07_END: s2f(15.815),
  VISUAL_08_START: s2f(15.815),
  VISUAL_08_END: s2f(17.540),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_split_screen_hook", desc: "Section 0.1: Split Screen Hook — Developer Meets Grandmother" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_grandmother_lamplight", desc: "Section 0.2: Grandmother Lamplight — Darning by Warm Light" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_zoom_out_accumulated", desc: "Section 0.3: Zoom Out Accumulated — The Weight of Careful Repair" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_sock_toss", desc: "Section 0.4: Sock Toss — When Socks Got Cheap Enough" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_developer_cursor_broll", desc: "Section 0.5: Developer Cursor B-Roll — AI-Assisted Code Edit" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_code_blink_patched", desc: "Section 0.6: Code Blink — The Patched Function" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_code_regeneration", desc: "Section 0.7: Code Regeneration — Delete and Rebuild" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_still_patching_beat", desc: "Section 0.8: Still Patching Beat — The Question Lingers" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_pdd_title_card", desc: "Section 0.9: PDD Title Card — Prompt-Driven Development" },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
