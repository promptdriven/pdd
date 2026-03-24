import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 17.540;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(11.280),
  VISUAL_01_START: s2f(0.000),
  VISUAL_01_END: s2f(5.500),
  VISUAL_02_START: s2f(5.500),
  VISUAL_02_END: s2f(11.280),
  VISUAL_03_START: s2f(11.280),
  VISUAL_03_END: s2f(11.280),
  VISUAL_04_START: s2f(11.460),
  VISUAL_04_END: s2f(13.940),
  VISUAL_05_START: s2f(14.120),
  VISUAL_05_END: s2f(15.860),
  VISUAL_06_START: s2f(16.020),
  VISUAL_06_END: s2f(17.540),
  VISUAL_07_START: s2f(17.540),
  VISUAL_07_END: s2f(17.540),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_split_screen_hook", desc: "01 split screen hook", lane: 1 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_developer_ai_edit", desc: "02 developer ai edit", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_grandmother_darning", desc: "03 grandmother darning", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_zoom_out_accumulated", desc: "04 zoom out accumulated", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_sock_toss", desc: "05 sock toss", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_code_blink_patched", desc: "06 code blink patched", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_code_regeneration", desc: "07 code regeneration", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_pdd_title_card", desc: "08 pdd title card", lane: 0 },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
