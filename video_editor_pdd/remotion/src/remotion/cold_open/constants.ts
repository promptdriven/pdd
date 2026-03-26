import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 17.540;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(17.540),
  VISUAL_01_START: s2f(0.000),
  VISUAL_01_END: s2f(17.540),
  VISUAL_02_START: s2f(0.000),
  VISUAL_02_END: s2f(17.540),
  VISUAL_03_START: s2f(9.567),
  VISUAL_03_END: s2f(17.540),
  VISUAL_04_START: s2f(9.567),
  VISUAL_04_END: s2f(17.540),
  VISUAL_05_START: s2f(12.756),
  VISUAL_05_END: s2f(17.540),
  VISUAL_06_START: s2f(13.781),
  VISUAL_06_END: s2f(17.540),
  VISUAL_07_START: s2f(15.348),
  VISUAL_07_END: s2f(17.540),
  VISUAL_08_START: s2f(15.348),
  VISUAL_08_END: s2f(17.540),
  VISUAL_09_START: s2f(15.591),
  VISUAL_09_END: s2f(17.540),
  VISUAL_10_START: s2f(17.540),
  VISUAL_10_END: s2f(17.540),
  VISUAL_11_START: s2f(17.540),
  VISUAL_11_END: s2f(17.540),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_split_screen_darning", desc: "01 split screen darning", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_developer_cursor_edit", desc: "02 developer cursor edit", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_grandmother_darning", desc: "03 grandmother darning", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_developer_codebase_zoomout", desc: "04 developer codebase zoomout", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_grandmother_drawer_zoomout", desc: "05 grandmother drawer zoomout", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "10_transition_beat", desc: "10 transition beat", lane: 1 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "06_sock_toss", desc: "06 sock toss", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "07_code_cursor_blink", desc: "07 code cursor blink", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "08_code_regeneration", desc: "08 code regeneration", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "09_title_card_pdd", desc: "09 title card pdd", lane: 0 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "01_split_screen_hook", desc: "01 split screen hook", lane: 0 },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "07_pdd_title_card", desc: "07 pdd title card", lane: 0 },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
