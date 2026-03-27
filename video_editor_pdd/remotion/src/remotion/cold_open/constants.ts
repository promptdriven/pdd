import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 17.900;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(8.660),
  VISUAL_01_START: s2f(0.000),
  VISUAL_01_END: s2f(17.900),
  VISUAL_02_START: s2f(0.000),
  VISUAL_02_END: s2f(17.900),
  VISUAL_03_START: s2f(9.944),
  VISUAL_03_END: s2f(17.900),
  VISUAL_04_START: s2f(9.944),
  VISUAL_04_END: s2f(17.900),
  VISUAL_05_START: s2f(12.786),
  VISUAL_05_END: s2f(17.900),
  VISUAL_06_START: s2f(14.240),
  VISUAL_06_END: s2f(15.800),
  VISUAL_07_START: s2f(16.040),
  VISUAL_07_END: s2f(17.900),
  VISUAL_08_START: s2f(16.040),
  VISUAL_08_END: s2f(17.900),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_split_screen_darning", desc: "01 split screen darning", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_developer_cursor_edit", desc: "02 developer cursor edit", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_grandmother_darning", desc: "03 grandmother darning", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_developer_codebase_zoomout", desc: "04 developer codebase zoomout", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_grandmother_drawer_zoomout", desc: "05 grandmother drawer zoomout", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_sock_toss", desc: "06 sock toss", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_code_cursor_blink", desc: "07 code cursor blink", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_code_regeneration", desc: "08 code regeneration", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_title_card_pdd", desc: "09 title card pdd", lane: 0 },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
