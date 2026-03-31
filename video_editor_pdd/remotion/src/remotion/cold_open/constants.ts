import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 49.180;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(12.980),
  VISUAL_01_START: s2f(14.740),
  VISUAL_01_END: s2f(18.440),
  VISUAL_02_START: s2f(19.900),
  VISUAL_02_END: s2f(26.480),
  VISUAL_03_START: s2f(26.620),
  VISUAL_03_END: s2f(32.960),
  VISUAL_04_START: s2f(27.860),
  VISUAL_04_END: s2f(32.960),
  VISUAL_05_START: s2f(27.860),
  VISUAL_05_END: s2f(46.040),
  VISUAL_06_START: s2f(33.160),
  VISUAL_06_END: s2f(46.040),
  VISUAL_07_START: s2f(46.300),
  VISUAL_07_END: s2f(49.180),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_split_developer_grandmother", desc: "01 split developer grandmother", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "06_veo_sock_discard", desc: "06 veo sock discard", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "07_code_cursor_blink", desc: "07 code cursor blink", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "08_code_regeneration", desc: "08 code regeneration", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "09_title_card_pdd", desc: "09 title card pdd", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "10_prompt_file_generate", desc: "10 prompt file generate", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "11_test_fix_regenerate", desc: "11 test fix regenerate", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "12_transition_overlay", desc: "12 transition overlay", lane: 0 },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> = {
  showTitle: true,
};

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
