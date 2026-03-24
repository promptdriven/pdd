import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 20.660;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(20.660),
  VISUAL_00_END: s2f(20.660),
  VISUAL_01_START: s2f(20.660),
  VISUAL_01_END: s2f(20.660),
  VISUAL_02_START: s2f(20.520),
  VISUAL_02_END: s2f(20.660),
  VISUAL_03_START: s2f(20.660),
  VISUAL_03_END: s2f(20.660),
  VISUAL_04_START: s2f(20.660),
  VISUAL_04_END: s2f(20.660),
  VISUAL_05_START: s2f(20.660),
  VISUAL_05_END: s2f(20.660),
  VISUAL_06_START: s2f(20.660),
  VISUAL_06_END: s2f(20.660),
  VISUAL_07_START: s2f(20.660),
  VISUAL_07_END: s2f(20.660),
  VISUAL_08_START: s2f(20.660),
  VISUAL_08_END: s2f(20.660),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_sock_callback_split", desc: "01 sock callback split", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_sock_discard_veo", desc: "02 sock discard veo", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_code_regenerate_workflow", desc: "03 code regenerate workflow", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_pdd_triangle", desc: "04 pdd triangle", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_dissolve_regenerate_loop", desc: "05 dissolve regenerate loop", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_mold_glow_finale", desc: "06 mold glow finale", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_the_beat", desc: "07 the beat", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_mold_is_what_matters", desc: "08 mold is what matters", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_final_title_card", desc: "09 final title card", lane: 0 },
];

export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
