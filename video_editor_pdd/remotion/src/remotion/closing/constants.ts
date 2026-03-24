import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 20.660;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(2.600),
  VISUAL_01_START: s2f(0.000),
  VISUAL_01_END: s2f(12.280),
  VISUAL_02_START: s2f(0.000),
  VISUAL_02_END: s2f(12.280),
  VISUAL_03_START: s2f(2.940),
  VISUAL_03_END: s2f(12.280),
  VISUAL_04_START: s2f(12.540),
  VISUAL_04_END: s2f(18.820),
  VISUAL_05_START: s2f(15.680),
  VISUAL_05_END: s2f(18.820),
  VISUAL_06_START: s2f(18.820),
  VISUAL_06_END: s2f(19.140),
  VISUAL_07_START: s2f(19.140),
  VISUAL_07_END: s2f(20.660),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_sock_callback_discard", desc: "01 sock callback discard", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_code_regenerate_workflow", desc: "02 code regenerate workflow", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_developer_regenerate_clip", desc: "03 developer regenerate clip", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_pdd_triangle", desc: "04 pdd triangle", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_dissolve_regenerate_loop", desc: "05 dissolve regenerate loop", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_mold_glow_finale", desc: "06 mold glow finale", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_the_beat", desc: "07 the beat", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_final_title_card", desc: "08 final title card", lane: 0 },
];

export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
