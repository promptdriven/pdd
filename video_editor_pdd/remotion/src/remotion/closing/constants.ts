import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 15.420;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(1.440),
  VISUAL_01_START: s2f(2.140),
  VISUAL_01_END: s2f(7.580),
  VISUAL_02_START: s2f(2.140),
  VISUAL_02_END: s2f(10.940),
  VISUAL_03_START: s2f(7.820),
  VISUAL_03_END: s2f(13.260),
  VISUAL_04_START: s2f(11.380),
  VISUAL_04_END: s2f(15.420),
  VISUAL_05_START: s2f(11.397),
  VISUAL_05_END: s2f(15.420),
  VISUAL_06_START: s2f(13.606),
  VISUAL_06_END: s2f(15.420),
  VISUAL_07_START: s2f(15.420),
  VISUAL_07_END: s2f(15.420),
  VISUAL_08_START: s2f(15.420),
  VISUAL_08_END: s2f(15.420),
  VISUAL_09_START: s2f(15.420),
  VISUAL_09_END: s2f(15.420),
  VISUAL_10_START: s2f(15.420),
  VISUAL_10_END: s2f(15.420),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_veo_sock_discard", desc: "01 veo sock discard", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_veo_developer_regenerate", desc: "02 veo developer regenerate", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_pdd_triangle", desc: "03 pdd triangle", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_dissolve_regenerate_loop", desc: "04 dissolve regenerate loop", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_veo_mold_glow_finale", desc: "05 veo mold glow finale", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "07_final_title_card", desc: "07 final title card", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "06_the_beat", desc: "06 the beat", lane: 0 },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "04_pdd_triangle", desc: "04 pdd triangle", lane: 0 },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "05_dissolve_regenerate_loop", desc: "05 dissolve regenerate loop", lane: 0 },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "06_mold_glow_finale", desc: "06 mold glow finale", lane: 0 },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "07_the_beat", desc: "07 the beat", lane: 0 },
];

export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
