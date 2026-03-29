import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 16.260;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(1.440),
  VISUAL_01_START: s2f(1.860),
  VISUAL_01_END: s2f(8.400),
  VISUAL_02_START: s2f(1.860),
  VISUAL_02_END: s2f(11.820),
  VISUAL_03_START: s2f(8.700),
  VISUAL_03_END: s2f(14.100),
  VISUAL_04_START: s2f(12.018),
  VISUAL_04_END: s2f(16.260),
  VISUAL_05_START: s2f(12.220),
  VISUAL_05_END: s2f(16.260),
  VISUAL_06_START: s2f(14.347),
  VISUAL_06_END: s2f(16.260),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_veo_sock_discard", desc: "01 veo sock discard", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_veo_developer_regenerate", desc: "02 veo developer regenerate", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_pdd_triangle", desc: "03 pdd triangle", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_dissolve_regenerate_loop", desc: "04 dissolve regenerate loop", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "07_final_title_card", desc: "07 final title card", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "05_veo_mold_glow_finale", desc: "05 veo mold glow finale", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "06_the_beat", desc: "06 the beat", lane: 0 },
];

export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
