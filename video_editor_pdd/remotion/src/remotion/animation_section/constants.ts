import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 7.787;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(3.006),
  VISUAL_01_START: s2f(3.006),
  VISUAL_01_END: s2f(3.039),
  VISUAL_02_START: s2f(3.039),
  VISUAL_02_END: s2f(3.072),
  VISUAL_03_START: s2f(3.072),
  VISUAL_03_END: s2f(3.106),
  VISUAL_04_START: s2f(3.106),
  VISUAL_04_END: s2f(3.139),
  VISUAL_05_START: s2f(3.139),
  VISUAL_05_END: s2f(3.172),
  VISUAL_06_START: s2f(3.172),
  VISUAL_06_END: s2f(6.178),
  VISUAL_07_START: s2f(6.178),
  VISUAL_07_END: s2f(6.597),
  VISUAL_08_START: s2f(6.597),
  VISUAL_08_END: s2f(7.016),
  VISUAL_09_START: s2f(7.016),
  VISUAL_09_END: s2f(7.434),
  VISUAL_10_START: s2f(7.434),
  VISUAL_10_END: s2f(7.787),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "animation_section_01_title_card", desc: "Animation Section 01 Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_blue_circle_pulse", desc: "Blue Circle Pulse" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_circle_to_square_morph", desc: "Circle To Square Morph" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_square_slide_right", desc: "Square Slide Right" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_split_comparison", desc: "Split Comparison" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_particle_burst", desc: "Particle Burst" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_section_outro", desc: "Section Outro" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_key_visual", desc: "Key Visual" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_split_summary", desc: "Split Summary" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "animation_section_02_key_visual", desc: "Animation Section 02 Key Visual" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "animation_section_03_split_summary", desc: "Animation Section 03 Split Summary" },
];

export const AnimationSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAnimationSectionProps: z.infer<typeof AnimationSectionProps> = {
  showTitle: true,
};

export type AnimationSectionPropsType = z.infer<typeof AnimationSectionProps>;
