import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 7.381;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(1.496),
  VISUAL_01_START: s2f(1.496),
  VISUAL_01_END: s2f(2.494),
  VISUAL_02_START: s2f(2.494),
  VISUAL_02_END: s2f(3.691),
  VISUAL_03_START: s2f(3.691),
  VISUAL_03_END: s2f(4.688),
  VISUAL_04_START: s2f(4.688),
  VISUAL_04_END: s2f(5.686),
  VISUAL_05_START: s2f(5.686),
  VISUAL_05_END: s2f(6.683),
  VISUAL_06_START: s2f(6.683),
  VISUAL_06_END: s2f(7.381),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "animation_section_01_title_card", desc: "Section 1.1: Animation Section Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_blue_circle_pulse", desc: "Section 1.2: Blue Circle Pulse" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_circle_to_square_morph", desc: "Section 1.3: Circle to Square Morph" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_square_slide_right", desc: "Section 1.4: Square Slide Right" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_split_comparison", desc: "Section 1.5: Split Comparison" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_particle_burst", desc: "Section 1.6: Particle Burst" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_section_outro", desc: "Section 1.7: Section Outro" },
];

export const AnimationSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAnimationSectionProps: z.infer<typeof AnimationSectionProps> = {
  showTitle: true,
};

export type AnimationSectionPropsType = z.infer<typeof AnimationSectionProps>;
