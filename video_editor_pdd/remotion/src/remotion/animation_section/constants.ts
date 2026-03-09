import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 21;
export const SECTION_DURATION_FRAMES = SECTION_FPS * SECTION_DURATION_SECONDS;

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(3.0),
  VISUAL_01_START: s2f(3.0),
  VISUAL_01_END: s2f(6.0),
  VISUAL_02_START: s2f(6.0),
  VISUAL_02_END: s2f(9.0),
  VISUAL_03_START: s2f(9.0),
  VISUAL_03_END: s2f(12.0),
  VISUAL_04_START: s2f(12.0),
  VISUAL_04_END: s2f(15.0),
  VISUAL_05_START: s2f(15.0),
  VISUAL_05_END: s2f(18.0),
  VISUAL_06_START: s2f(18.0),
  VISUAL_06_END: s2f(21.0),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "animation_section_01_title_card", desc: "Title card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_blue_circle_pulse", desc: "Blue circle pulse" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_circle_to_square_transform", desc: "Circle to square transform" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_shape_showcase", desc: "Shape showcase" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_animation_timeline", desc: "Animation timeline" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_split_before_after", desc: "Split before after" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_section_closing_card", desc: "Section closing card" },
];

export const AnimationSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAnimationSectionProps: z.infer<typeof AnimationSectionProps> = {
  showTitle: true,
};

export type AnimationSectionPropsType = z.infer<typeof AnimationSectionProps>;
