import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 10.880;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(1.088),
  VISUAL_01_START: s2f(1.088),
  VISUAL_01_END: s2f(2.901),
  VISUAL_02_START: s2f(2.901),
  VISUAL_02_END: s2f(4.715),
  VISUAL_03_START: s2f(4.715),
  VISUAL_03_END: s2f(6.528),
  VISUAL_04_START: s2f(6.528),
  VISUAL_04_END: s2f(8.341),
  VISUAL_05_START: s2f(8.341),
  VISUAL_05_END: s2f(9.792),
  VISUAL_06_START: s2f(9.792),
  VISUAL_06_END: s2f(10.880),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "animation_section_01_title_card", desc: "Section 1.1: Animation Section Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_blue_circle_pulse", desc: "Section 1.2: Blue Circle Pulse" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_circle_to_square_transform", desc: "Section 1.3: Circle to Square Transform" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_shape_showcase", desc: "Section 1.4: Shape Showcase Infographic" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_animation_timeline", desc: "Section 1.5: Animation Timeline Diagram" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_split_before_after", desc: "Section 1.6: Split Before/After Comparison" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_section_closing_card", desc: "Section 1.7: Section Closing Card" },
];

export const AnimationSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAnimationSectionProps: z.infer<typeof AnimationSectionProps> = {
  showTitle: true,
};

export type AnimationSectionPropsType = z.infer<typeof AnimationSectionProps>;
