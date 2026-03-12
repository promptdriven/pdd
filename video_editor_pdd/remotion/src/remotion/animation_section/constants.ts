import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 7.320;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(3.000),
  VISUAL_01_START: s2f(3.000),
  VISUAL_01_END: s2f(7.320),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "animation_section_01_title_card", desc: "Section 1.1: Animation Section Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_blue_circle_pulse", desc: "Section 1.2: Blue Circle Pulse" },
];

export const AnimationSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAnimationSectionProps: z.infer<typeof AnimationSectionProps> = {
  showTitle: true,
};

export type AnimationSectionPropsType = z.infer<typeof AnimationSectionProps>;
