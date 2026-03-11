import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 12.117;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(4.039),
  VISUAL_01_START: s2f(4.039),
  VISUAL_01_END: s2f(8.078),
  VISUAL_02_START: s2f(8.078),
  VISUAL_02_END: s2f(12.117),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "animation_section_01_title_card", desc: "Animation Section Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "animation_section_02_key_visual", desc: "Animation Section Key Visual" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "animation_section_03_split_summary", desc: "Animation Section Split Summary" },
];

export const AnimationSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAnimationSectionProps: z.infer<typeof AnimationSectionProps> = {
  showTitle: true,
};

export type AnimationSectionPropsType = z.infer<typeof AnimationSectionProps>;
