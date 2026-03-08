import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 7.32;
export const SECTION_DURATION_FRAMES = 220;

export const BEATS = {
  VISUAL_00_START: 0,
  VISUAL_00_END: 73,
  VISUAL_01_START: 73,
  VISUAL_01_END: 146,
  VISUAL_02_START: 146,
  VISUAL_02_END: 220,
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "animation_section_01_title_card", desc: "Animation Section 01 Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "animation_section_02_key_visual", desc: "Animation Section 02 Key Visual" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "animation_section_03_split_summary", desc: "Animation Section 03 Split Summary" },
];

export const AnimationSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAnimationSectionProps: z.infer<typeof AnimationSectionProps> = {
  showTitle: true,
};

export type AnimationSectionPropsType = z.infer<typeof AnimationSectionProps>;
