import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 7.120;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(1.424),
  VISUAL_01_START: s2f(1.424),
  VISUAL_01_END: s2f(2.848),
  VISUAL_02_START: s2f(2.848),
  VISUAL_02_END: s2f(4.272),
  VISUAL_03_START: s2f(4.272),
  VISUAL_03_END: s2f(5.696),
  VISUAL_04_START: s2f(5.696),
  VISUAL_04_END: s2f(7.120),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo_section_01_title_card", desc: "Veo Section Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "veo_section_02_key_visual", desc: "Veo Section Key Visual" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "veo_section_03_split_summary", desc: "Veo Section Split Summary" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_veo_broll", desc: "Veo Section Veo B-Roll" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_veo_cutaway", desc: "Veo Section Veo Cutaway" },
];

export const VeoSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultVeoSectionProps: z.infer<typeof VeoSectionProps> = {
  showTitle: true,
};

export type VeoSectionPropsType = z.infer<typeof VeoSectionProps>;
