import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 11.242667;
export const SECTION_DURATION_FRAMES = 338;

export const BEATS = {
  VISUAL_00_START: 0,
  VISUAL_00_END: 112,
  VISUAL_01_START: 112,
  VISUAL_01_END: 224,
  VISUAL_02_START: 224,
  VISUAL_02_END: 338,
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo_section_01_title_card", desc: "Veo Section 01 Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "veo_section_02_key_visual", desc: "Veo Section 02 Key Visual" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "veo_section_03_split_summary", desc: "Veo Section 03 Split Summary" },
];

export const VeoSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultVeoSectionProps: z.infer<typeof VeoSectionProps> = {
  showTitle: true,
};

export type VeoSectionPropsType = z.infer<typeof VeoSectionProps>;
