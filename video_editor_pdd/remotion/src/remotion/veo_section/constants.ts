import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 7.829;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(1.710),
  VISUAL_01_START: s2f(1.710),
  VISUAL_01_END: s2f(3.420),
  VISUAL_02_START: s2f(3.420),
  VISUAL_02_END: s2f(3.453),
  VISUAL_03_START: s2f(3.453),
  VISUAL_03_END: s2f(3.486),
  VISUAL_04_START: s2f(3.486),
  VISUAL_04_END: s2f(5.196),
  VISUAL_05_START: s2f(5.196),
  VISUAL_05_END: s2f(6.906),
  VISUAL_06_START: s2f(6.906),
  VISUAL_06_END: s2f(7.389),
  VISUAL_07_START: s2f(7.389),
  VISUAL_07_END: s2f(7.829),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo_section_01_title_card", desc: "Veo Section 01 Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "04_wave_data_overlay", desc: "Wave Data Overlay" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "05_split_nature_comparison", desc: "Split Nature Comparison" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "06_veo_pipeline_infographic", desc: "Veo Pipeline Infographic" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "07_narration_overlay_intro", desc: "Narration Overlay Intro" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "08_section_end_card", desc: "Section End Card" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "veo_section_02_key_visual", desc: "Veo Section 02 Key Visual" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "veo_section_03_split_summary", desc: "Veo Section 03 Split Summary" },
];

export const VeoSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultVeoSectionProps: z.infer<typeof VeoSectionProps> = {
  showTitle: true,
};

export type VeoSectionPropsType = z.infer<typeof VeoSectionProps>;
