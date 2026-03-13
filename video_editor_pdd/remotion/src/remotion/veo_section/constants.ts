import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 7.552;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(0.731),
  VISUAL_01_START: s2f(0.731),
  VISUAL_01_END: s2f(1.705),
  VISUAL_02_START: s2f(1.705),
  VISUAL_02_END: s2f(2.680),
  VISUAL_03_START: s2f(2.680),
  VISUAL_03_END: s2f(3.654),
  VISUAL_04_START: s2f(3.654),
  VISUAL_04_END: s2f(4.629),
  VISUAL_05_START: s2f(4.629),
  VISUAL_05_END: s2f(5.847),
  VISUAL_06_START: s2f(5.847),
  VISUAL_06_END: s2f(6.821),
  VISUAL_07_START: s2f(6.821),
  VISUAL_07_END: s2f(7.552),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo_section_01_title_card", desc: "Section 2.1: Veo Section Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_ocean_wave_broll", desc: "Section 2.2: Ocean Wave B-Roll" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_wave_data_overlay", desc: "Section 2.3: Wave Data Overlay" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_aerial_forest_broll", desc: "Section 2.4: Aerial Forest B-Roll" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_split_nature_comparison", desc: "Section 2.5: Split Nature Comparison" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_veo_pipeline_infographic", desc: "Section 2.6: Veo Generation Pipeline Infographic" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_narration_overlay_intro", desc: "Section 2.7: Narration Overlay Intro" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_section_end_card", desc: "Section 2.8: Section End Card" },
];

export const VeoSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultVeoSectionProps: z.infer<typeof VeoSectionProps> = {
  showTitle: true,
};

export type VeoSectionPropsType = z.infer<typeof VeoSectionProps>;
