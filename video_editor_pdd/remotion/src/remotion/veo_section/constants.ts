import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 11.797;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(0.843),
  VISUAL_01_START: s2f(0.843),
  VISUAL_01_END: s2f(1.685),
  VISUAL_02_START: s2f(1.685),
  VISUAL_02_END: s2f(2.528),
  VISUAL_03_START: s2f(2.528),
  VISUAL_03_END: s2f(3.371),
  VISUAL_04_START: s2f(3.371),
  VISUAL_04_END: s2f(4.213),
  VISUAL_05_START: s2f(4.213),
  VISUAL_05_END: s2f(5.056),
  VISUAL_06_START: s2f(5.056),
  VISUAL_06_END: s2f(5.899),
  VISUAL_07_START: s2f(5.899),
  VISUAL_07_END: s2f(6.741),
  VISUAL_08_START: s2f(6.741),
  VISUAL_08_END: s2f(7.584),
  VISUAL_09_START: s2f(7.584),
  VISUAL_09_END: s2f(8.427),
  VISUAL_10_START: s2f(8.427),
  VISUAL_10_END: s2f(9.269),
  VISUAL_11_START: s2f(9.269),
  VISUAL_11_END: s2f(10.112),
  VISUAL_12_START: s2f(10.112),
  VISUAL_12_END: s2f(10.955),
  VISUAL_13_START: s2f(10.955),
  VISUAL_13_END: s2f(11.797),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo_section_01_title_card", desc: "Section 2.1: Veo Section Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_ocean_wave_sunset", desc: "Section 2.2: Ocean Wave Sunset" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_narration_overlay_intro", desc: "Section 2.3: Narration Overlay — Intro" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_forest_canopy_aerial", desc: "Section 2.4: Forest Canopy Aerial" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_narration_overlay_forest", desc: "Section 2.5: Narration Overlay — Forest" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_veo_badge_callout", desc: "Section 2.6: Veo Badge Callout" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_split_ocean_forest", desc: "Section 2.7: Split Screen — Ocean & Forest" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_veo_technology_callout", desc: "Section 2.8: Veo Technology Callout" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_waveform_visualizer", desc: "Section 2.9: Waveform Visualizer" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "10_split_comparison", desc: "Section 2.10: Split Comparison — Prompt vs. Output" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "11_veo_badge_reprise", desc: "Section 2.11: Veo Badge Reprise" },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "12_split_ocean_forest_reprise", desc: "Section 2.12: Split Screen — Ocean & Forest Reprise" },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "13_veo_technology_reprise", desc: "Section 2.13: Veo Technology Reprise" },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "14_section_outro", desc: "Section 2.14: Section Outro" },
];

export const VeoSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultVeoSectionProps: z.infer<typeof VeoSectionProps> = {
  showTitle: true,
};

export type VeoSectionPropsType = z.infer<typeof VeoSectionProps>;
