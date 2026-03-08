import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 42;
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
  VISUAL_07_START: s2f(21.0),
  VISUAL_07_END: s2f(24.0),
  VISUAL_08_START: s2f(24.0),
  VISUAL_08_END: s2f(27.0),
  VISUAL_09_START: s2f(27.0),
  VISUAL_09_END: s2f(30.0),
  VISUAL_10_START: s2f(30.0),
  VISUAL_10_END: s2f(33.0),
  VISUAL_11_START: s2f(33.0),
  VISUAL_11_END: s2f(36.0),
  VISUAL_12_START: s2f(36.0),
  VISUAL_12_END: s2f(39.0),
  VISUAL_13_START: s2f(39.0),
  VISUAL_13_END: s2f(42.0),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo_section_01_title_card", desc: "Title card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "03_narration_overlay_intro", desc: "Narration overlay intro" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "05_narration_overlay_forest", desc: "Narration overlay forest" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "05_veo_badge_callout", desc: "Veo badge callout" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "06_split_ocean_forest", desc: "Split ocean forest" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_veo_badge_callout", desc: "Veo badge callout" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "06_veo_technology_callout", desc: "Veo technology callout" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "07_split_comparison", desc: "Split comparison" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "07_veo_badge_callout", desc: "Veo badge callout" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "07_waveform_visualizer", desc: "Waveform visualizer" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "08_section_end_card", desc: "Section end card" },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "08_split_ocean_forest", desc: "Split ocean forest" },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "08_veo_technology_callout", desc: "Veo technology callout" },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "09_section_outro", desc: "Section outro" },
];

export const VeoSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultVeoSectionProps: z.infer<typeof VeoSectionProps> = {
  showTitle: true,
};

export type VeoSectionPropsType = z.infer<typeof VeoSectionProps>;
