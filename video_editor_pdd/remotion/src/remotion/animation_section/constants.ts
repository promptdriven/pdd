import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 51;
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
  VISUAL_14_START: s2f(42.0),
  VISUAL_14_END: s2f(45.0),
  VISUAL_15_START: s2f(45.0),
  VISUAL_15_END: s2f(48.0),
  VISUAL_16_START: s2f(48.0),
  VISUAL_16_END: s2f(51.0),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "animation_section_01_title_card", desc: "Title card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_bar_chart_key_visual", desc: "Bar chart key visual" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "02_intro_data_pulse", desc: "Intro data pulse" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "03_blue_circle_pulse", desc: "Blue circle pulse" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "03_key_visual_bar_chart", desc: "Key visual bar chart" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "03_particle_transition", desc: "Particle transition" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "04_circle_to_square_transform", desc: "Circle to square transform" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "04_remotion_logo_reveal", desc: "Remotion logo reveal" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "05_animation_engine_diagram", desc: "Animation engine diagram" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "05_animation_showcase", desc: "Animation showcase" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "05_bar_chart_key_visual", desc: "Bar chart key visual" },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "06_framework_comparison", desc: "Framework comparison" },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "06_split_before_after", desc: "Split before after" },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "06_split_summary", desc: "Split summary" },
  { start: BEATS.VISUAL_14_START, end: BEATS.VISUAL_14_END, id: "07_before_after_split_summary", desc: "Before after split summary" },
  { start: BEATS.VISUAL_15_START, end: BEATS.VISUAL_15_END, id: "08_closing_badge", desc: "Closing badge" },
  { start: BEATS.VISUAL_16_START, end: BEATS.VISUAL_16_END, id: "08_section_closing_card", desc: "Section closing card" },
];

export const AnimationSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAnimationSectionProps: z.infer<typeof AnimationSectionProps> = {
  showTitle: true,
};

export type AnimationSectionPropsType = z.infer<typeof AnimationSectionProps>;
