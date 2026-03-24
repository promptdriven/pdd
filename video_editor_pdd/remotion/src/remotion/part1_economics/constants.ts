import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 455.440;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(4.300),
  VISUAL_01_START: s2f(97.460),
  VISUAL_01_END: s2f(158.500),
  VISUAL_02_START: s2f(158.500),
  VISUAL_02_END: s2f(212.320),
  VISUAL_03_START: s2f(212.320),
  VISUAL_03_END: s2f(255.580),
  VISUAL_04_START: s2f(255.580),
  VISUAL_04_END: s2f(277.360),
  VISUAL_05_START: s2f(331.980),
  VISUAL_05_END: s2f(387.960),
  VISUAL_06_START: s2f(441.120),
  VISUAL_06_END: s2f(455.440),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "04_research_annotations", desc: "04 research annotations", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "05_context_window_shrink", desc: "05 context window shrink", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "06_performance_vs_context", desc: "06 performance vs context", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "07_two_by_two_grid", desc: "07 two by two grid", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "09_patching_vs_regeneration_split", desc: "09 patching vs regeneration split", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "12_developer_darning_split", desc: "12 developer darning split", lane: 0 },
];

export const Part1EconomicsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsSectionProps: z.infer<typeof Part1EconomicsSectionProps> = {
  showTitle: true,
};

export type Part1EconomicsSectionPropsType = z.infer<typeof Part1EconomicsSectionProps>;
