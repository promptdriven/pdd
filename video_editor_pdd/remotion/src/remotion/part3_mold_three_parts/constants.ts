import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 344.160;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(29.420),
  VISUAL_01_START: s2f(29.760),
  VISUAL_01_END: s2f(59.300),
  VISUAL_02_START: s2f(68.820),
  VISUAL_02_END: s2f(96.560),
  VISUAL_03_START: s2f(68.820),
  VISUAL_03_END: s2f(112.180),
  VISUAL_04_START: s2f(144.300),
  VISUAL_04_END: s2f(161.920),
  VISUAL_05_START: s2f(271.980),
  VISUAL_05_END: s2f(298.820),
  VISUAL_06_START: s2f(299.120),
  VISUAL_06_END: s2f(303.620),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "01 section title card", lane: 0 },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_mold_cross_section", desc: "02 mold cross section", lane: 0 },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "04_liquid_hits_wall", desc: "04 liquid hits wall", lane: 0 },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "05_research_annotations", desc: "05 research annotations", lane: 0 },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "09_bug_fork_diagram", desc: "09 bug fork diagram", lane: 0 },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "15_context_window_comparison", desc: "15 context window comparison", lane: 0 },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "16_grounding_material", desc: "16 grounding material", lane: 0 },
];

export const Part3MoldThreePartsSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsSectionProps: z.infer<typeof Part3MoldThreePartsSectionProps> = {
  showTitle: true,
};

export type Part3MoldThreePartsSectionPropsType = z.infer<typeof Part3MoldThreePartsSectionProps>;
