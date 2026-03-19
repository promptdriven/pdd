import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 32.080;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(0.089),
  VISUAL_01_START: s2f(0.089),
  VISUAL_01_END: s2f(0.201),
  VISUAL_02_START: s2f(0.201),
  VISUAL_02_END: s2f(0.380),
  VISUAL_03_START: s2f(0.380),
  VISUAL_03_END: s2f(0.513),
  VISUAL_04_START: s2f(0.513),
  VISUAL_04_END: s2f(0.647),
  VISUAL_05_START: s2f(0.647),
  VISUAL_05_END: s2f(31.968),
  VISUAL_06_START: s2f(31.968),
  VISUAL_06_END: s2f(32.080),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_section_title_card", desc: "Section 6.1: Where to Start — Section Title Card" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_legacy_codebase_reveal", desc: "Section 6.2: Legacy Codebase Reveal — The Brownfield Reality" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_module_highlight_update", desc: "Section 6.3: Module Highlight & Update — Extracting a Prompt from Existing Code" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_source_of_truth_shift", desc: "Section 6.4: Source of Truth Shift — Code Grays, Prompt Glows" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_regenerate_compare_loop", desc: "Section 6.5: Regenerate & Compare Loop — Validating the Migration" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_spreading_glow_migration", desc: "Section 6.6: Spreading Glow Migration — Modules Converting One by One" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_no_big_bang_callout", desc: "Section 6.7: No Big Bang Callout — Gradual Migration Takeaway" },
];

export const WhereToStartSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultWhereToStartSectionProps: z.infer<typeof WhereToStartSectionProps> = {
  showTitle: true,
};

export type WhereToStartSectionPropsType = z.infer<typeof WhereToStartSectionProps>;
