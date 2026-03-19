import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 20.660;
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.000),
  VISUAL_00_END: s2f(2.431),
  VISUAL_01_START: s2f(2.431),
  VISUAL_01_END: s2f(4.254),
  VISUAL_02_START: s2f(4.254),
  VISUAL_02_END: s2f(7.292),
  VISUAL_03_START: s2f(7.292),
  VISUAL_03_END: s2f(10.330),
  VISUAL_04_START: s2f(10.330),
  VISUAL_04_END: s2f(12.761),
  VISUAL_05_START: s2f(12.761),
  VISUAL_05_END: s2f(15.191),
  VISUAL_06_START: s2f(15.191),
  VISUAL_06_END: s2f(16.406),
  VISUAL_07_START: s2f(16.406),
  VISUAL_07_END: s2f(18.229),
  VISUAL_08_START: s2f(18.229),
  VISUAL_08_END: s2f(20.660),
};

export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "01_sock_callback_split", desc: "Section 7.1: Sock Callback — The Final Discard" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "02_sock_discard_veo", desc: "Section 7.2: Sock Discard — The Final Toss" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "03_code_regenerate_workflow", desc: "Section 7.3: Code Regenerate Workflow — Never Opened the File" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "04_pdd_triangle", desc: "Section 7.4: PDD Triangle — The Core Visual Thesis" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "05_dissolve_regenerate_loop", desc: "Section 7.5: Dissolve-Regenerate Loop — Code Is Ephemeral" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "06_mold_glow_finale", desc: "Section 7.6: Mold Glow Finale — The Code Is Just Plastic" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "07_the_beat", desc: "Section 7.7: The Beat — Dramatic Silence" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "08_mold_is_what_matters", desc: "Section 7.8: The Mold Is What Matters — Final Thesis" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "09_final_title_card", desc: "Section 7.9: Final Title Card — Call to Action" },
];

export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
