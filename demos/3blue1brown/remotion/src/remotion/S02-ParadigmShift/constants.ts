import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 2: Paradigm Shift
// Audio: part2_paradigm_shift_narration.wav (66.9s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "So, what actually changed with clothes?"
//     2.9s [ 1] "It wasn't just that fabric got cheaper."
//     6.8s [ 2] "It was a paradigm shift in manufacturing"
//     9.8s [ 3] "from crafting individual objects to designing molds."
//    14.6s [ 4] "Make the mold once, produce unlimited identical parts,"
//    18.7s [ 5] "refine the mold once, every future part improves automa..."
//    23.9s [ 6] "And when there's a defect, you don't patch individual p..."
//    28.8s [ 7] "You fix the mold, and that fix applies to every part yo..."
//    34.8s [ 8] "This is the real shift, not cheaper material,"
//    38.9s [ 9] "a migration of where value lives."
//    41.1s [10] "In crafting, value lives in the object."
//    44.7s [11] "You protect the object, losing the chair is losing ever..."
//    49.9s [12] "In molding, value lives in the specification."
//    53.4s [13] "The mold, the plastic part,"
//    55.9s [14] "disposable, regenerated at will."
//    59.6s [15] "This is prompt-driven development."
//    62.9s [16] "The prompt is your mold, the code is just plastic."

export const PART2_FPS = 30;
export const PART2_DURATION_SECONDS = 69;
export const PART2_DURATION_FRAMES = PART2_FPS * PART2_DURATION_SECONDS;
export const PART2_WIDTH = 1920;
export const PART2_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART2_FPS);

export const BEATS = {
  // Visual 0: veo:01_factory_floor — "So, what actually changed with clothes?..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(4.76),  // 143 frames

  // Visual 1: veo:02_mold_closeup — "It was a paradigm shift in manufacturing..."
  VISUAL_01_START: s2f(6.8),  // 204 frames
  VISUAL_01_END: s2f(13.34),  // 400 frames

  // Visual 2: PartsEject — "Make the mold once, produce unlimited identical pa..."
  VISUAL_02_START: s2f(14.64),  // 439 frames
  VISUAL_02_END: s2f(22.56),  // 677 frames

  // Visual 3: DefectDiscovered — "And when there's a defect, you don't patch individ..."
  VISUAL_03_START: s2f(23.94),  // 718 frames
  VISUAL_03_END: s2f(28.28),  // 848 frames

  // Visual 4: PerfectParts — "You fix the mold, and that fix applies to every pa..."
  VISUAL_04_START: s2f(28.84),  // 865 frames
  VISUAL_04_END: s2f(33.32),  // 1000 frames

  // Visual 5: ValueAura — "This is the real shift, not cheaper material,..."
  VISUAL_05_START: s2f(34.78),  // 1043 frames
  VISUAL_05_END: s2f(40.84),  // 1225 frames

  // Visual 6: veo:07_craftsman_vs_mold — "In crafting, value lives in the object...."
  VISUAL_06_START: s2f(41.14),  // 1234 frames
  VISUAL_06_END: s2f(48.3),  // 1449 frames

  // Visual 7: PlasticRegenerates — "In molding, value lives in the specification...."
  VISUAL_07_START: s2f(49.88),  // 1496 frames
  VISUAL_07_END: s2f(58.26),  // 1748 frames

  // Visual 8: MoldToPrompt — "This is prompt-driven development...."
  VISUAL_08_START: s2f(59.6),  // 1788 frames
  VISUAL_08_END: s2f(66.68),  // 2000 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:01_factory_floor", desc: "What changed with clothes, paradigm shift" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "veo:02_mold_closeup", desc: "Manufacturing: crafting to designing molds" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "PartsEject", desc: "Make mold once, unlimited identical parts" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "DefectDiscovered", desc: "Defect: don't patch parts" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "PerfectParts", desc: "Fix the mold, applies to every future part" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "ValueAura", desc: "Real shift: migration of where value lives" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "veo:07_craftsman_vs_mold", desc: "Crafting: value in object, protect it" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "PlasticRegenerates", desc: "Molding: value in specification, disposable" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "MoldToPrompt", desc: "This is PDD: prompt is mold, code is plastic" },
];

// Props schema
export const Part2ParadigmShiftProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftProps: z.infer<typeof Part2ParadigmShiftProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftPropsType = z.infer<typeof Part2ParadigmShiftProps>;
