import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 2: Paradigm Shift
// Audio: part2_paradigm_shift_narration.wav (112.2s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "In crafting, value lives in the object, you protect the..."
//     8.8s [ 1] "In molding, value lives in the specification, the mold,..."
//    18.5s [ 2] "This is prompt-driven development. The prompt is your m..."
//    26.9s [ 3] "No one nay, ninety-sil, hum, no one nay, no one nay, th..."
//    35.4s [ 4] "Now, let's get precise, because prompt is the mold is a..."
//    43.3s [ 5] "In PDD, the mold has three components, three types of c..."
//    50.6s [ 6] "First tests, tests are the walls of your mold."
//    54.8s [ 7] "Each test is a constraint, a boundary the generated cod..."
//    60.8s [ 8] "When the model generates code, it sees these tests, the..."
//    67.6s [ 9] "it literally cannot generate code that violates these w..."
//    72.1s [10] "Now, here's where it gets interesting, when you find a ..."
//    77.0s [11] "you don't patch the code, you add a wall."
//    81.5s [12] "That wall is permanent, that bug can never occur again,..."
//    92.5s [13] "This is the ratchet effect, tests only accumulate, the ..."
//    99.1s [14] "each wall you add constrains all future generations."
//   104.2s [15] "In traditional development, a bug fix helps one place."
//   107.5s [16] "In PDD, a test prevents that bug everywhere, forever."

export const PART2_FPS = 30;
export const PART2_DURATION_SECONDS = 115;
export const PART2_DURATION_FRAMES = PART2_FPS * PART2_DURATION_SECONDS;
export const PART2_WIDTH = 1920;
export const PART2_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART2_FPS);

export const BEATS = {
  // Visual 0: veo:01_factory_floor — "In crafting, value lives in the object, you protec..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(17.18),  // 515 frames

  // Visual 1: MoldToPrompt — "This is prompt-driven development. The prompt is y..."
  VISUAL_01_START: s2f(18.46),  // 554 frames
  VISUAL_01_END: s2f(25.68),  // 770 frames

  // Visual 2: PromptGeneratesCode — "No one nay, ninety-sil, hum, no one nay, no one na..."
  VISUAL_02_START: s2f(26.88),  // 806 frames
  VISUAL_02_END: s2f(49.22),  // 1477 frames

  // Visual 3: CrossSectionIntro — "First tests, tests are the walls of your mold...."
  VISUAL_03_START: s2f(50.56),  // 1517 frames
  VISUAL_03_END: s2f(70.7),  // 2121 frames

  // Visual 4: AddTestWall — "Now, here's where it gets interesting, when you fi..."
  VISUAL_04_START: s2f(72.06),  // 2162 frames
  VISUAL_04_END: s2f(90.8),  // 2724 frames

  // Visual 5: RatchetTimelapse — "This is the ratchet effect, tests only accumulate,..."
  VISUAL_05_START: s2f(92.5),  // 2775 frames
  VISUAL_05_END: s2f(101.98),  // 3059 frames

  // Visual 6: TraditionalVsPdd — "In traditional development, a bug fix helps one pl..."
  VISUAL_06_START: s2f(104.2),  // 3126 frames
  VISUAL_06_END: s2f(111.94),  // 3358 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "veo:01_factory_floor", desc: "Crafting vs molding: value in object vs specification" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "MoldToPrompt", desc: "PDD: prompt is your mold, code is plastic" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "PromptGeneratesCode", desc: "Three components intro: precise → mold has three parts" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "CrossSectionIntro", desc: "Test capital: tests are walls → constraint → sees tests → ca" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "AddTestWall", desc: "Bug found: don't patch → add wall → permanent" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "RatchetTimelapse", desc: "Ratchet effect: tests accumulate → constrains all future" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "TraditionalVsPdd", desc: "Traditional vs PDD: bug fix one place vs everywhere forever" },
];

// Props schema
export const Part2ParadigmShiftProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftProps: z.infer<typeof Part2ParadigmShiftProps> = {
  showTitle: true,
};

export type Part2ParadigmShiftPropsType = z.infer<typeof Part2ParadigmShiftProps>;
