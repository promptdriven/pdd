import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 3: Mold Has Three Parts
// Audio: part3_mold_narration.wav (145.9s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Now, let's get precise, because prompt is the mold as a..."
//     7.6s [ 1] "In PDD, the mold has three components, three types of c..."
//    15.2s [ 2] "First, tests. Tests are the walls of your mold."
//    19.6s [ 3] "Each test is a constraint. A boundary the generated cod..."
//    25.1s [ 4] "When the model generates code, it sees these tests. The..."
//    32.0s [ 5] "It literally cannot generate code that violates these w..."
//    36.4s [ 6] "Now, here's where it gets interesting. When you find a ..."
//    43.7s [ 7] "You add a wall. That wall is permanent. That bug can ne..."
//    53.2s [ 8] "Not in any future generation."
//    56.9s [ 9] "This is the ratchet effect. Tests only accumulate. The ..."
//    63.5s [10] "Each wall you add constrains all future generations."
//    68.1s [11] "In traditional development, a bug fix helps one place. ..."
//    75.7s [12] "forever. Second, the prompt. Your specification of what..."
//    81.1s [13] "The prompt doesn't define the walls. Tests do that. The..."
//    89.6s [14] "And here's something subtle. The exact implementation c..."
//    97.2s [15] "The code is flexible. The contract is fixed. A good pro..."
//   104.0s [16] "You're specifying what and why, not how. Third, groundi..."
//   112.4s [17] "what fills the mold. Grounding is learned from your pas..."
//   118.7s [18] "generate and fix code, that knowledge feeds back into t..."
//   125.7s [19] "your team's conventions. Grounding captures all of it a..."
//   131.5s [20] "generations. Prompt plus tests plus grounding. Intent p..."
//   139.6s [21] "they form a complete specification. The code is output...."

export const PART3_FPS = 30;
export const PART3_DURATION_SECONDS = 148;
export const PART3_DURATION_FRAMES = PART3_FPS * PART3_DURATION_SECONDS;
export const PART3_WIDTH = 1920;
export const PART3_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART3_FPS);

export const BEATS = {
  // Visual 0: CrossSectionIntro — "Now, let's get precise, because prompt is the mold..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(13.58),  // 407 frames

  // Visual 1: WallsIlluminate — "First, tests. Tests are the walls of your mold...."
  VISUAL_01_START: s2f(15.18),  // 455 frames
  VISUAL_01_END: s2f(23.46),  // 704 frames

  // Visual 2: LiquidInjection — "When the model generates code, it sees these tests..."
  VISUAL_02_START: s2f(25.14),  // 754 frames
  VISUAL_02_END: s2f(35.08),  // 1052 frames

  // Visual 3: AddTestWall — "Now, here's where it gets interesting. When you fi..."
  VISUAL_03_START: s2f(36.4),  // 1092 frames
  VISUAL_03_END: s2f(55.2),  // 1656 frames

  // Visual 4: RatchetTimelapse — "This is the ratchet effect. Tests only accumulate...."
  VISUAL_04_START: s2f(56.94),  // 1708 frames
  VISUAL_04_END: s2f(66.34),  // 1990 frames

  // Visual 5: TraditionalVsPdd — "In traditional development, a bug fix helps one pl..."
  VISUAL_05_START: s2f(68.1),  // 2043 frames
  VISUAL_05_END: s2f(75.7),  // 2271 frames

  // Visual 6: PromptTextFlows — "forever. Second, the prompt. Your specification of..."
  VISUAL_06_START: s2f(75.7),  // 2271 frames
  VISUAL_06_END: s2f(87.38),  // 2621 frames

  // Visual 7: PromptVariations — "And here's something subtle. The exact implementat..."
  VISUAL_07_START: s2f(89.6),  // 2688 frames
  VISUAL_07_END: s2f(96.4),  // 2892 frames

  // Visual 8: PromptGovernsCode — "The code is flexible. The contract is fixed. A goo..."
  VISUAL_08_START: s2f(97.22),  // 2917 frames
  VISUAL_08_END: s2f(104.0),  // 3120 frames

  // Visual 9: GroundingPanel — "You're specifying what and why, not how. Third, gr..."
  VISUAL_09_START: s2f(104.0),  // 3120 frames
  VISUAL_09_END: s2f(131.52),  // 3946 frames

  // Visual 10: ThreeComponents — "generations. Prompt plus tests plus grounding. Int..."
  VISUAL_10_START: s2f(131.52),  // 3946 frames
  VISUAL_10_END: s2f(139.24),  // 4177 frames

  // Visual 11: CodeOutputMoldGlows — "they form a complete specification. The code is ou..."
  VISUAL_11_START: s2f(139.6),  // 4188 frames
  VISUAL_11_END: s2f(145.74),  // 4372 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "CrossSectionIntro", desc: "Intro: three components, three types of capital" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "WallsIlluminate", desc: "Tests are walls, constraint, boundary" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "LiquidInjection", desc: "Model sees tests, cannot violate walls" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "AddTestWall", desc: "Bug: add wall, permanent, never again" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "RatchetTimelapse", desc: "Ratchet effect: tests accumulate" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "TraditionalVsPdd", desc: "Traditional vs PDD comparison" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "PromptTextFlows", desc: "Second: prompt, specification of what you want" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "PromptVariations", desc: "Implementation varies, behavior locked" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "PromptGovernsCode", desc: "Good prompt smaller than code" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "GroundingPanel", desc: "Third: grounding, style, patterns, conventions" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "ThreeComponents", desc: "Prompt+tests+grounding, complete specification" },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "CodeOutputMoldGlows", desc: "Code is output, mold is what matters" },
];

// Props schema
export const Part3MoldThreePartsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsProps: z.infer<typeof Part3MoldThreePartsProps> = {
  showTitle: true,
};

export type Part3MoldThreePartsPropsType = z.infer<typeof Part3MoldThreePartsProps>;
