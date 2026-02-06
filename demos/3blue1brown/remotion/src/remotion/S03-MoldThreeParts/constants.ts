import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 3: Mold Has Three Parts
// Audio: part3_mold_narration.wav (175.1s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Second, the prompt, your specification of what you want..."
//     3.1s [ 1] "The prompt doesn't define the walls."
//     5.1s [ 2] "Tests do that."
//     6.7s [ 3] "The prompt defines what you're asking for and why."
//    11.5s [ 4] "And here's something subtle."
//    13.6s [ 5] "The exact implementation can vary."
//    16.9s [ 6] "What's locked is the behavior."
//    19.2s [ 7] "The code is flexible."
//    20.9s [ 8] "The contract is fixed."
//    23.0s [ 9] "A good prompt is much smaller than the code it generate..."
//    25.9s [10] "You're specifying what and why, not how."
//    30.8s [11] "Third, grounding."
//    32.6s [12] "This determines the properties of what fills the mold."
//    36.8s [13] "Grounding is learned from your past generations."
//    39.8s [14] "When you successfully generate and fix code,"
//    42.7s [15] "that knowledge feeds back into the system."
//    45.7s [16] "Your style, your patterns, your team's conventions."
//    49.6s [17] "Grounding captures all of it"
//    51.1s [18] "and applies it automatically to future generations."
//    55.9s [19] "Prompt plus tests plus grounding, intent plus constrain..."
//    60.9s [20] "Together, they form a complete specification."
//    64.7s [21] "The code is output."
//    66.7s [22] "The mold is what matters."
//    69.3s [23] "Now, here's something subtle that changes how you think..."
//    74.8s [24] "In 3D printing, there's no mold."
//    77.6s [25] "The machine must know exactly where to place every sing..."
//    81.5s [26] "The specification must be extremely precise."
//    85.5s [27] "In injection molding, precision comes from the walls."
//    89.5s [28] "The material just flows until it's constrained."
//    93.8s [29] "This maps directly to PDD."
//    98.0s [30] "With few tests, your prompt needs to specify everything..."
//   102.5s [31] "Edge cases, error handling, exact behavior in every sit..."
//   108.5s [32] "With many tests, the prompt only needs to specify inten..."
//   113.0s [33] "The tests handle the constraints."
//   116.2s [34] "This is why test accumulation matters."
//   119.9s [35] "It's not just about catching bugs."
//   122.4s [36] "It's about making prompts simpler and regeneration safe..."
//   127.7s [37] "More tests, less prompt, the walls do the precision wor..."
//   132.9s [38] "Hmm, let's talk about compound returns."
//   137.5s [39] "When you patch code, each fix has local returns."
//   141.5s [40] "You fixed one bug in one place."
//   143.8s [41] "Similar bugs can still occur elsewhere."
//   146.6s [42] "And sometimes your patch introduces new bugs."
//   150.1s [43] "The returns are linear at best."
//   152.9s [44] "Often sub-linear."
//   155.6s [45] "When you add a test in PDD, the returns are different."
//   160.2s [46] "That test you wrote today, it constrains tomorrow's gen..."
//   164.2s [47] "And next weeks, and next years, it's a permanent wall."
//   168.6s [48] "Every investment in the mold has compound returns."
//   172.0s [49] "Every investment in patching has diminishing returns."

export const PART3_FPS = 30;
export const PART3_DURATION_SECONDS = 178;
export const PART3_DURATION_FRAMES = PART3_FPS * PART3_DURATION_SECONDS;
export const PART3_WIDTH = 1920;
export const PART3_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART3_FPS);

export const BEATS = {
  // Visual 0: PromptTextFlows — "Second, the prompt, your specification of what you..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(9.34),  // 280 frames

  // Visual 1: PromptVariations — "And here's something subtle...."
  VISUAL_01_START: s2f(11.46),  // 344 frames
  VISUAL_01_END: s2f(22.08),  // 662 frames

  // Visual 2: PromptGovernsCode — "A good prompt is much smaller than the code it gen..."
  VISUAL_02_START: s2f(22.98),  // 689 frames
  VISUAL_02_END: s2f(29.2),  // 876 frames

  // Visual 3: GroundingPanel — "Third, grounding...."
  VISUAL_03_START: s2f(30.84),  // 925 frames
  VISUAL_03_END: s2f(54.16),  // 1625 frames

  // Visual 4: ThreeComponents — "Prompt plus tests plus grounding, intent plus cons..."
  VISUAL_04_START: s2f(55.94),  // 1678 frames
  VISUAL_04_END: s2f(67.68),  // 2030 frames

  // Visual 5: veo:split_3d_vs_mold — "Now, here's something subtle that changes how you ..."
  VISUAL_05_START: s2f(69.3),  // 2079 frames
  VISUAL_05_END: s2f(91.8),  // 2754 frames

  // Visual 6: PrecisionGraph — "This maps directly to PDD...."
  VISUAL_06_START: s2f(93.82),  // 2815 frames
  VISUAL_06_END: s2f(131.72),  // 3952 frames

  // Visual 7: LongPrompt — "Hmm, let's talk about compound returns...."
  VISUAL_07_START: s2f(132.88),  // 3986 frames
  VISUAL_07_END: s2f(153.96),  // 4619 frames

  // Visual 8: ShortPromptTests — "When you add a test in PDD, the returns are differ..."
  VISUAL_08_START: s2f(155.58),  // 4667 frames
  VISUAL_08_END: s2f(174.74),  // 5242 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "PromptTextFlows", desc: "Prompt capital: specification → doesn't define walls → askin" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "PromptVariations", desc: "Subtle: implementation varies → behavior locked → flexible →" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "PromptGovernsCode", desc: "Compression: smaller than code → what and why not how" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "GroundingPanel", desc: "Grounding: properties → learned → style → conventions → auto" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "ThreeComponents", desc: "Integration: prompt+tests+grounding → complete spec → code i" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "veo:split_3d_vs_mold", desc: "Precision tradeoff: 3D printing → no mold → every point → wa" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "PrecisionGraph", desc: "PDD mapping: few tests → specify everything → many tests → i" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "LongPrompt", desc: "Compound returns: patch → local returns → one bug → sub-line" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "ShortPromptTests", desc: "PDD returns: test today → constrains tomorrow → permanent wa" },
];

// Props schema
export const Part3MoldThreePartsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsProps: z.infer<typeof Part3MoldThreePartsProps> = {
  showTitle: true,
};

export type Part3MoldThreePartsPropsType = z.infer<typeof Part3MoldThreePartsProps>;
