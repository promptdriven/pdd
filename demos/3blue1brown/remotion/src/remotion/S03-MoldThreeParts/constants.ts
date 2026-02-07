import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 3: Mold Has Three Parts
// Audio: part3_mold_narration.wav (292.1s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "Now let's get precise, because prompt is the mold is a ..."
//     6.8s [ 1] "In PDD, the mold has three components, three types of c..."
//    13.4s [ 2] "First, tests. Tests are the walls of your mold."
//    18.4s [ 3] "Each test is a constraint, a boundary the generated cod..."
//    23.6s [ 4] "And these walls matter more than you'd think."
//    27.6s [ 5] "CodeRabbit analyzed hundreds of pull requests and found..."
//    35.3s [ 6] "than human code, 75% more logic errors, 8 times more pe..."
//    44.7s [ 7] "it. AI without strong tests increases instability. AI w..."
//    53.6s [ 8] "The walls aren't optional. They're what make regenerati..."
//    60.2s [ 9] "It sees these tests. The code it produces must pass the..."
//    67.0s [10] "violates these walls. Now here's where it gets interest..."
//    83.6s [11] "not in this generation, not in any future generation. T..."
//    92.4s [12] "accumulate. The mold only gets more precise. Each wall ..."
//   100.1s [13] "In traditional development, a bug fix helps one place. ..."
//   108.0s [14] "forever. Now here's something most people don't know. I..."
//   117.6s [15] "SAT and SMT solvers to mathematically prove equivalence..."
//   128.0s [16] "to formally verify properties of generated code, not sa..."
//   134.5s [17] "mathematical proof that a property holds for every poss..."
//   140.2s [18] "When Z3 proves that a function never returns null for a..."
//   146.0s [19] "it hasn't tried every input. It's reason symbolically o..."
//   152.8s [20] "the same certainty. The same category of guarantee the ..."
//   159.1s [21] "dollar tape-outs. Traditional unit tests are still samp..."
//   165.7s [22] "but Z3 gives you walls that are proven, not just tested..."
//   171.4s [23] "analogy isn't a metaphor. It's the same technology. Sec..."
//   180.6s [24] "want. The prompt doesn't define the walls. Tests do tha..."
//   187.8s [25] "and why. And here's something subtle. The exact impleme..."
//   195.5s [26] "behavior. The code is flexible. The contract is fixed. ..."
//   203.5s [27] "of the code it generates. You're specifying what and wh..."
//   211.7s [28] "Remember the context window problem? Code is token expe..."
//   218.7s [29] "and these models were trained on up to 30 times more na..."
//   224.5s [30] "found that just adding natural language comments to cod..."
//   229.8s [31] "quality by 41%. The prompt isn't fighting the model's s..."
//   237.4s [32] "And unlike agentic tools that dynamically guess which c..."
//   242.8s [33] "and increasingly guess wrong, each prompt declares its ..."
//   250.1s [34] "not machine-assemble. Third, grounding. This determines..."
//   259.2s [35] "Grounding is learned from your past generations. When y..."
//   264.6s [36] "that knowledge feeds back into the system. Your style, ..."
//   271.9s [37] "grounding captures all of it, and applies it automatica..."
//   278.5s [38] "Cramped plus tests plus grounding. Intent plus constrai..."
//   286.3s [39] "complete specification. The code is output, the mold is..."

export const PART3_FPS = 30;
export const PART3_DURATION_SECONDS = 295;
export const PART3_DURATION_FRAMES = PART3_FPS * PART3_DURATION_SECONDS;
export const PART3_WIDTH = 1920;
export const PART3_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART3_FPS);

export const BEATS = {
  // Visual 0: CrossSectionIntro — "Now let's get precise, because prompt is the mold ..."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(12.26),  // 368 frames

  // Visual 1: WallsIlluminate — "First, tests. Tests are the walls of your mold...."
  VISUAL_01_START: s2f(13.44),  // 403 frames
  VISUAL_01_END: s2f(23.6),  // 708 frames

  // Visual 2: LiquidInjection — "And these walls matter more than you'd think...."
  VISUAL_02_START: s2f(23.6),  // 708 frames
  VISUAL_02_END: s2f(52.12),  // 1564 frames

  // Visual 3: FocusSingleWall — "The walls aren't optional. They're what make regen..."
  VISUAL_03_START: s2f(53.6),  // 1608 frames
  VISUAL_03_END: s2f(66.98),  // 2009 frames

  // Visual 4: BugDiscovered — "violates these walls. Now here's where it gets int..."
  VISUAL_04_START: s2f(66.98),  // 2009 frames
  VISUAL_04_END: s2f(83.58),  // 2507 frames

  // Visual 5: AddTestWall — "not in this generation, not in any future generati..."
  VISUAL_05_START: s2f(83.58),  // 2507 frames
  VISUAL_05_END: s2f(98.64),  // 2959 frames

  // Visual 6: RatchetTimelapse — "In traditional development, a bug fix helps one pl..."
  VISUAL_06_START: s2f(100.06),  // 3002 frames
  VISUAL_06_END: s2f(107.38),  // 3221 frames

  // Visual 7: TraditionalVsPdd — "forever. Now here's something most people don't kn..."
  VISUAL_07_START: s2f(108.02),  // 3241 frames
  VISUAL_07_END: s2f(117.6),  // 3528 frames

  // Visual 8: TraditionalVsPdd — "SAT and SMT solvers to mathematically prove equiva..."
  VISUAL_08_START: s2f(117.6),  // 3528 frames
  VISUAL_08_END: s2f(138.78),  // 4163 frames

  // Visual 9: TraditionalVsPdd — "When Z3 proves that a function never returns null ..."
  VISUAL_09_START: s2f(140.2),  // 4206 frames
  VISUAL_09_END: s2f(171.44),  // 5143 frames

  // Visual 10: InjectionNozzle — "analogy isn't a metaphor. It's the same technology..."
  VISUAL_10_START: s2f(171.44),  // 5143 frames
  VISUAL_10_END: s2f(187.78),  // 5633 frames

  // Visual 11: PromptTextFlows — "and why. And here's something subtle. The exact im..."
  VISUAL_11_START: s2f(187.78),  // 5633 frames
  VISUAL_11_END: s2f(195.5),  // 5865 frames

  // Visual 12: PromptVariations — "behavior. The code is flexible. The contract is fi..."
  VISUAL_12_START: s2f(195.5),  // 5865 frames
  VISUAL_12_END: s2f(203.48),  // 6104 frames

  // Visual 13: PromptGovernsCode — "of the code it generates. You're specifying what a..."
  VISUAL_13_START: s2f(203.48),  // 6104 frames
  VISUAL_13_END: s2f(210.4),  // 6312 frames

  // Visual 14: PromptGovernsCode — "Remember the context window problem? Code is token..."
  VISUAL_14_START: s2f(211.72),  // 6352 frames
  VISUAL_14_END: s2f(249.7),  // 7491 frames

  // Visual 15: GroundingPanel — "not machine-assemble. Third, grounding. This deter..."
  VISUAL_15_START: s2f(250.08),  // 7502 frames
  VISUAL_15_END: s2f(258.04),  // 7741 frames

  // Visual 16: GroundingComparison — "Grounding is learned from your past generations. W..."
  VISUAL_16_START: s2f(259.24),  // 7777 frames
  VISUAL_16_END: s2f(264.6),  // 7938 frames

  // Visual 17: GroundingDatabase — "that knowledge feeds back into the system. Your st..."
  VISUAL_17_START: s2f(264.6),  // 7938 frames
  VISUAL_17_END: s2f(276.48),  // 8294 frames

  // Visual 18: ThreeComponents — "Cramped plus tests plus grounding. Intent plus con..."
  VISUAL_18_START: s2f(278.46),  // 8354 frames
  VISUAL_18_END: s2f(286.34),  // 8590 frames

  // Visual 19: CodeOutputMoldGlows — "complete specification. The code is output, the mo..."
  VISUAL_19_START: s2f(286.34),  // 8590 frames
  VISUAL_19_END: s2f(291.86),  // 8756 frames
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "CrossSectionIntro", desc: "Get precise, mold has three components, three capitals" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "WallsIlluminate", desc: "First tests, tests are walls, constraint, boundary" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "LiquidInjection", desc: "Walls matter, CodeRabbit 1.7x issues, DORA confirms" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "FocusSingleWall", desc: "Walls not optional, model sees tests, cannot violate" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "BugDiscovered", desc: "Bug found, you don't patch the code" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "AddTestWall", desc: "Add a wall, permanent, bug can never occur again" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "RatchetTimelapse", desc: "Ratchet effect, tests only accumulate, mold more precise" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "TraditionalVsPdd", desc: "Traditional fix one place, PDD prevents bug everywhere" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "TraditionalVsPdd", desc: "Synopsys uses SAT/SMT, PDD uses Z3, same class solver" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "TraditionalVsPdd", desc: "Z3 proves for all inputs, symbolic reasoning, same math" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "InjectionNozzle", desc: "Second the prompt, specification of what you want" },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "PromptTextFlows", desc: "Prompt defines what and why, implementation can vary" },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "PromptVariations", desc: "Behavior locked, code flexible, contract fixed" },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "PromptGovernsCode", desc: "Good prompt 1/5 to 1/10 size, what and why not how" },
  { start: BEATS.VISUAL_14_START, end: BEATS.VISUAL_14_END, id: "PromptGovernsCode", desc: "Context window: prompts are NL, 30x more training data" },
  { start: BEATS.VISUAL_15_START, end: BEATS.VISUAL_15_END, id: "GroundingPanel", desc: "Third grounding, determines properties of what fills mold" },
  { start: BEATS.VISUAL_16_START, end: BEATS.VISUAL_16_END, id: "GroundingComparison", desc: "Grounding learned from past generations" },
  { start: BEATS.VISUAL_17_START, end: BEATS.VISUAL_17_END, id: "GroundingDatabase", desc: "Style patterns conventions, feeds back into system" },
  { start: BEATS.VISUAL_18_START, end: BEATS.VISUAL_18_END, id: "ThreeComponents", desc: "Prompt+tests+grounding, complete specification" },
  { start: BEATS.VISUAL_19_START, end: BEATS.VISUAL_19_END, id: "CodeOutputMoldGlows", desc: "Code is output, mold is what matters" },
];

// Props schema
export const Part3MoldThreePartsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsProps: z.infer<typeof Part3MoldThreePartsProps> = {
  showTitle: true,
};

export type Part3MoldThreePartsPropsType = z.infer<typeof Part3MoldThreePartsProps>;
