import { z } from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: Part 1: Economics of Darning
// Audio: part1_economics_narration.wav (432.9s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
//     0.0s [ 0] "This isn't nostalgia, it's economics."
//     3.5s [ 1] "In 1950, a wool sock cost real money relative to an hou..."
//     8.7s [ 2] "Darning made sense, you'd spend 30 minutes to save a do..."
//    13.4s [ 3] "By the mid-1960s, the math flipped."
//    16.6s [ 4] "A new sock cost less than the time to repair the old on..."
//    20.3s [ 5] "Darning became irrational."
//    23.9s [ 6] "Now look at code."
//    26.6s [ 7] "For decades, generating new code was expensive."
//    30.9s [ 8] "Writing from scratch took hours, days, weeks."
//    34.6s [ 9] "So when something broke, you patched."
//    37.2s [10] "Of course you patched. It was rational."
//    40.8s [11] "Now here's where it gets interesting."
//    43.4s [12] "AI made patching faster too."
//    46.0s [13] "Cursor, Claude, co-pilot."
//    48.6s [14] "They're incredible tools."
//    50.1s [15] "They understand your code base."
//    51.5s [16] "Suggest fixes, catch bugs before you make them."
//    55.7s [17] "Look, each patch is getting faster."
//    58.3s [18] "That's real. That's what you feel when you use these to..."
//    63.0s [19] "But watch the dashed line, the total cost, it's barely ..."
//    67.9s [20] "Because even though each patch is faster,"
//    70.8s [21] "every patch still leaves residue, technical debt."
//    74.0s [22] "That debt accumulates faster now because you're patchin..."
//    79.2s [23] "GitHub measured a 55% speed up on individual coding tas..."
//    84.8s [24] "But that was 95 developers writing one HTTP server from..."
//    90.7s [25] "A Greenfield task."
//    92.3s [26] "Exactly where AI shines."
//    95.6s [27] "When an oval tracked almost 800 developers across real ..."
//   101.4s [28] "no change in throughput."
//   103.0s [29] "41% more bugs."
//   104.6s [30] "The Upsil team themselves expected to see gains."
//   108.6s [31] "Their own product manager said,"
//   110.8s [32] "people are ending up being more reviewers for this code..."
//   114.6s [33] "And you might have some false faith that the code is do..."
//   119.1s [34] "And GitClear confirmed it across 211 million lines of c..."
//   124.0s [35] "Since AI coding assistance arrived,"
//   126.8s [36] "codechern is up 44%."
//   128.8s [37] "New code getting revised within two weeks."
//   131.4s [38] "Meanwhile, refactoring collapsed by 60%."
//   135.7s [39] "Developers aren't cleaning up. They're piling on."
//   140.7s [40] "And there's something else hiding in that debt."
//   144.1s [41] "Something specific to AI assisted development."
//   148.4s [42] "When your code base is small,"
//   150.4s [43] "AI tools are brilliant."
//   152.3s [44] "The context window,"
//   153.7s [45] "what the model can actually see,"
//   156.0s [46] "covers almost everything."
//   157.6s [47] "It understands how the pieces connect."
//   161.4s [48] "But code bases grow. And that window,"
//   164.2s [49] "it stays the same size."
//   166.3s [50] "A typical enterprise code base spans millions of tokens..."
//   170.6s [51] "Even the largest context windows hold a fraction of tha..."
//   175.0s [52] "So now the AI has to guess what's relevant."
//   178.0s [53] "Tools like cursor, use embeddings."
//   181.0s [54] "Cloud code uses agentic search."
//   183.9s [55] "Grip, file by file."
//   185.8s [56] "When Jolt AI benchmarked these tools on real code bases..."
//   191.1s [57] "pure vector search failed to find the right files."
//   195.3s [58] "Agentic search found more."
//   197.6s [59] "But took three to five minutes per query."
//   201.2s [60] "And here's what makes it worse."
//   203.3s [61] "A 2025 EMNLP study proved that even when the model retr..."
//   208.6s [62] "the right information,"
//   210.2s [63] "performance still degrades."
//   212.3s [64] "14 to 85% just from the sheer length of the input."
//   216.9s [65] "It's not about finding the right code."
//   218.7s [66] "The extrotocons themselves hurt the model's ability to ..."
//   223.5s [67] "A separate chroma study across 18 state-of-the-art mode..."
//   228.9s [68] "They call it context rot."
//   232.1s [69] "This is why AI assisted patching is really two stories."
//   238.0s [70] "On a small code base, a few thousand lines patching wit..."
//   245.0s [71] "The context window covers everything."
//   247.2s [72] "That's real."
//   249.8s [73] "But on a large code base, the kind you get after years ..."
//   254.6s [74] "Experience developers are actually 19% slower with AI t..."
//   259.3s [75] "And here's the devastating part."
//   261.2s [76] "Those same developers believed AI was making them 20% f..."
//   266.2s [77] "That's a 39-point gap between what it felt like and wha..."
//   270.9s [78] "The context window can't keep up."
//   273.1s [79] "The model guesses wrong, but it guesses confidently."
//   276.1s [80] "So you don't notice until the bugs hit production."
//   280.2s [81] "And here's the catch."
//   282.0s [82] "Every patch makes the code base bigger."
//   285.1s [83] "So patching pushes you from the world where AI helps in..."
//   292.5s [84] "Regeneration doesn't have this problem."
//   294.9s [85] "A prompt is a fifth to a tenth the size of the coded go..."
//   299.0s [86] "So where raw code overwhelms the context window."
//   302.4s [87] "The prompts for ten modules fit comfortably."
//   305.7s [88] "And the prompt defines its own context."
//   308.8s [89] "The developer declares exactly what the model needs to ..."
//   312.9s [90] "Instead of an agentic tool guessing at what's relevant,..."
//   320.9s [91] "And there's something else."
//   323.4s [92] "These models are trained on up to 30 times more natural..."
//   328.6s [93] "Natural language is their deepest fluency."
//   332.5s [94] "MIT showed that giving models natural language context ..."
//   341.7s [95] "A prompt is natural language."
//   344.1s [96] "You're speaking the model's strongest language and givi..."
//   349.2s [97] "Research also confirms modules around 250 lines have th..."
//   355.8s [98] "A U-shaped curve where two small fragments logic and tw..."
//   362.0s [99] "That's exactly the size of focused prompt produces."
//   366.6s [100] "Meanwhile, generation just crossed below both lines."
//   371.3s [101] "The debt doesn't just slow down."
//   373.8s [102] "It resets."
//   375.2s [103] "Each regeneration starts clean."
//   379.0s [104] "Tools like cursor and clawed code are the best-darning ..."
//   383.5s [105] "I use them. They're fantastic."
//   386.3s [106] "But they're still darning needles and the fundamental p..."
//   392.1s [107] "It's accumulation."
//   394.8s [108] "This is the part of software economics nobody talks abo..."
//   399.0s [109] "80-90% of software cost isn't building the initial syst..."
//   403.4s [110] "It's maintaining it."
//   405.3s [111] "McKinsey found that organizations with high technical d..."
//   410.6s [112] "and deliver features 25-50% slower."
//   414.5s [113] "Stripe measure developers wasting a third of their enti..."
//   421.8s [114] "And those costs compound literally."
//   425.9s [115] "Technical debt follows a compound interest curve."
//   429.3s [116] "Unless you regenerate, then the debt resets."

export const PART1_FPS = 30;
export const PART1_DURATION_SECONDS = 435;
export const PART1_DURATION_FRAMES = PART1_FPS * PART1_DURATION_SECONDS;
export const PART1_WIDTH = 1920;
export const PART1_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * PART1_FPS);

export const BEATS = {
  // Visual 0: SockPriceChart — "This isn't nostalgia, it's economics...."
  VISUAL_00_START: s2f(0.0),  // 0 frames
  VISUAL_00_END: s2f(2.68),  // 80 frames

  // Visual 1: ThresholdHighlight — "In 1950, a wool sock cost real money relative to a..."
  VISUAL_01_START: s2f(3.52),  // 106 frames
  VISUAL_01_END: s2f(12.04),  // 361 frames

  // Visual 2: LinesDiverge — "By the mid-1960s, the math flipped...."
  VISUAL_02_START: s2f(13.42),  // 403 frames
  VISUAL_02_END: s2f(22.16),  // 665 frames

  // Visual 3: CodeCostChart — "Now look at code...."
  VISUAL_03_START: s2f(23.92),  // 718 frames
  VISUAL_03_END: s2f(25.44),  // 763 frames

  // Visual 4: AIMilestones — "For decades, generating new code was expensive...."
  VISUAL_04_START: s2f(26.6),  // 798 frames
  VISUAL_04_END: s2f(39.24),  // 1177 frames

  // Visual 5: CodeCostChart — "Now here's where it gets interesting...."
  VISUAL_05_START: s2f(40.78),  // 1223 frames
  VISUAL_05_END: s2f(54.68),  // 1640 frames

  // Visual 6: CodeCostChartMini — "Look, each patch is getting faster...."
  VISUAL_06_START: s2f(55.7),  // 1671 frames
  VISUAL_06_END: s2f(61.46),  // 1844 frames

  // Visual 7: CrossingPoint — "But watch the dashed line, the total cost, it's ba..."
  VISUAL_07_START: s2f(62.96),  // 1889 frames
  VISUAL_07_END: s2f(78.08),  // 2342 frames

  // Visual 8: CrossingPoint — "GitHub measured a 55% speed up on individual codin..."
  VISUAL_08_START: s2f(79.16),  // 2375 frames
  VISUAL_08_END: s2f(118.08),  // 3542 frames

  // Visual 9: CrossingPoint — "And GitClear confirmed it across 211 million lines..."
  VISUAL_09_START: s2f(119.14),  // 3574 frames
  VISUAL_09_END: s2f(139.1),  // 4173 frames

  // Visual 10: ContextRot — "And there's something else hiding in that debt...."
  VISUAL_10_START: s2f(140.7),  // 4221 frames
  VISUAL_10_END: s2f(146.92),  // 4408 frames

  // Visual 11: ContextRot — "When your code base is small,..."
  VISUAL_11_START: s2f(148.4),  // 4452 frames
  VISUAL_11_END: s2f(159.62),  // 4789 frames

  // Visual 12: ContextRot — "But code bases grow. And that window,..."
  VISUAL_12_START: s2f(161.44),  // 4843 frames
  VISUAL_12_END: s2f(173.6),  // 5208 frames

  // Visual 13: ContextRot — "So now the AI has to guess what's relevant...."
  VISUAL_13_START: s2f(174.98),  // 5249 frames
  VISUAL_13_END: s2f(199.76),  // 5993 frames

  // Visual 14: ContextRot — "And here's what makes it worse...."
  VISUAL_14_START: s2f(201.16),  // 6035 frames
  VISUAL_14_END: s2f(230.52),  // 6916 frames

  // Visual 15: CrossingPoint — "This is why AI assisted patching is really two sto..."
  VISUAL_15_START: s2f(232.12),  // 6964 frames
  VISUAL_15_END: s2f(248.38),  // 7451 frames

  // Visual 16: CrossingPoint — "But on a large code base, the kind you get after y..."
  VISUAL_16_START: s2f(249.76),  // 7493 frames
  VISUAL_16_END: s2f(279.02),  // 8371 frames

  // Visual 17: CrossingPoint — "And here's the catch...."
  VISUAL_17_START: s2f(280.16),  // 8405 frames
  VISUAL_17_END: s2f(290.38),  // 8711 frames

  // Visual 18: veo:veo_developer_edit — "Regeneration doesn't have this problem...."
  VISUAL_18_START: s2f(292.48),  // 8774 frames
  VISUAL_18_END: s2f(319.86),  // 9596 frames

  // Visual 19: veo:veo_developer_edit — "And there's something else...."
  VISUAL_19_START: s2f(320.92),  // 9628 frames
  VISUAL_19_END: s2f(365.0),  // 10950 frames

  // Visual 20: CrossingPoint — "Meanwhile, generation just crossed below both line..."
  VISUAL_20_START: s2f(366.62),  // 10999 frames
  VISUAL_20_END: s2f(377.3),  // 11319 frames

  // Visual 21: veo:07_split_screen_sepia — "Tools like cursor and clawed code are the best-dar..."
  VISUAL_21_START: s2f(379.02),  // 11371 frames
  VISUAL_21_END: s2f(392.9),  // 11787 frames

  // Visual 22: PieChart — "This is the part of software economics nobody talk..."
  VISUAL_22_START: s2f(394.82),  // 11845 frames
  VISUAL_22_END: s2f(420.36),  // 12611 frames

  // Visual 23: PieToCurve — "And those costs compound literally...."
  // Extended to fill remaining section duration (was 432.64s, now 435s).
  VISUAL_23_START: s2f(421.76),  // 12653 frames
  VISUAL_23_END: s2f(435.0),   // 13050 frames — fills to end of section
};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
  { start: BEATS.VISUAL_00_START, end: BEATS.VISUAL_00_END, id: "SockPriceChart", desc: "This isn't nostalgia, it's economics" },
  { start: BEATS.VISUAL_01_START, end: BEATS.VISUAL_01_END, id: "ThresholdHighlight", desc: "In 1950 wool sock cost real money, darning made sense" },
  { start: BEATS.VISUAL_02_START, end: BEATS.VISUAL_02_END, id: "LinesDiverge", desc: "Mid-1960s math flipped, darning became irrational" },
  { start: BEATS.VISUAL_03_START, end: BEATS.VISUAL_03_END, id: "CodeCostChart", desc: "Now look at code" },
  { start: BEATS.VISUAL_04_START, end: BEATS.VISUAL_04_END, id: "AIMilestones", desc: "For decades generating expensive, you patched, rational" },
  { start: BEATS.VISUAL_05_START, end: BEATS.VISUAL_05_END, id: "CodeCostChart", desc: "AI made patching faster too, Cursor Claude Copilot" },
  { start: BEATS.VISUAL_06_START, end: BEATS.VISUAL_06_END, id: "CodeCostChartMini", desc: "Each patch getting faster, that's real, you feel it" },
  { start: BEATS.VISUAL_07_START, end: BEATS.VISUAL_07_END, id: "CrossingPoint", desc: "But watch dashed line, debt accumulates faster" },
  { start: BEATS.VISUAL_08_START, end: BEATS.VISUAL_08_END, id: "CrossingPoint", desc: "GitHub 55% speedup, Uplevel 800 devs no change" },
  { start: BEATS.VISUAL_09_START, end: BEATS.VISUAL_09_END, id: "CrossingPoint", desc: "GitClear 44% churn, refactoring -60%, piling on" },
  { start: BEATS.VISUAL_10_START, end: BEATS.VISUAL_10_END, id: "ContextRot", desc: "Something else hiding in debt, AI-specific" },
  { start: BEATS.VISUAL_11_START, end: BEATS.VISUAL_11_END, id: "ContextRot", desc: "Small codebase AI brilliant, context covers everything" },
  { start: BEATS.VISUAL_12_START, end: BEATS.VISUAL_12_END, id: "ContextRot", desc: "Codebases grow, window stays same, millions of tokens" },
  { start: BEATS.VISUAL_13_START, end: BEATS.VISUAL_13_END, id: "ContextRot", desc: "AI guesses relevance, vector search fails, agentic slow" },
  { start: BEATS.VISUAL_14_START, end: BEATS.VISUAL_14_END, id: "ContextRot", desc: "EMNLP: performance degrades with length, context rot" },
  { start: BEATS.VISUAL_15_START, end: BEATS.VISUAL_15_END, id: "CrossingPoint", desc: "AI patching two stories, small codebase transformative" },
  { start: BEATS.VISUAL_16_START, end: BEATS.VISUAL_16_END, id: "CrossingPoint", desc: "Large codebase 19% slower, 39-point perception gap" },
  { start: BEATS.VISUAL_17_START, end: BEATS.VISUAL_17_END, id: "PatchCycle", desc: "Every patch makes codebase bigger, pushes to worse world" },
  { start: BEATS.VISUAL_18_START, end: BEATS.VISUAL_18_END, id: "veo:veo_developer_edit", desc: "Regeneration no problem, prompt fits, no retrieval no rot" },
  { start: BEATS.VISUAL_19_START, end: BEATS.VISUAL_19_END, id: "ContextWindowComparison", desc: "NL is models deepest fluency, room to think" },
  { start: BEATS.VISUAL_20_START, end: BEATS.VISUAL_20_END, id: "CrossingPoint", desc: "Generation crossed below both lines, debt resets" },
  { start: BEATS.VISUAL_21_START, end: BEATS.VISUAL_21_END, id: "veo:07_split_screen_sepia", desc: "Best darning needles ever, still accumulation" },
  { start: BEATS.VISUAL_22_START, end: BEATS.VISUAL_22_END, id: "PieChart", desc: "80-90% cost is maintenance, McKinsey Stripe tech debt" },
  { start: BEATS.VISUAL_23_START, end: BEATS.VISUAL_23_END, id: "PieToCurve", desc: "Costs compound literally, unless you regenerate" },
];

// Props schema
export const Part1EconomicsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsProps: z.infer<typeof Part1EconomicsProps> = {
  showTitle: true,
};

export type Part1EconomicsPropsType = z.infer<typeof Part1EconomicsProps>;
