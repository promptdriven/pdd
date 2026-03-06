// Part3Mold13SubtitleTrack constants

// Duration: ~280.73s at 30fps = 8422 frames
export const TOTAL_FRAMES = 8422;
export const FPS = 30;

// Subtitle region (bottom ~11% of 1080p frame)
export const BACKDROP_Y_START = 860;
export const BACKDROP_Y_END = 1020;
export const BACKDROP_HEIGHT = 160; // 1020 - 860
export const TEXT_CENTER_Y = 940;

// Backdrop styling
export const BACKDROP_FILL = "rgba(0, 0, 0, 0.55)";
export const BACKDROP_BLUR = 4;
export const BACKDROP_FEATHER_PX = 20;

// Text container
export const TEXT_MAX_WIDTH = 1600;
export const TEXT_PADDING_V = 24;
export const TEXT_PADDING_H = 40;

// Typography
export const FONT_FAMILY = "'Inter', sans-serif";
export const FONT_SIZE = 36;
export const LETTER_SPACING = "0.01em";
export const WORD_SPACING = 10;
export const TEXT_SHADOW = "0 2px 8px rgba(0, 0, 0, 0.8)";

// Word states
export const CURRENT_COLOR = "#FFFFFF";
export const CURRENT_WEIGHT = 700;
export const CURRENT_SCALE = 1.05;

export const RECENT_COLOR = "rgba(255, 255, 255, 0.9)";
export const RECENT_WEIGHT = 500;

export const OLDER_COLOR = "#CBD5E1";
export const OLDER_OPACITY = 0.7;
export const OLDER_WEIGHT = 400;

// "Recent" = spoken within last 0.5s = 15 frames
export const RECENT_WINDOW_FRAMES = 15;

// Background color
export const BG_COLOR = "#0A1628";

// Animation timing (frames)
export const WORD_APPEAR_DURATION = 6;
export const HIGHLIGHT_DURATION = 6;
export const WINDOW_SLIDE_DURATION = 8;
export const TRACK_FADE_IN_FRAMES = 15;
export const TRACK_FADE_OUT_FRAMES = 30;
export const WINDOW_SIZE = 12;

// Subtitle start (after title card fades) — frame 150 = 5s
export const SUBTITLE_START_FRAME = 150;

// Silence gap between segments
export const SILENCE_GAP_FRAMES = 9; // 0.3s
export const SEGMENT_CLEAR_DURATION = 10;

// Word exit animation
export const EXIT_DURATION = 6;
export const EXIT_SLIDE_PX = 20;

// Word data types
export interface WordEntry {
  word: string;
  startFrame: number;
  endFrame: number;
  segment: number;
}

// Embedded word timestamps for Part 3 Mold narration
// Full narration covering ~280.73 seconds of content, organized by 25 segments
// Narration covers: The prompt-as-mold paradigm, three pillars of PDD (prompt, tests,
// code), practical workflow, CodeRabbit/Dora metrics, natural language context windows,
// the ratchet mechanism, and the specification-first development approach.
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "The prompt is the mold — not a suggestion, not a comment."
  { word: "The", startFrame: 150, endFrame: 160, segment: 0 },
  { word: "prompt", startFrame: 162, endFrame: 182, segment: 0 },
  { word: "is", startFrame: 184, endFrame: 190, segment: 0 },
  { word: "the", startFrame: 192, endFrame: 198, segment: 0 },
  { word: "mold", startFrame: 200, endFrame: 220, segment: 0 },
  { word: "—", startFrame: 222, endFrame: 228, segment: 0 },
  { word: "not", startFrame: 230, endFrame: 240, segment: 0 },
  { word: "a", startFrame: 242, endFrame: 246, segment: 0 },
  { word: "suggestion,", startFrame: 248, endFrame: 278, segment: 0 },
  { word: "not", startFrame: 280, endFrame: 290, segment: 0 },
  { word: "a", startFrame: 292, endFrame: 296, segment: 0 },
  { word: "comment.", startFrame: 298, endFrame: 330, segment: 0 },

  // Segment 1: "It is the source of truth for what the software does."
  { word: "It", startFrame: 360, endFrame: 368, segment: 1 },
  { word: "is", startFrame: 370, endFrame: 378, segment: 1 },
  { word: "the", startFrame: 380, endFrame: 388, segment: 1 },
  { word: "source", startFrame: 390, endFrame: 410, segment: 1 },
  { word: "of", startFrame: 412, endFrame: 418, segment: 1 },
  { word: "truth", startFrame: 420, endFrame: 442, segment: 1 },
  { word: "for", startFrame: 444, endFrame: 454, segment: 1 },
  { word: "what", startFrame: 456, endFrame: 468, segment: 1 },
  { word: "the", startFrame: 470, endFrame: 478, segment: 1 },
  { word: "software", startFrame: 480, endFrame: 510, segment: 1 },
  { word: "does.", startFrame: 512, endFrame: 540, segment: 1 },

  // Segment 2: "Three pillars hold the system together."
  { word: "Three", startFrame: 570, endFrame: 590, segment: 2 },
  { word: "pillars", startFrame: 592, endFrame: 618, segment: 2 },
  { word: "hold", startFrame: 620, endFrame: 638, segment: 2 },
  { word: "the", startFrame: 640, endFrame: 648, segment: 2 },
  { word: "system", startFrame: 650, endFrame: 674, segment: 2 },
  { word: "together.", startFrame: 676, endFrame: 714, segment: 2 },

  // Segment 3: "First: the prompt. A natural language specification."
  { word: "First:", startFrame: 744, endFrame: 768, segment: 3 },
  { word: "the", startFrame: 770, endFrame: 778, segment: 3 },
  { word: "prompt.", startFrame: 780, endFrame: 810, segment: 3 },
  { word: "A", startFrame: 820, endFrame: 826, segment: 3 },
  { word: "natural", startFrame: 828, endFrame: 852, segment: 3 },
  { word: "language", startFrame: 854, endFrame: 882, segment: 3 },
  { word: "specification.", startFrame: 884, endFrame: 936, segment: 3 },

  // Segment 4: "It describes behavior, constraints, edge cases — everything the code must satisfy."
  { word: "It", startFrame: 966, endFrame: 974, segment: 4 },
  { word: "describes", startFrame: 976, endFrame: 1006, segment: 4 },
  { word: "behavior,", startFrame: 1008, endFrame: 1040, segment: 4 },
  { word: "constraints,", startFrame: 1042, endFrame: 1082, segment: 4 },
  { word: "edge", startFrame: 1084, endFrame: 1102, segment: 4 },
  { word: "cases", startFrame: 1104, endFrame: 1124, segment: 4 },
  { word: "—", startFrame: 1126, endFrame: 1134, segment: 4 },
  { word: "everything", startFrame: 1136, endFrame: 1170, segment: 4 },
  { word: "the", startFrame: 1172, endFrame: 1180, segment: 4 },
  { word: "code", startFrame: 1182, endFrame: 1200, segment: 4 },
  { word: "must", startFrame: 1202, endFrame: 1218, segment: 4 },
  { word: "satisfy.", startFrame: 1220, endFrame: 1260, segment: 4 },

  // Segment 5: "Second: tests. Automated verification that the mold holds."
  { word: "Second:", startFrame: 1290, endFrame: 1318, segment: 5 },
  { word: "tests.", startFrame: 1320, endFrame: 1350, segment: 5 },
  { word: "Automated", startFrame: 1360, endFrame: 1396, segment: 5 },
  { word: "verification", startFrame: 1398, endFrame: 1442, segment: 5 },
  { word: "that", startFrame: 1444, endFrame: 1458, segment: 5 },
  { word: "the", startFrame: 1460, endFrame: 1468, segment: 5 },
  { word: "mold", startFrame: 1470, endFrame: 1490, segment: 5 },
  { word: "holds.", startFrame: 1492, endFrame: 1526, segment: 5 },

  // Segment 6: "Not just unit tests — behavioral contracts derived from the prompt itself."
  { word: "Not", startFrame: 1556, endFrame: 1568, segment: 6 },
  { word: "just", startFrame: 1570, endFrame: 1586, segment: 6 },
  { word: "unit", startFrame: 1588, endFrame: 1606, segment: 6 },
  { word: "tests", startFrame: 1608, endFrame: 1628, segment: 6 },
  { word: "—", startFrame: 1630, endFrame: 1638, segment: 6 },
  { word: "behavioral", startFrame: 1640, endFrame: 1678, segment: 6 },
  { word: "contracts", startFrame: 1680, endFrame: 1714, segment: 6 },
  { word: "derived", startFrame: 1716, endFrame: 1742, segment: 6 },
  { word: "from", startFrame: 1744, endFrame: 1758, segment: 6 },
  { word: "the", startFrame: 1760, endFrame: 1768, segment: 6 },
  { word: "prompt", startFrame: 1770, endFrame: 1794, segment: 6 },
  { word: "itself.", startFrame: 1796, endFrame: 1832, segment: 6 },

  // Segment 7: "Third: the code. Generated, disposable, replaceable."
  { word: "Third:", startFrame: 1862, endFrame: 1890, segment: 7 },
  { word: "the", startFrame: 1892, endFrame: 1900, segment: 7 },
  { word: "code.", startFrame: 1902, endFrame: 1932, segment: 7 },
  { word: "Generated,", startFrame: 1942, endFrame: 1978, segment: 7 },
  { word: "disposable,", startFrame: 1980, endFrame: 2020, segment: 7 },
  { word: "replaceable.", startFrame: 2022, endFrame: 2070, segment: 7 },

  // Segment 8: "If the code drifts from the spec, you don't patch it."
  { word: "If", startFrame: 2100, endFrame: 2108, segment: 8 },
  { word: "the", startFrame: 2110, endFrame: 2118, segment: 8 },
  { word: "code", startFrame: 2120, endFrame: 2138, segment: 8 },
  { word: "drifts", startFrame: 2140, endFrame: 2166, segment: 8 },
  { word: "from", startFrame: 2168, endFrame: 2182, segment: 8 },
  { word: "the", startFrame: 2184, endFrame: 2192, segment: 8 },
  { word: "spec,", startFrame: 2194, endFrame: 2220, segment: 8 },
  { word: "you", startFrame: 2222, endFrame: 2234, segment: 8 },
  { word: "don't", startFrame: 2236, endFrame: 2254, segment: 8 },
  { word: "patch", startFrame: 2256, endFrame: 2278, segment: 8 },
  { word: "it.", startFrame: 2280, endFrame: 2304, segment: 8 },

  // Segment 9: "You regenerate it. Fix the mold, not the plastic."
  { word: "You", startFrame: 2334, endFrame: 2346, segment: 9 },
  { word: "regenerate", startFrame: 2348, endFrame: 2388, segment: 9 },
  { word: "it.", startFrame: 2390, endFrame: 2416, segment: 9 },
  { word: "Fix", startFrame: 2426, endFrame: 2444, segment: 9 },
  { word: "the", startFrame: 2446, endFrame: 2454, segment: 9 },
  { word: "mold,", startFrame: 2456, endFrame: 2480, segment: 9 },
  { word: "not", startFrame: 2482, endFrame: 2496, segment: 9 },
  { word: "the", startFrame: 2498, endFrame: 2506, segment: 9 },
  { word: "plastic.", startFrame: 2508, endFrame: 2546, segment: 9 },

  // Segment 10: "CodeRabbit measured this: teams using structured prompts saw 30% fewer review cycles."
  { word: "CodeRabbit", startFrame: 2576, endFrame: 2616, segment: 10 },
  { word: "measured", startFrame: 2618, endFrame: 2646, segment: 10 },
  { word: "this:", startFrame: 2648, endFrame: 2672, segment: 10 },
  { word: "teams", startFrame: 2682, endFrame: 2704, segment: 10 },
  { word: "using", startFrame: 2706, endFrame: 2726, segment: 10 },
  { word: "structured", startFrame: 2728, endFrame: 2764, segment: 10 },
  { word: "prompts", startFrame: 2766, endFrame: 2794, segment: 10 },
  { word: "saw", startFrame: 2796, endFrame: 2812, segment: 10 },
  { word: "30%", startFrame: 2814, endFrame: 2838, segment: 10 },
  { word: "fewer", startFrame: 2840, endFrame: 2862, segment: 10 },
  { word: "review", startFrame: 2864, endFrame: 2890, segment: 10 },
  { word: "cycles.", startFrame: 2892, endFrame: 2930, segment: 10 },

  // Segment 11: "Dora metrics confirm it — lead time drops when specs are precise."
  { word: "Dora", startFrame: 2960, endFrame: 2984, segment: 11 },
  { word: "metrics", startFrame: 2986, endFrame: 3014, segment: 11 },
  { word: "confirm", startFrame: 3016, endFrame: 3042, segment: 11 },
  { word: "it", startFrame: 3044, endFrame: 3052, segment: 11 },
  { word: "—", startFrame: 3054, endFrame: 3062, segment: 11 },
  { word: "lead", startFrame: 3064, endFrame: 3082, segment: 11 },
  { word: "time", startFrame: 3084, endFrame: 3102, segment: 11 },
  { word: "drops", startFrame: 3104, endFrame: 3126, segment: 11 },
  { word: "when", startFrame: 3128, endFrame: 3142, segment: 11 },
  { word: "specs", startFrame: 3144, endFrame: 3168, segment: 11 },
  { word: "are", startFrame: 3170, endFrame: 3180, segment: 11 },
  { word: "precise.", startFrame: 3182, endFrame: 3222, segment: 11 },

  // Segment 12: "The prompt functions as a natural language context window."
  { word: "The", startFrame: 3252, endFrame: 3262, segment: 12 },
  { word: "prompt", startFrame: 3264, endFrame: 3288, segment: 12 },
  { word: "functions", startFrame: 3290, endFrame: 3322, segment: 12 },
  { word: "as", startFrame: 3324, endFrame: 3332, segment: 12 },
  { word: "a", startFrame: 3334, endFrame: 3338, segment: 12 },
  { word: "natural", startFrame: 3340, endFrame: 3366, segment: 12 },
  { word: "language", startFrame: 3368, endFrame: 3396, segment: 12 },
  { word: "context", startFrame: 3398, endFrame: 3424, segment: 12 },
  { word: "window.", startFrame: 3426, endFrame: 3462, segment: 12 },

  // Segment 13: "It carries intent forward across every regeneration."
  { word: "It", startFrame: 3492, endFrame: 3500, segment: 13 },
  { word: "carries", startFrame: 3502, endFrame: 3530, segment: 13 },
  { word: "intent", startFrame: 3532, endFrame: 3558, segment: 13 },
  { word: "forward", startFrame: 3560, endFrame: 3588, segment: 13 },
  { word: "across", startFrame: 3590, endFrame: 3614, segment: 13 },
  { word: "every", startFrame: 3616, endFrame: 3636, segment: 13 },
  { word: "regeneration.", startFrame: 3638, endFrame: 3694, segment: 13 },

  // Segment 14: "Without it, context degrades with each edit."
  { word: "Without", startFrame: 3724, endFrame: 3752, segment: 14 },
  { word: "it,", startFrame: 3754, endFrame: 3770, segment: 14 },
  { word: "context", startFrame: 3772, endFrame: 3800, segment: 14 },
  { word: "degrades", startFrame: 3802, endFrame: 3834, segment: 14 },
  { word: "with", startFrame: 3836, endFrame: 3850, segment: 14 },
  { word: "each", startFrame: 3852, endFrame: 3870, segment: 14 },
  { word: "edit.", startFrame: 3872, endFrame: 3902, segment: 14 },

  // Segment 15: "The ratchet mechanism prevents backsliding."
  { word: "The", startFrame: 3932, endFrame: 3942, segment: 15 },
  { word: "ratchet", startFrame: 3944, endFrame: 3974, segment: 15 },
  { word: "mechanism", startFrame: 3976, endFrame: 4012, segment: 15 },
  { word: "prevents", startFrame: 4014, endFrame: 4044, segment: 15 },
  { word: "backsliding.", startFrame: 4046, endFrame: 4098, segment: 15 },

  // Segment 16: "Each test that passes becomes a permanent constraint."
  { word: "Each", startFrame: 4128, endFrame: 4146, segment: 16 },
  { word: "test", startFrame: 4148, endFrame: 4168, segment: 16 },
  { word: "that", startFrame: 4170, endFrame: 4184, segment: 16 },
  { word: "passes", startFrame: 4186, endFrame: 4214, segment: 16 },
  { word: "becomes", startFrame: 4216, endFrame: 4244, segment: 16 },
  { word: "a", startFrame: 4246, endFrame: 4252, segment: 16 },
  { word: "permanent", startFrame: 4254, endFrame: 4292, segment: 16 },
  { word: "constraint.", startFrame: 4294, endFrame: 4340, segment: 16 },

  // Segment 17: "The system can only move forward — never backward."
  { word: "The", startFrame: 4370, endFrame: 4380, segment: 17 },
  { word: "system", startFrame: 4382, endFrame: 4408, segment: 17 },
  { word: "can", startFrame: 4410, endFrame: 4424, segment: 17 },
  { word: "only", startFrame: 4426, endFrame: 4446, segment: 17 },
  { word: "move", startFrame: 4448, endFrame: 4468, segment: 17 },
  { word: "forward", startFrame: 4470, endFrame: 4500, segment: 17 },
  { word: "—", startFrame: 4502, endFrame: 4510, segment: 17 },
  { word: "never", startFrame: 4512, endFrame: 4534, segment: 17 },
  { word: "backward.", startFrame: 4536, endFrame: 4576, segment: 17 },

  // Segment 18: "You write the prompt. The LLM generates code. Tests verify conformance."
  { word: "You", startFrame: 4606, endFrame: 4618, segment: 18 },
  { word: "write", startFrame: 4620, endFrame: 4642, segment: 18 },
  { word: "the", startFrame: 4644, endFrame: 4652, segment: 18 },
  { word: "prompt.", startFrame: 4654, endFrame: 4688, segment: 18 },
  { word: "The", startFrame: 4698, endFrame: 4708, segment: 18 },
  { word: "LLM", startFrame: 4710, endFrame: 4736, segment: 18 },
  { word: "generates", startFrame: 4738, endFrame: 4772, segment: 18 },
  { word: "code.", startFrame: 4774, endFrame: 4804, segment: 18 },
  { word: "Tests", startFrame: 4814, endFrame: 4836, segment: 18 },
  { word: "verify", startFrame: 4838, endFrame: 4864, segment: 18 },
  { word: "conformance.", startFrame: 4866, endFrame: 4920, segment: 18 },

  // Segment 19: "If tests fail, you refine the prompt — not the code."
  { word: "If", startFrame: 4950, endFrame: 4958, segment: 19 },
  { word: "tests", startFrame: 4960, endFrame: 4982, segment: 19 },
  { word: "fail,", startFrame: 4984, endFrame: 5008, segment: 19 },
  { word: "you", startFrame: 5010, endFrame: 5022, segment: 19 },
  { word: "refine", startFrame: 5024, endFrame: 5050, segment: 19 },
  { word: "the", startFrame: 5052, endFrame: 5060, segment: 19 },
  { word: "prompt", startFrame: 5062, endFrame: 5088, segment: 19 },
  { word: "—", startFrame: 5090, endFrame: 5098, segment: 19 },
  { word: "not", startFrame: 5100, endFrame: 5114, segment: 19 },
  { word: "the", startFrame: 5116, endFrame: 5124, segment: 19 },
  { word: "code.", startFrame: 5126, endFrame: 5158, segment: 19 },

  // Segment 20: "The code is a side effect of getting the specification right."
  { word: "The", startFrame: 5188, endFrame: 5198, segment: 20 },
  { word: "code", startFrame: 5200, endFrame: 5218, segment: 20 },
  { word: "is", startFrame: 5220, endFrame: 5228, segment: 20 },
  { word: "a", startFrame: 5230, endFrame: 5234, segment: 20 },
  { word: "side", startFrame: 5236, endFrame: 5256, segment: 20 },
  { word: "effect", startFrame: 5258, endFrame: 5282, segment: 20 },
  { word: "of", startFrame: 5284, endFrame: 5292, segment: 20 },
  { word: "getting", startFrame: 5294, endFrame: 5320, segment: 20 },
  { word: "the", startFrame: 5322, endFrame: 5330, segment: 20 },
  { word: "specification", startFrame: 5332, endFrame: 5384, segment: 20 },
  { word: "right.", startFrame: 5386, endFrame: 5418, segment: 20 },

  // Segment 21: "Think about what that means for code review."
  { word: "Think", startFrame: 5448, endFrame: 5470, segment: 21 },
  { word: "about", startFrame: 5472, endFrame: 5492, segment: 21 },
  { word: "what", startFrame: 5494, endFrame: 5510, segment: 21 },
  { word: "that", startFrame: 5512, endFrame: 5528, segment: 21 },
  { word: "means", startFrame: 5530, endFrame: 5552, segment: 21 },
  { word: "for", startFrame: 5554, endFrame: 5566, segment: 21 },
  { word: "code", startFrame: 5568, endFrame: 5588, segment: 21 },
  { word: "review.", startFrame: 5590, endFrame: 5626, segment: 21 },

  // Segment 22: "You review the prompt, not thousands of lines of generated output."
  { word: "You", startFrame: 5656, endFrame: 5668, segment: 22 },
  { word: "review", startFrame: 5670, endFrame: 5696, segment: 22 },
  { word: "the", startFrame: 5698, endFrame: 5706, segment: 22 },
  { word: "prompt,", startFrame: 5708, endFrame: 5740, segment: 22 },
  { word: "not", startFrame: 5742, endFrame: 5756, segment: 22 },
  { word: "thousands", startFrame: 5758, endFrame: 5792, segment: 22 },
  { word: "of", startFrame: 5794, endFrame: 5802, segment: 22 },
  { word: "lines", startFrame: 5804, endFrame: 5826, segment: 22 },
  { word: "of", startFrame: 5828, endFrame: 5836, segment: 22 },
  { word: "generated", startFrame: 5838, endFrame: 5872, segment: 22 },
  { word: "output.", startFrame: 5874, endFrame: 5912, segment: 22 },

  // Segment 23: "The specification is the artifact. Everything else follows from it."
  { word: "The", startFrame: 5942, endFrame: 5952, segment: 23 },
  { word: "specification", startFrame: 5954, endFrame: 6008, segment: 23 },
  { word: "is", startFrame: 6010, endFrame: 6018, segment: 23 },
  { word: "the", startFrame: 6020, endFrame: 6028, segment: 23 },
  { word: "artifact.", startFrame: 6030, endFrame: 6072, segment: 23 },
  { word: "Everything", startFrame: 6082, endFrame: 6120, segment: 23 },
  { word: "else", startFrame: 6122, endFrame: 6144, segment: 23 },
  { word: "follows", startFrame: 6146, endFrame: 6176, segment: 23 },
  { word: "from", startFrame: 6178, endFrame: 6194, segment: 23 },
  { word: "it.", startFrame: 6196, endFrame: 6222, segment: 23 },

  // Segment 24: "That's the mold. That's prompt-driven development."
  { word: "That's", startFrame: 6252, endFrame: 6274, segment: 24 },
  { word: "the", startFrame: 6276, endFrame: 6284, segment: 24 },
  { word: "mold.", startFrame: 6286, endFrame: 6318, segment: 24 },
  { word: "That's", startFrame: 6328, endFrame: 6350, segment: 24 },
  { word: "prompt-driven", startFrame: 6352, endFrame: 6400, segment: 24 },
  { word: "development.", startFrame: 6402, endFrame: 6460, segment: 24 },
];
