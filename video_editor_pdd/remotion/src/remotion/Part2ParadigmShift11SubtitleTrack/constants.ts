// Part2ParadigmShift11SubtitleTrack constants

// Duration: ~195.79s at 30fps = 5874 frames
export const TOTAL_FRAMES = 5874;
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

// Embedded word timestamps for Part 2 Paradigm Shift narration
// Full narration covering ~195.79 seconds of content, organized by 19 segments
// Narration text: "Not cheaper materials — a shift in how things are made. The same
// pattern across textiles, plastics, semiconductors. The value didn't stay in the
// thing itself. Design the mold once, produce unlimited identical parts. Find a
// defect? Fix the mold — not every individual part. The cost is in the specification,
// not the production. Value migrates from the object to the specification. The plastic
// part is disposable. The mold is everything. 1980s — engineers hand-drew gate layouts.
// 1985 — Verilog HDL: describe behavior, not wires. Synopsys added verification with
// SAT and SMT solvers. Same revolution: specification replaced manual construction.
// The prompt is your mold. Code is plastic. Tests lock the behavior. We've seen this
// before — we just didn't recognize it."
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "Not cheaper materials — a shift in how things are made."
  { word: "Not", startFrame: 150, endFrame: 160, segment: 0 },
  { word: "cheaper", startFrame: 162, endFrame: 180, segment: 0 },
  { word: "materials", startFrame: 182, endFrame: 206, segment: 0 },
  { word: "—", startFrame: 208, endFrame: 214, segment: 0 },
  { word: "a", startFrame: 216, endFrame: 220, segment: 0 },
  { word: "shift", startFrame: 222, endFrame: 238, segment: 0 },
  { word: "in", startFrame: 240, endFrame: 246, segment: 0 },
  { word: "how", startFrame: 248, endFrame: 260, segment: 0 },
  { word: "things", startFrame: 262, endFrame: 280, segment: 0 },
  { word: "are", startFrame: 282, endFrame: 292, segment: 0 },
  { word: "made.", startFrame: 294, endFrame: 318, segment: 0 },

  // Segment 1: "The same pattern across textiles, plastics, semiconductors."
  { word: "The", startFrame: 348, endFrame: 358, segment: 1 },
  { word: "same", startFrame: 360, endFrame: 374, segment: 1 },
  { word: "pattern", startFrame: 376, endFrame: 398, segment: 1 },
  { word: "across", startFrame: 400, endFrame: 418, segment: 1 },
  { word: "textiles,", startFrame: 420, endFrame: 448, segment: 1 },
  { word: "plastics,", startFrame: 450, endFrame: 478, segment: 1 },
  { word: "semiconductors.", startFrame: 480, endFrame: 530, segment: 1 },

  // Segment 2: "The value didn't stay in the thing itself."
  { word: "The", startFrame: 560, endFrame: 570, segment: 2 },
  { word: "value", startFrame: 572, endFrame: 590, segment: 2 },
  { word: "didn't", startFrame: 592, endFrame: 610, segment: 2 },
  { word: "stay", startFrame: 612, endFrame: 628, segment: 2 },
  { word: "in", startFrame: 630, endFrame: 636, segment: 2 },
  { word: "the", startFrame: 638, endFrame: 646, segment: 2 },
  { word: "thing", startFrame: 648, endFrame: 666, segment: 2 },
  { word: "itself.", startFrame: 668, endFrame: 698, segment: 2 },

  // Segment 3: "Design the mold once, produce unlimited identical parts."
  { word: "Design", startFrame: 728, endFrame: 748, segment: 3 },
  { word: "the", startFrame: 750, endFrame: 758, segment: 3 },
  { word: "mold", startFrame: 760, endFrame: 778, segment: 3 },
  { word: "once,", startFrame: 780, endFrame: 800, segment: 3 },
  { word: "produce", startFrame: 802, endFrame: 824, segment: 3 },
  { word: "unlimited", startFrame: 826, endFrame: 856, segment: 3 },
  { word: "identical", startFrame: 858, endFrame: 888, segment: 3 },
  { word: "parts.", startFrame: 890, endFrame: 918, segment: 3 },

  // Segment 4: "Find a defect? Fix the mold — not every individual part."
  { word: "Find", startFrame: 948, endFrame: 964, segment: 4 },
  { word: "a", startFrame: 966, endFrame: 970, segment: 4 },
  { word: "defect?", startFrame: 972, endFrame: 998, segment: 4 },
  { word: "Fix", startFrame: 1008, endFrame: 1024, segment: 4 },
  { word: "the", startFrame: 1026, endFrame: 1034, segment: 4 },
  { word: "mold", startFrame: 1036, endFrame: 1054, segment: 4 },
  { word: "—", startFrame: 1056, endFrame: 1064, segment: 4 },
  { word: "not", startFrame: 1066, endFrame: 1078, segment: 4 },
  { word: "every", startFrame: 1080, endFrame: 1098, segment: 4 },
  { word: "individual", startFrame: 1100, endFrame: 1132, segment: 4 },
  { word: "part.", startFrame: 1134, endFrame: 1160, segment: 4 },

  // Segment 5: "The cost is in the specification, not the production."
  { word: "The", startFrame: 1190, endFrame: 1200, segment: 5 },
  { word: "cost", startFrame: 1202, endFrame: 1218, segment: 5 },
  { word: "is", startFrame: 1220, endFrame: 1228, segment: 5 },
  { word: "in", startFrame: 1230, endFrame: 1236, segment: 5 },
  { word: "the", startFrame: 1238, endFrame: 1246, segment: 5 },
  { word: "specification,", startFrame: 1248, endFrame: 1296, segment: 5 },
  { word: "not", startFrame: 1298, endFrame: 1310, segment: 5 },
  { word: "the", startFrame: 1312, endFrame: 1320, segment: 5 },
  { word: "production.", startFrame: 1322, endFrame: 1362, segment: 5 },

  // Segment 6: "Value migrates from the object to the specification."
  { word: "Value", startFrame: 1392, endFrame: 1412, segment: 6 },
  { word: "migrates", startFrame: 1414, endFrame: 1440, segment: 6 },
  { word: "from", startFrame: 1442, endFrame: 1456, segment: 6 },
  { word: "the", startFrame: 1458, endFrame: 1466, segment: 6 },
  { word: "object", startFrame: 1468, endFrame: 1490, segment: 6 },
  { word: "to", startFrame: 1492, endFrame: 1500, segment: 6 },
  { word: "the", startFrame: 1502, endFrame: 1510, segment: 6 },
  { word: "specification.", startFrame: 1512, endFrame: 1564, segment: 6 },

  // Segment 7: "The plastic part is disposable."
  { word: "The", startFrame: 1594, endFrame: 1604, segment: 7 },
  { word: "plastic", startFrame: 1606, endFrame: 1628, segment: 7 },
  { word: "part", startFrame: 1630, endFrame: 1648, segment: 7 },
  { word: "is", startFrame: 1650, endFrame: 1658, segment: 7 },
  { word: "disposable.", startFrame: 1660, endFrame: 1704, segment: 7 },

  // Segment 8: "The mold is everything."
  { word: "The", startFrame: 1734, endFrame: 1744, segment: 8 },
  { word: "mold", startFrame: 1746, endFrame: 1766, segment: 8 },
  { word: "is", startFrame: 1768, endFrame: 1776, segment: 8 },
  { word: "everything.", startFrame: 1778, endFrame: 1820, segment: 8 },

  // Segment 9: "1980s — engineers hand-drew gate layouts."
  { word: "1980s", startFrame: 1850, endFrame: 1878, segment: 9 },
  { word: "—", startFrame: 1880, endFrame: 1888, segment: 9 },
  { word: "engineers", startFrame: 1890, endFrame: 1920, segment: 9 },
  { word: "hand-drew", startFrame: 1922, endFrame: 1954, segment: 9 },
  { word: "gate", startFrame: 1956, endFrame: 1974, segment: 9 },
  { word: "layouts.", startFrame: 1976, endFrame: 2012, segment: 9 },

  // Segment 10: "1985 — Verilog HDL: describe behavior, not wires."
  { word: "1985", startFrame: 2042, endFrame: 2066, segment: 10 },
  { word: "—", startFrame: 2068, endFrame: 2076, segment: 10 },
  { word: "Verilog", startFrame: 2078, endFrame: 2106, segment: 10 },
  { word: "HDL:", startFrame: 2108, endFrame: 2130, segment: 10 },
  { word: "describe", startFrame: 2132, endFrame: 2158, segment: 10 },
  { word: "behavior,", startFrame: 2160, endFrame: 2194, segment: 10 },
  { word: "not", startFrame: 2196, endFrame: 2210, segment: 10 },
  { word: "wires.", startFrame: 2212, endFrame: 2244, segment: 10 },

  // Segment 11: "Synopsys added verification with SAT and SMT solvers."
  { word: "Synopsys", startFrame: 2274, endFrame: 2306, segment: 11 },
  { word: "added", startFrame: 2308, endFrame: 2328, segment: 11 },
  { word: "verification", startFrame: 2330, endFrame: 2374, segment: 11 },
  { word: "with", startFrame: 2376, endFrame: 2390, segment: 11 },
  { word: "SAT", startFrame: 2392, endFrame: 2414, segment: 11 },
  { word: "and", startFrame: 2416, endFrame: 2426, segment: 11 },
  { word: "SMT", startFrame: 2428, endFrame: 2450, segment: 11 },
  { word: "solvers.", startFrame: 2452, endFrame: 2490, segment: 11 },

  // Segment 12: "Same revolution: specification replaced manual construction."
  { word: "Same", startFrame: 2520, endFrame: 2538, segment: 12 },
  { word: "revolution:", startFrame: 2540, endFrame: 2578, segment: 12 },
  { word: "specification", startFrame: 2580, endFrame: 2630, segment: 12 },
  { word: "replaced", startFrame: 2632, endFrame: 2660, segment: 12 },
  { word: "manual", startFrame: 2662, endFrame: 2686, segment: 12 },
  { word: "construction.", startFrame: 2688, endFrame: 2736, segment: 12 },

  // Segment 13: "The prompt is your mold."
  { word: "The", startFrame: 2766, endFrame: 2776, segment: 13 },
  { word: "prompt", startFrame: 2778, endFrame: 2800, segment: 13 },
  { word: "is", startFrame: 2802, endFrame: 2810, segment: 13 },
  { word: "your", startFrame: 2812, endFrame: 2828, segment: 13 },
  { word: "mold.", startFrame: 2830, endFrame: 2860, segment: 13 },

  // Segment 14: "Code is plastic."
  { word: "Code", startFrame: 2890, endFrame: 2908, segment: 14 },
  { word: "is", startFrame: 2910, endFrame: 2918, segment: 14 },
  { word: "plastic.", startFrame: 2920, endFrame: 2956, segment: 14 },

  // Segment 15: "Tests lock the behavior."
  { word: "Tests", startFrame: 2986, endFrame: 3006, segment: 15 },
  { word: "lock", startFrame: 3008, endFrame: 3026, segment: 15 },
  { word: "the", startFrame: 3028, endFrame: 3036, segment: 15 },
  { word: "behavior.", startFrame: 3038, endFrame: 3076, segment: 15 },

  // Segment 16: "We've seen this before —"
  { word: "We've", startFrame: 3106, endFrame: 3124, segment: 16 },
  { word: "seen", startFrame: 3126, endFrame: 3144, segment: 16 },
  { word: "this", startFrame: 3146, endFrame: 3162, segment: 16 },
  { word: "before", startFrame: 3164, endFrame: 3186, segment: 16 },
  { word: "—", startFrame: 3188, endFrame: 3196, segment: 16 },

  // Segment 17: "we just didn't recognize it."
  { word: "we", startFrame: 3210, endFrame: 3222, segment: 17 },
  { word: "just", startFrame: 3224, endFrame: 3240, segment: 17 },
  { word: "didn't", startFrame: 3242, endFrame: 3262, segment: 17 },
  { word: "recognize", startFrame: 3264, endFrame: 3296, segment: 17 },
  { word: "it.", startFrame: 3298, endFrame: 3326, segment: 17 },
];
