// Shared subtitle track constants (Part2 + Part5)

// ─── Part5 Constants ────────────────────────────────────────────────────────

// Duration: ~98.42s at 30fps = 2953 frames
export const TOTAL_FRAMES = 2953;
export const FPS = 30;

// Subtitle region (bottom portion of 1080p frame)
export const BACKDROP_Y_START = 870;
export const BACKDROP_HEIGHT = 180; // 870 to 1050
export const TEXT_CENTER_Y = 960;

// Backdrop styling
export const BACKDROP_FILL = "rgba(0, 0, 0, 0.6)";
export const BACKDROP_BLUR = 4;
export const BACKDROP_FEATHER_PX = 8;

// Text container
export const TEXT_MAX_WIDTH = 1600;
export const TEXT_PADDING_V = 24;
export const TEXT_PADDING_H = 40;

// Typography
export const FONT_FAMILY = "'Inter', sans-serif";
export const FONT_SIZE = 36;
export const FONT_WEIGHT_SEMI = 600;
export const LETTER_SPACING = "-0.01em";
export const WORD_SPACING = 12;
export const TEXT_SHADOW = "0 2px 8px rgba(0, 0, 0, 0.8)";

// Word states — current=#FFF 100%, previous=#FFF 50%, next=#FFF 30%
export const CURRENT_COLOR = "#FFFFFF";
export const CURRENT_OPACITY = 1.0;
export const CURRENT_SCALE = 1.05;

export const PREVIOUS_COLOR = "#FFFFFF";
export const PREVIOUS_OPACITY = 0.5;

export const UPCOMING_COLOR = "#FFFFFF";
export const UPCOMING_OPACITY = 0.3;

// Accent underline (green, matching Part 5 theme)
export const UNDERLINE_COLOR = "#22C55E";
export const UNDERLINE_OPACITY = 0.6;
export const UNDERLINE_HEIGHT = 2;

// Background color (dark navy)
export const BG_COLOR = "#0A1628";

// Animation timing (frames)
export const HIGHLIGHT_SCALE_UP_FRAMES = 3;
export const HIGHLIGHT_SCALE_DOWN_FRAMES = 6;
export const WORD_FADE_DURATION = 6;
export const WINDOW_SLIDE_DURATION = 10;
export const TRACK_FADE_IN_FRAMES = 15;
export const TRACK_FADE_OUT_FRAMES = 15;
export const WINDOW_SIZE = 12;

// Silence gap between segments
export const SILENCE_GAP_FRAMES = 9; // 0.3s
export const SEGMENT_CLEAR_DURATION = 10;

// Word exit animation
export const EXIT_DURATION = 10;
export const EXIT_SLIDE_PX = 20;

// Word data types
export interface WordEntry {
  word: string;
  startFrame: number;
  endFrame: number;
  segment: number;
}

// Embedded word timestamps for Part 5 Compound narration
// Full narration covering ~98.42 seconds across 2953 frames, organized by segments
// "Eighty to ninety percent of software cost is maintenance. Not features.
// Not launch. Maintenance. This is the elephant in the room. Patching
// accumulates debt linearly — each patch adds residual complexity. Generation
// resets debt each cycle — fresh code, no residue. The gap compounds. Over
// months and years, the trajectories diverge dramatically. Teams that patch
// sink deeper. Teams that generate compound their advantage. Early adoption
// creates exponential separation. Your grandmother didn't need a study to
// figure this out. When the economics flip, you stop darning. You start buying
// new socks. We're at that moment for code."
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "Eighty to ninety percent of software cost is maintenance."
  { word: "Eighty", startFrame: 20, endFrame: 42, segment: 0 },
  { word: "to", startFrame: 44, endFrame: 54, segment: 0 },
  { word: "ninety", startFrame: 56, endFrame: 80, segment: 0 },
  { word: "percent", startFrame: 82, endFrame: 108, segment: 0 },
  { word: "of", startFrame: 110, endFrame: 118, segment: 0 },
  { word: "software", startFrame: 120, endFrame: 150, segment: 0 },
  { word: "cost", startFrame: 152, endFrame: 174, segment: 0 },
  { word: "is", startFrame: 176, endFrame: 186, segment: 0 },
  { word: "maintenance.", startFrame: 188, endFrame: 238, segment: 0 },

  // Segment 1: "Not features. Not launch. Maintenance."
  { word: "Not", startFrame: 260, endFrame: 276, segment: 1 },
  { word: "features.", startFrame: 278, endFrame: 312, segment: 1 },
  { word: "Not", startFrame: 320, endFrame: 336, segment: 1 },
  { word: "launch.", startFrame: 338, endFrame: 370, segment: 1 },
  { word: "Maintenance.", startFrame: 378, endFrame: 428, segment: 1 },

  // Segment 2: "This is the elephant in the room."
  { word: "This", startFrame: 452, endFrame: 468, segment: 2 },
  { word: "is", startFrame: 470, endFrame: 480, segment: 2 },
  { word: "the", startFrame: 482, endFrame: 492, segment: 2 },
  { word: "elephant", startFrame: 494, endFrame: 528, segment: 2 },
  { word: "in", startFrame: 530, endFrame: 540, segment: 2 },
  { word: "the", startFrame: 542, endFrame: 552, segment: 2 },
  { word: "room.", startFrame: 554, endFrame: 590, segment: 2 },

  // Segment 3: "Patching accumulates debt linearly — each patch adds residual complexity."
  { word: "Patching", startFrame: 618, endFrame: 652, segment: 3 },
  { word: "accumulates", startFrame: 654, endFrame: 700, segment: 3 },
  { word: "debt", startFrame: 702, endFrame: 726, segment: 3 },
  { word: "linearly", startFrame: 728, endFrame: 766, segment: 3 },
  { word: "—", startFrame: 768, endFrame: 778, segment: 3 },
  { word: "each", startFrame: 780, endFrame: 800, segment: 3 },
  { word: "patch", startFrame: 802, endFrame: 826, segment: 3 },
  { word: "adds", startFrame: 828, endFrame: 850, segment: 3 },
  { word: "residual", startFrame: 852, endFrame: 892, segment: 3 },
  { word: "complexity.", startFrame: 894, endFrame: 944, segment: 3 },

  // Segment 4: "Generation resets debt each cycle — fresh code, no residue."
  { word: "Generation", startFrame: 972, endFrame: 1018, segment: 4 },
  { word: "resets", startFrame: 1020, endFrame: 1048, segment: 4 },
  { word: "debt", startFrame: 1050, endFrame: 1072, segment: 4 },
  { word: "each", startFrame: 1074, endFrame: 1094, segment: 4 },
  { word: "cycle", startFrame: 1096, endFrame: 1126, segment: 4 },
  { word: "—", startFrame: 1128, endFrame: 1138, segment: 4 },
  { word: "fresh", startFrame: 1140, endFrame: 1166, segment: 4 },
  { word: "code,", startFrame: 1168, endFrame: 1192, segment: 4 },
  { word: "no", startFrame: 1194, endFrame: 1208, segment: 4 },
  { word: "residue.", startFrame: 1210, endFrame: 1252, segment: 4 },

  // Segment 5: "The gap compounds."
  { word: "The", startFrame: 1280, endFrame: 1294, segment: 5 },
  { word: "gap", startFrame: 1296, endFrame: 1318, segment: 5 },
  { word: "compounds.", startFrame: 1320, endFrame: 1366, segment: 5 },

  // Segment 6: "Over months and years, the trajectories diverge dramatically."
  { word: "Over", startFrame: 1394, endFrame: 1414, segment: 6 },
  { word: "months", startFrame: 1416, endFrame: 1442, segment: 6 },
  { word: "and", startFrame: 1444, endFrame: 1456, segment: 6 },
  { word: "years,", startFrame: 1458, endFrame: 1488, segment: 6 },
  { word: "the", startFrame: 1490, endFrame: 1500, segment: 6 },
  { word: "trajectories", startFrame: 1502, endFrame: 1554, segment: 6 },
  { word: "diverge", startFrame: 1556, endFrame: 1590, segment: 6 },
  { word: "dramatically.", startFrame: 1592, endFrame: 1652, segment: 6 },

  // Segment 7: "Teams that patch sink deeper."
  { word: "Teams", startFrame: 1680, endFrame: 1704, segment: 7 },
  { word: "that", startFrame: 1706, endFrame: 1722, segment: 7 },
  { word: "patch", startFrame: 1724, endFrame: 1750, segment: 7 },
  { word: "sink", startFrame: 1752, endFrame: 1776, segment: 7 },
  { word: "deeper.", startFrame: 1778, endFrame: 1816, segment: 7 },

  // Segment 8: "Teams that generate compound their advantage."
  { word: "Teams", startFrame: 1844, endFrame: 1868, segment: 8 },
  { word: "that", startFrame: 1870, endFrame: 1886, segment: 8 },
  { word: "generate", startFrame: 1888, endFrame: 1926, segment: 8 },
  { word: "compound", startFrame: 1928, endFrame: 1962, segment: 8 },
  { word: "their", startFrame: 1964, endFrame: 1984, segment: 8 },
  { word: "advantage.", startFrame: 1986, endFrame: 2036, segment: 8 },

  // Segment 9: "Early adoption creates exponential separation."
  { word: "Early", startFrame: 2064, endFrame: 2088, segment: 9 },
  { word: "adoption", startFrame: 2090, endFrame: 2126, segment: 9 },
  { word: "creates", startFrame: 2128, endFrame: 2160, segment: 9 },
  { word: "exponential", startFrame: 2162, endFrame: 2212, segment: 9 },
  { word: "separation.", startFrame: 2214, endFrame: 2266, segment: 9 },

  // Segment 10: "Your grandmother didn't need a study to figure this out."
  { word: "Your", startFrame: 2294, endFrame: 2312, segment: 10 },
  { word: "grandmother", startFrame: 2314, endFrame: 2356, segment: 10 },
  { word: "didn't", startFrame: 2358, endFrame: 2382, segment: 10 },
  { word: "need", startFrame: 2384, endFrame: 2404, segment: 10 },
  { word: "a", startFrame: 2406, endFrame: 2412, segment: 10 },
  { word: "study", startFrame: 2414, endFrame: 2440, segment: 10 },
  { word: "to", startFrame: 2442, endFrame: 2452, segment: 10 },
  { word: "figure", startFrame: 2454, endFrame: 2480, segment: 10 },
  { word: "this", startFrame: 2482, endFrame: 2500, segment: 10 },
  { word: "out.", startFrame: 2502, endFrame: 2532, segment: 10 },

  // Segment 11: "When the economics flip, you stop darning."
  { word: "When", startFrame: 2560, endFrame: 2578, segment: 11 },
  { word: "the", startFrame: 2580, endFrame: 2590, segment: 11 },
  { word: "economics", startFrame: 2592, endFrame: 2634, segment: 11 },
  { word: "flip,", startFrame: 2636, endFrame: 2662, segment: 11 },
  { word: "you", startFrame: 2664, endFrame: 2680, segment: 11 },
  { word: "stop", startFrame: 2682, endFrame: 2704, segment: 11 },
  { word: "darning.", startFrame: 2706, endFrame: 2748, segment: 11 },

  // Segment 12: "You start buying new socks."
  { word: "You", startFrame: 2770, endFrame: 2786, segment: 12 },
  { word: "start", startFrame: 2788, endFrame: 2812, segment: 12 },
  { word: "buying", startFrame: 2814, endFrame: 2842, segment: 12 },
  { word: "new", startFrame: 2844, endFrame: 2862, segment: 12 },
  { word: "socks.", startFrame: 2864, endFrame: 2900, segment: 12 },

  // Segment 13: "We're at that moment for code."
  { word: "We're", startFrame: 2910, endFrame: 2920, segment: 13 },
  { word: "at", startFrame: 2921, endFrame: 2926, segment: 13 },
  { word: "that", startFrame: 2927, endFrame: 2932, segment: 13 },
  { word: "moment", startFrame: 2933, endFrame: 2938, segment: 13 },
  { word: "for", startFrame: 2939, endFrame: 2943, segment: 13 },
  { word: "code.", startFrame: 2944, endFrame: 2950, segment: 13 },
];

// ─── Part2 Paradigm Shift Constants ─────────────────────────────────────────

// Duration: ~195.79s at 30fps = 5874 frames
export const P2_TOTAL_FRAMES = 5874;

// Subtitle region
export const P2_BACKDROP_Y_START = 860;
export const P2_BACKDROP_HEIGHT = 160; // 860 to 1020
export const P2_BACKDROP_FILL = "rgba(0, 0, 0, 0.55)";
export const P2_BACKDROP_FEATHER_PX = 20;

// Word states — per spec: current=#FFF 100% bold, recent=#FFF 90% medium, older=#CBD5E1 70% regular
export const P2_CURRENT_COLOR = "#FFFFFF";
export const P2_CURRENT_SCALE = 1.05;
export const P2_CURRENT_WEIGHT = 700;

export const P2_RECENT_COLOR = "#FFFFFF";
export const P2_RECENT_OPACITY = 0.9;
export const P2_RECENT_WEIGHT = 500;

export const P2_OLDER_COLOR = "#CBD5E1";
export const P2_OLDER_OPACITY = 0.7;
export const P2_OLDER_WEIGHT = 400;

// Recent word threshold: 0.5s = 15 frames at 30fps
export const P2_RECENT_THRESHOLD_FRAMES = 15;

// Accent underline (blue, matching Part 2 paradigm shift theme)
export const P2_UNDERLINE_COLOR = "#3B82F6";

// Animation timing
export const P2_TRACK_FADE_OUT_FRAMES = 30; // final 30 frames per spec

// Letter spacing per spec
export const P2_LETTER_SPACING = "0.01em";
export const P2_WORD_SPACING = 10;

// Embedded word timestamps for Part 2 Paradigm Shift narration
// Full narration covering ~195.79 seconds across 19 segments
// "Not cheaper materials — a shift in how things are made. The same pattern
// across textiles, plastics, semiconductors. The value didn't stay in the
// thing itself. Design the mold once, produce unlimited identical parts.
// Find a defect? Fix the mold — not every individual part. The cost is in
// the specification, not the production. Value migrates from the object to
// the specification. The plastic part is disposable. The mold is everything.
// 1980s — engineers hand-drew gate layouts. 1985 — Verilog HDL: describe
// behavior, not wires. Synopsys added verification with SAT and SMT solvers.
// Same revolution: specification replaced manual construction. The prompt is
// your mold. Code is plastic. Tests lock the behavior. We've seen this
// before — we just didn't recognize it."
export const P2_WORD_DATA: WordEntry[] = [
  // Segment 0: "Not cheaper materials — a shift in how things are made."
  { word: "Not", startFrame: 150, endFrame: 168, segment: 0 },
  { word: "cheaper", startFrame: 170, endFrame: 200, segment: 0 },
  { word: "materials", startFrame: 202, endFrame: 240, segment: 0 },
  { word: "—", startFrame: 242, endFrame: 252, segment: 0 },
  { word: "a", startFrame: 254, endFrame: 262, segment: 0 },
  { word: "shift", startFrame: 264, endFrame: 292, segment: 0 },
  { word: "in", startFrame: 294, endFrame: 304, segment: 0 },
  { word: "how", startFrame: 306, endFrame: 324, segment: 0 },
  { word: "things", startFrame: 326, endFrame: 354, segment: 0 },
  { word: "are", startFrame: 356, endFrame: 370, segment: 0 },
  { word: "made.", startFrame: 372, endFrame: 408, segment: 0 },

  // Segment 1: "The same pattern across textiles, plastics, semiconductors."
  { word: "The", startFrame: 438, endFrame: 452, segment: 1 },
  { word: "same", startFrame: 454, endFrame: 478, segment: 1 },
  { word: "pattern", startFrame: 480, endFrame: 514, segment: 1 },
  { word: "across", startFrame: 516, endFrame: 544, segment: 1 },
  { word: "textiles,", startFrame: 546, endFrame: 586, segment: 1 },
  { word: "plastics,", startFrame: 588, endFrame: 628, segment: 1 },
  { word: "semiconductors.", startFrame: 630, endFrame: 698, segment: 1 },

  // Segment 2: "The value didn't stay in the thing itself."
  { word: "The", startFrame: 728, endFrame: 742, segment: 2 },
  { word: "value", startFrame: 744, endFrame: 772, segment: 2 },
  { word: "didn't", startFrame: 774, endFrame: 800, segment: 2 },
  { word: "stay", startFrame: 802, endFrame: 826, segment: 2 },
  { word: "in", startFrame: 828, endFrame: 838, segment: 2 },
  { word: "the", startFrame: 840, endFrame: 852, segment: 2 },
  { word: "thing", startFrame: 854, endFrame: 880, segment: 2 },
  { word: "itself.", startFrame: 882, endFrame: 924, segment: 2 },

  // Segment 3: "Design the mold once, produce unlimited identical parts."
  { word: "Design", startFrame: 954, endFrame: 984, segment: 3 },
  { word: "the", startFrame: 986, endFrame: 998, segment: 3 },
  { word: "mold", startFrame: 1000, endFrame: 1028, segment: 3 },
  { word: "once,", startFrame: 1030, endFrame: 1058, segment: 3 },
  { word: "produce", startFrame: 1060, endFrame: 1094, segment: 3 },
  { word: "unlimited", startFrame: 1096, endFrame: 1138, segment: 3 },
  { word: "identical", startFrame: 1140, endFrame: 1180, segment: 3 },
  { word: "parts.", startFrame: 1182, endFrame: 1224, segment: 3 },

  // Segment 4: "Find a defect? Fix the mold — not every individual part."
  { word: "Find", startFrame: 1254, endFrame: 1278, segment: 4 },
  { word: "a", startFrame: 1280, endFrame: 1288, segment: 4 },
  { word: "defect?", startFrame: 1290, endFrame: 1326, segment: 4 },
  { word: "Fix", startFrame: 1336, endFrame: 1358, segment: 4 },
  { word: "the", startFrame: 1360, endFrame: 1372, segment: 4 },
  { word: "mold", startFrame: 1374, endFrame: 1400, segment: 4 },
  { word: "—", startFrame: 1402, endFrame: 1412, segment: 4 },
  { word: "not", startFrame: 1414, endFrame: 1432, segment: 4 },
  { word: "every", startFrame: 1434, endFrame: 1460, segment: 4 },
  { word: "individual", startFrame: 1462, endFrame: 1506, segment: 4 },
  { word: "part.", startFrame: 1508, endFrame: 1544, segment: 4 },

  // Segment 5: "The cost is in the specification, not the production."
  { word: "The", startFrame: 1574, endFrame: 1588, segment: 5 },
  { word: "cost", startFrame: 1590, endFrame: 1614, segment: 5 },
  { word: "is", startFrame: 1616, endFrame: 1628, segment: 5 },
  { word: "in", startFrame: 1630, endFrame: 1640, segment: 5 },
  { word: "the", startFrame: 1642, endFrame: 1654, segment: 5 },
  { word: "specification,", startFrame: 1656, endFrame: 1716, segment: 5 },
  { word: "not", startFrame: 1718, endFrame: 1736, segment: 5 },
  { word: "the", startFrame: 1738, endFrame: 1750, segment: 5 },
  { word: "production.", startFrame: 1752, endFrame: 1806, segment: 5 },

  // Segment 6: "Value migrates from the object to the specification."
  { word: "Value", startFrame: 1836, endFrame: 1864, segment: 6 },
  { word: "migrates", startFrame: 1866, endFrame: 1904, segment: 6 },
  { word: "from", startFrame: 1906, endFrame: 1924, segment: 6 },
  { word: "the", startFrame: 1926, endFrame: 1938, segment: 6 },
  { word: "object", startFrame: 1940, endFrame: 1970, segment: 6 },
  { word: "to", startFrame: 1972, endFrame: 1984, segment: 6 },
  { word: "the", startFrame: 1986, endFrame: 1998, segment: 6 },
  { word: "specification.", startFrame: 2000, endFrame: 2062, segment: 6 },

  // Segment 7: "The plastic part is disposable."
  { word: "The", startFrame: 2092, endFrame: 2106, segment: 7 },
  { word: "plastic", startFrame: 2108, endFrame: 2140, segment: 7 },
  { word: "part", startFrame: 2142, endFrame: 2166, segment: 7 },
  { word: "is", startFrame: 2168, endFrame: 2180, segment: 7 },
  { word: "disposable.", startFrame: 2182, endFrame: 2238, segment: 7 },

  // Segment 8: "The mold is everything."
  { word: "The", startFrame: 2268, endFrame: 2282, segment: 8 },
  { word: "mold", startFrame: 2284, endFrame: 2312, segment: 8 },
  { word: "is", startFrame: 2314, endFrame: 2326, segment: 8 },
  { word: "everything.", startFrame: 2328, endFrame: 2386, segment: 8 },

  // Segment 9: "1980s — engineers hand-drew gate layouts."
  { word: "1980s", startFrame: 2416, endFrame: 2450, segment: 9 },
  { word: "—", startFrame: 2452, endFrame: 2462, segment: 9 },
  { word: "engineers", startFrame: 2464, endFrame: 2508, segment: 9 },
  { word: "hand-drew", startFrame: 2510, endFrame: 2552, segment: 9 },
  { word: "gate", startFrame: 2554, endFrame: 2578, segment: 9 },
  { word: "layouts.", startFrame: 2580, endFrame: 2628, segment: 9 },

  // Segment 10: "1985 — Verilog HDL: describe behavior, not wires."
  { word: "1985", startFrame: 2658, endFrame: 2690, segment: 10 },
  { word: "—", startFrame: 2692, endFrame: 2702, segment: 10 },
  { word: "Verilog", startFrame: 2704, endFrame: 2740, segment: 10 },
  { word: "HDL:", startFrame: 2742, endFrame: 2770, segment: 10 },
  { word: "describe", startFrame: 2772, endFrame: 2808, segment: 10 },
  { word: "behavior,", startFrame: 2810, endFrame: 2852, segment: 10 },
  { word: "not", startFrame: 2854, endFrame: 2872, segment: 10 },
  { word: "wires.", startFrame: 2874, endFrame: 2916, segment: 10 },

  // Segment 11: "Synopsys added verification with SAT and SMT solvers."
  { word: "Synopsys", startFrame: 2946, endFrame: 2990, segment: 11 },
  { word: "added", startFrame: 2992, endFrame: 3018, segment: 11 },
  { word: "verification", startFrame: 3020, endFrame: 3072, segment: 11 },
  { word: "with", startFrame: 3074, endFrame: 3092, segment: 11 },
  { word: "SAT", startFrame: 3094, endFrame: 3118, segment: 11 },
  { word: "and", startFrame: 3120, endFrame: 3134, segment: 11 },
  { word: "SMT", startFrame: 3136, endFrame: 3162, segment: 11 },
  { word: "solvers.", startFrame: 3164, endFrame: 3212, segment: 11 },

  // Segment 12: "Same revolution: specification replaced manual construction."
  { word: "Same", startFrame: 3242, endFrame: 3268, segment: 12 },
  { word: "revolution:", startFrame: 3270, endFrame: 3318, segment: 12 },
  { word: "specification", startFrame: 3320, endFrame: 3380, segment: 12 },
  { word: "replaced", startFrame: 3382, endFrame: 3418, segment: 12 },
  { word: "manual", startFrame: 3420, endFrame: 3452, segment: 12 },
  { word: "construction.", startFrame: 3454, endFrame: 3518, segment: 12 },

  // Segment 13: "The prompt is your mold."
  { word: "The", startFrame: 3548, endFrame: 3562, segment: 13 },
  { word: "prompt", startFrame: 3564, endFrame: 3596, segment: 13 },
  { word: "is", startFrame: 3598, endFrame: 3610, segment: 13 },
  { word: "your", startFrame: 3612, endFrame: 3634, segment: 13 },
  { word: "mold.", startFrame: 3636, endFrame: 3678, segment: 13 },

  // Segment 14: "Code is plastic."
  { word: "Code", startFrame: 3708, endFrame: 3736, segment: 14 },
  { word: "is", startFrame: 3738, endFrame: 3750, segment: 14 },
  { word: "plastic.", startFrame: 3752, endFrame: 3798, segment: 14 },

  // Segment 15: "Tests lock the behavior."
  { word: "Tests", startFrame: 3828, endFrame: 3858, segment: 15 },
  { word: "lock", startFrame: 3860, endFrame: 3886, segment: 15 },
  { word: "the", startFrame: 3888, endFrame: 3900, segment: 15 },
  { word: "behavior.", startFrame: 3902, endFrame: 3952, segment: 15 },

  // Segment 16: "We've seen this before —"
  { word: "We've", startFrame: 3982, endFrame: 4010, segment: 16 },
  { word: "seen", startFrame: 4012, endFrame: 4038, segment: 16 },
  { word: "this", startFrame: 4040, endFrame: 4062, segment: 16 },
  { word: "before", startFrame: 4064, endFrame: 4096, segment: 16 },
  { word: "—", startFrame: 4098, endFrame: 4108, segment: 16 },

  // Segment 17: "we just didn't recognize it."
  { word: "we", startFrame: 4138, endFrame: 4154, segment: 17 },
  { word: "just", startFrame: 4156, endFrame: 4180, segment: 17 },
  { word: "didn't", startFrame: 4182, endFrame: 4210, segment: 17 },
  { word: "recognize", startFrame: 4212, endFrame: 4256, segment: 17 },
  { word: "it.", startFrame: 4258, endFrame: 4298, segment: 17 },
];
