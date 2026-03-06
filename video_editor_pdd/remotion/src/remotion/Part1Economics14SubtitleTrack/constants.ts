// Part1Economics14SubtitleTrack constants

// Duration: ~382s at 30fps = 11,468 frames
export const TOTAL_FRAMES = 11468;
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

// Embedded word timestamps for Part 1 Economics narration
// Full narration covering ~382 seconds of content, organized by segment
export const WORD_DATA: WordEntry[] = [
  // Segment 0: Opening — "The economics of AI-assisted coding have shifted dramatically."
  { word: "The", startFrame: 150, endFrame: 160, segment: 0 },
  { word: "economics", startFrame: 162, endFrame: 178, segment: 0 },
  { word: "of", startFrame: 180, endFrame: 186, segment: 0 },
  { word: "AI-assisted", startFrame: 188, endFrame: 210, segment: 0 },
  { word: "coding", startFrame: 212, endFrame: 228, segment: 0 },
  { word: "have", startFrame: 230, endFrame: 240, segment: 0 },
  { word: "shifted", startFrame: 242, endFrame: 258, segment: 0 },
  { word: "dramatically.", startFrame: 260, endFrame: 286, segment: 0 },

  // Segment 1: "GitHub reports that developers using Copilot accept nearly 30% of suggestions."
  { word: "GitHub", startFrame: 310, endFrame: 328, segment: 1 },
  { word: "reports", startFrame: 330, endFrame: 346, segment: 1 },
  { word: "that", startFrame: 348, endFrame: 356, segment: 1 },
  { word: "developers", startFrame: 358, endFrame: 380, segment: 1 },
  { word: "using", startFrame: 382, endFrame: 394, segment: 1 },
  { word: "Copilot", startFrame: 396, endFrame: 418, segment: 1 },
  { word: "accept", startFrame: 420, endFrame: 436, segment: 1 },
  { word: "nearly", startFrame: 438, endFrame: 452, segment: 1 },
  { word: "30%", startFrame: 454, endFrame: 470, segment: 1 },
  { word: "of", startFrame: 472, endFrame: 478, segment: 1 },
  { word: "suggestions.", startFrame: 480, endFrame: 510, segment: 1 },

  // Segment 2: "That means code is being generated at an unprecedented rate."
  { word: "That", startFrame: 540, endFrame: 552, segment: 2 },
  { word: "means", startFrame: 554, endFrame: 568, segment: 2 },
  { word: "code", startFrame: 570, endFrame: 582, segment: 2 },
  { word: "is", startFrame: 584, endFrame: 590, segment: 2 },
  { word: "being", startFrame: 592, endFrame: 604, segment: 2 },
  { word: "generated", startFrame: 606, endFrame: 628, segment: 2 },
  { word: "at", startFrame: 630, endFrame: 636, segment: 2 },
  { word: "an", startFrame: 638, endFrame: 644, segment: 2 },
  { word: "unprecedented", startFrame: 646, endFrame: 680, segment: 2 },
  { word: "rate.", startFrame: 682, endFrame: 700, segment: 2 },

  // Segment 3: "Uplevel found that AI-assisted engineers write 26% more code per week."
  { word: "Uplevel", startFrame: 730, endFrame: 752, segment: 3 },
  { word: "found", startFrame: 754, endFrame: 768, segment: 3 },
  { word: "that", startFrame: 770, endFrame: 778, segment: 3 },
  { word: "AI-assisted", startFrame: 780, endFrame: 808, segment: 3 },
  { word: "engineers", startFrame: 810, endFrame: 834, segment: 3 },
  { word: "write", startFrame: 836, endFrame: 850, segment: 3 },
  { word: "26%", startFrame: 852, endFrame: 870, segment: 3 },
  { word: "more", startFrame: 872, endFrame: 886, segment: 3 },
  { word: "code", startFrame: 888, endFrame: 902, segment: 3 },
  { word: "per", startFrame: 904, endFrame: 914, segment: 3 },
  { word: "week.", startFrame: 916, endFrame: 938, segment: 3 },

  // Segment 4: "But here's the uncomfortable truth nobody wants to talk about."
  { word: "But", startFrame: 968, endFrame: 978, segment: 4 },
  { word: "here's", startFrame: 980, endFrame: 996, segment: 4 },
  { word: "the", startFrame: 998, endFrame: 1006, segment: 4 },
  { word: "uncomfortable", startFrame: 1008, endFrame: 1046, segment: 4 },
  { word: "truth", startFrame: 1048, endFrame: 1066, segment: 4 },
  { word: "nobody", startFrame: 1068, endFrame: 1088, segment: 4 },
  { word: "wants", startFrame: 1090, endFrame: 1106, segment: 4 },
  { word: "to", startFrame: 1108, endFrame: 1114, segment: 4 },
  { word: "talk", startFrame: 1116, endFrame: 1130, segment: 4 },
  { word: "about.", startFrame: 1132, endFrame: 1152, segment: 4 },

  // Segment 5: "GitClear's analysis of 150 million lines of code tells a different story."
  { word: "GitClear's", startFrame: 1182, endFrame: 1208, segment: 5 },
  { word: "analysis", startFrame: 1210, endFrame: 1234, segment: 5 },
  { word: "of", startFrame: 1236, endFrame: 1242, segment: 5 },
  { word: "150", startFrame: 1244, endFrame: 1262, segment: 5 },
  { word: "million", startFrame: 1264, endFrame: 1282, segment: 5 },
  { word: "lines", startFrame: 1284, endFrame: 1300, segment: 5 },
  { word: "of", startFrame: 1302, endFrame: 1308, segment: 5 },
  { word: "code", startFrame: 1310, endFrame: 1324, segment: 5 },
  { word: "tells", startFrame: 1326, endFrame: 1342, segment: 5 },
  { word: "a", startFrame: 1344, endFrame: 1348, segment: 5 },
  { word: "different", startFrame: 1350, endFrame: 1374, segment: 5 },
  { word: "story.", startFrame: 1376, endFrame: 1400, segment: 5 },

  // Segment 6: "Code churn — the percentage of lines modified within two weeks — has doubled."
  { word: "Code", startFrame: 1430, endFrame: 1444, segment: 6 },
  { word: "churn", startFrame: 1446, endFrame: 1464, segment: 6 },
  { word: "—", startFrame: 1466, endFrame: 1474, segment: 6 },
  { word: "the", startFrame: 1476, endFrame: 1484, segment: 6 },
  { word: "percentage", startFrame: 1486, endFrame: 1516, segment: 6 },
  { word: "of", startFrame: 1518, endFrame: 1524, segment: 6 },
  { word: "lines", startFrame: 1526, endFrame: 1542, segment: 6 },
  { word: "modified", startFrame: 1544, endFrame: 1568, segment: 6 },
  { word: "within", startFrame: 1570, endFrame: 1588, segment: 6 },
  { word: "two", startFrame: 1590, endFrame: 1602, segment: 6 },
  { word: "weeks", startFrame: 1604, endFrame: 1620, segment: 6 },
  { word: "—", startFrame: 1622, endFrame: 1630, segment: 6 },
  { word: "has", startFrame: 1632, endFrame: 1642, segment: 6 },
  { word: "doubled.", startFrame: 1644, endFrame: 1672, segment: 6 },

  // Segment 7: "More code is being written, rewritten, and thrown away than ever before."
  { word: "More", startFrame: 1702, endFrame: 1716, segment: 7 },
  { word: "code", startFrame: 1718, endFrame: 1732, segment: 7 },
  { word: "is", startFrame: 1734, endFrame: 1740, segment: 7 },
  { word: "being", startFrame: 1742, endFrame: 1756, segment: 7 },
  { word: "written,", startFrame: 1758, endFrame: 1778, segment: 7 },
  { word: "rewritten,", startFrame: 1780, endFrame: 1806, segment: 7 },
  { word: "and", startFrame: 1808, endFrame: 1816, segment: 7 },
  { word: "thrown", startFrame: 1818, endFrame: 1836, segment: 7 },
  { word: "away", startFrame: 1838, endFrame: 1854, segment: 7 },
  { word: "than", startFrame: 1856, endFrame: 1868, segment: 7 },
  { word: "ever", startFrame: 1870, endFrame: 1886, segment: 7 },
  { word: "before.", startFrame: 1888, endFrame: 1916, segment: 7 },

  // Segment 8: "The cost crossover point is approaching fast."
  { word: "The", startFrame: 1946, endFrame: 1956, segment: 8 },
  { word: "cost", startFrame: 1958, endFrame: 1974, segment: 8 },
  { word: "crossover", startFrame: 1976, endFrame: 2004, segment: 8 },
  { word: "point", startFrame: 2006, endFrame: 2022, segment: 8 },
  { word: "is", startFrame: 2024, endFrame: 2030, segment: 8 },
  { word: "approaching", startFrame: 2032, endFrame: 2062, segment: 8 },
  { word: "fast.", startFrame: 2064, endFrame: 2088, segment: 8 },

  // Segment 9: "When maintaining AI-generated code costs more than writing it from scratch,"
  { word: "When", startFrame: 2118, endFrame: 2130, segment: 9 },
  { word: "maintaining", startFrame: 2132, endFrame: 2166, segment: 9 },
  { word: "AI-generated", startFrame: 2168, endFrame: 2202, segment: 9 },
  { word: "code", startFrame: 2204, endFrame: 2218, segment: 9 },
  { word: "costs", startFrame: 2220, endFrame: 2238, segment: 9 },
  { word: "more", startFrame: 2240, endFrame: 2254, segment: 9 },
  { word: "than", startFrame: 2256, endFrame: 2268, segment: 9 },
  { word: "writing", startFrame: 2270, endFrame: 2290, segment: 9 },
  { word: "it", startFrame: 2292, endFrame: 2298, segment: 9 },
  { word: "from", startFrame: 2300, endFrame: 2314, segment: 9 },
  { word: "scratch,", startFrame: 2316, endFrame: 2346, segment: 9 },

  // Segment 10: "the productivity gains vanish entirely."
  { word: "the", startFrame: 2370, endFrame: 2380, segment: 10 },
  { word: "productivity", startFrame: 2382, endFrame: 2418, segment: 10 },
  { word: "gains", startFrame: 2420, endFrame: 2438, segment: 10 },
  { word: "vanish", startFrame: 2440, endFrame: 2462, segment: 10 },
  { word: "entirely.", startFrame: 2464, endFrame: 2498, segment: 10 },

  // Segment 11: "Context degradation is the silent killer."
  { word: "Context", startFrame: 2528, endFrame: 2552, segment: 11 },
  { word: "degradation", startFrame: 2554, endFrame: 2590, segment: 11 },
  { word: "is", startFrame: 2592, endFrame: 2598, segment: 11 },
  { word: "the", startFrame: 2600, endFrame: 2608, segment: 11 },
  { word: "silent", startFrame: 2610, endFrame: 2630, segment: 11 },
  { word: "killer.", startFrame: 2632, endFrame: 2660, segment: 11 },

  // Segment 12: "Every time the AI loses context, it regenerates code that already exists."
  { word: "Every", startFrame: 2690, endFrame: 2706, segment: 12 },
  { word: "time", startFrame: 2708, endFrame: 2722, segment: 12 },
  { word: "the", startFrame: 2724, endFrame: 2732, segment: 12 },
  { word: "AI", startFrame: 2734, endFrame: 2746, segment: 12 },
  { word: "loses", startFrame: 2748, endFrame: 2766, segment: 12 },
  { word: "context,", startFrame: 2768, endFrame: 2792, segment: 12 },
  { word: "it", startFrame: 2794, endFrame: 2800, segment: 12 },
  { word: "regenerates", startFrame: 2802, endFrame: 2838, segment: 12 },
  { word: "code", startFrame: 2840, endFrame: 2854, segment: 12 },
  { word: "that", startFrame: 2856, endFrame: 2866, segment: 12 },
  { word: "already", startFrame: 2868, endFrame: 2890, segment: 12 },
  { word: "exists.", startFrame: 2892, endFrame: 2920, segment: 12 },

  // Segment 13: "Slightly different. Slightly wrong. Each regeneration drifts further from intent."
  { word: "Slightly", startFrame: 2950, endFrame: 2974, segment: 13 },
  { word: "different.", startFrame: 2976, endFrame: 3006, segment: 13 },
  { word: "Slightly", startFrame: 3020, endFrame: 3044, segment: 13 },
  { word: "wrong.", startFrame: 3046, endFrame: 3076, segment: 13 },
  { word: "Each", startFrame: 3100, endFrame: 3116, segment: 13 },
  { word: "regeneration", startFrame: 3118, endFrame: 3160, segment: 13 },
  { word: "drifts", startFrame: 3162, endFrame: 3184, segment: 13 },
  { word: "further", startFrame: 3186, endFrame: 3208, segment: 13 },
  { word: "from", startFrame: 3210, endFrame: 3224, segment: 13 },
  { word: "intent.", startFrame: 3226, endFrame: 3258, segment: 13 },

  // Segment 14: "The perception gap is real."
  { word: "The", startFrame: 3288, endFrame: 3298, segment: 14 },
  { word: "perception", startFrame: 3300, endFrame: 3332, segment: 14 },
  { word: "gap", startFrame: 3334, endFrame: 3350, segment: 14 },
  { word: "is", startFrame: 3352, endFrame: 3358, segment: 14 },
  { word: "real.", startFrame: 3360, endFrame: 3384, segment: 14 },

  // Segment 15: "Developers feel 30% more productive. Code quality metrics tell the opposite story."
  { word: "Developers", startFrame: 3414, endFrame: 3446, segment: 15 },
  { word: "feel", startFrame: 3448, endFrame: 3464, segment: 15 },
  { word: "30%", startFrame: 3466, endFrame: 3484, segment: 15 },
  { word: "more", startFrame: 3486, endFrame: 3500, segment: 15 },
  { word: "productive.", startFrame: 3502, endFrame: 3538, segment: 15 },
  { word: "Code", startFrame: 3560, endFrame: 3576, segment: 15 },
  { word: "quality", startFrame: 3578, endFrame: 3600, segment: 15 },
  { word: "metrics", startFrame: 3602, endFrame: 3628, segment: 15 },
  { word: "tell", startFrame: 3630, endFrame: 3646, segment: 15 },
  { word: "the", startFrame: 3648, endFrame: 3656, segment: 15 },
  { word: "opposite", startFrame: 3658, endFrame: 3686, segment: 15 },
  { word: "story.", startFrame: 3688, endFrame: 3716, segment: 15 },

  // Segment 16: "Bug rates climb. Code duplication explodes. Maintenance burden grows."
  { word: "Bug", startFrame: 3746, endFrame: 3762, segment: 16 },
  { word: "rates", startFrame: 3764, endFrame: 3782, segment: 16 },
  { word: "climb.", startFrame: 3784, endFrame: 3810, segment: 16 },
  { word: "Code", startFrame: 3830, endFrame: 3846, segment: 16 },
  { word: "duplication", startFrame: 3848, endFrame: 3884, segment: 16 },
  { word: "explodes.", startFrame: 3886, endFrame: 3920, segment: 16 },
  { word: "Maintenance", startFrame: 3940, endFrame: 3978, segment: 16 },
  { word: "burden", startFrame: 3980, endFrame: 4002, segment: 16 },
  { word: "grows.", startFrame: 4004, endFrame: 4036, segment: 16 },

  // Segment 17: "The regeneration tax compounds with every iteration."
  { word: "The", startFrame: 4066, endFrame: 4076, segment: 17 },
  { word: "regeneration", startFrame: 4078, endFrame: 4120, segment: 17 },
  { word: "tax", startFrame: 4122, endFrame: 4140, segment: 17 },
  { word: "compounds", startFrame: 4142, endFrame: 4174, segment: 17 },
  { word: "with", startFrame: 4176, endFrame: 4190, segment: 17 },
  { word: "every", startFrame: 4192, endFrame: 4212, segment: 17 },
  { word: "iteration.", startFrame: 4214, endFrame: 4250, segment: 17 },

  // Segment 18: "When the AI regenerates a function, it doesn't just rewrite it."
  { word: "When", startFrame: 4280, endFrame: 4292, segment: 18 },
  { word: "the", startFrame: 4294, endFrame: 4302, segment: 18 },
  { word: "AI", startFrame: 4304, endFrame: 4316, segment: 18 },
  { word: "regenerates", startFrame: 4318, endFrame: 4354, segment: 18 },
  { word: "a", startFrame: 4356, endFrame: 4360, segment: 18 },
  { word: "function,", startFrame: 4362, endFrame: 4390, segment: 18 },
  { word: "it", startFrame: 4392, endFrame: 4398, segment: 18 },
  { word: "doesn't", startFrame: 4400, endFrame: 4420, segment: 18 },
  { word: "just", startFrame: 4422, endFrame: 4438, segment: 18 },
  { word: "rewrite", startFrame: 4440, endFrame: 4464, segment: 18 },
  { word: "it.", startFrame: 4466, endFrame: 4480, segment: 18 },

  // Segment 19: "It creates a new version that may subtly break callers."
  { word: "It", startFrame: 4510, endFrame: 4518, segment: 19 },
  { word: "creates", startFrame: 4520, endFrame: 4542, segment: 19 },
  { word: "a", startFrame: 4544, endFrame: 4548, segment: 19 },
  { word: "new", startFrame: 4550, endFrame: 4564, segment: 19 },
  { word: "version", startFrame: 4566, endFrame: 4590, segment: 19 },
  { word: "that", startFrame: 4592, endFrame: 4604, segment: 19 },
  { word: "may", startFrame: 4606, endFrame: 4620, segment: 19 },
  { word: "subtly", startFrame: 4622, endFrame: 4646, segment: 19 },
  { word: "break", startFrame: 4648, endFrame: 4666, segment: 19 },
  { word: "callers.", startFrame: 4668, endFrame: 4700, segment: 19 },

  // Segment 20: "The cost crossover is not hypothetical. It's measurable. It's happening now."
  { word: "The", startFrame: 4730, endFrame: 4740, segment: 20 },
  { word: "cost", startFrame: 4742, endFrame: 4758, segment: 20 },
  { word: "crossover", startFrame: 4760, endFrame: 4790, segment: 20 },
  { word: "is", startFrame: 4792, endFrame: 4798, segment: 20 },
  { word: "not", startFrame: 4800, endFrame: 4814, segment: 20 },
  { word: "hypothetical.", startFrame: 4816, endFrame: 4860, segment: 20 },
  { word: "It's", startFrame: 4880, endFrame: 4894, segment: 20 },
  { word: "measurable.", startFrame: 4896, endFrame: 4936, segment: 20 },
  { word: "It's", startFrame: 4956, endFrame: 4970, segment: 20 },
  { word: "happening", startFrame: 4972, endFrame: 5002, segment: 20 },
  { word: "now.", startFrame: 5004, endFrame: 5032, segment: 20 },

  // Segment 21: "Teams report initial velocity spikes followed by grinding slowdowns."
  { word: "Teams", startFrame: 5062, endFrame: 5080, segment: 21 },
  { word: "report", startFrame: 5082, endFrame: 5102, segment: 21 },
  { word: "initial", startFrame: 5104, endFrame: 5128, segment: 21 },
  { word: "velocity", startFrame: 5130, endFrame: 5158, segment: 21 },
  { word: "spikes", startFrame: 5160, endFrame: 5184, segment: 21 },
  { word: "followed", startFrame: 5186, endFrame: 5212, segment: 21 },
  { word: "by", startFrame: 5214, endFrame: 5222, segment: 21 },
  { word: "grinding", startFrame: 5224, endFrame: 5252, segment: 21 },
  { word: "slowdowns.", startFrame: 5254, endFrame: 5294, segment: 21 },

  // Segment 22: "Sprint one is magical. Sprint five is a nightmare."
  { word: "Sprint", startFrame: 5324, endFrame: 5344, segment: 22 },
  { word: "one", startFrame: 5346, endFrame: 5360, segment: 22 },
  { word: "is", startFrame: 5362, endFrame: 5368, segment: 22 },
  { word: "magical.", startFrame: 5370, endFrame: 5402, segment: 22 },
  { word: "Sprint", startFrame: 5422, endFrame: 5442, segment: 22 },
  { word: "five", startFrame: 5444, endFrame: 5460, segment: 22 },
  { word: "is", startFrame: 5462, endFrame: 5468, segment: 22 },
  { word: "a", startFrame: 5470, endFrame: 5474, segment: 22 },
  { word: "nightmare.", startFrame: 5476, endFrame: 5516, segment: 22 },

  // Segment 23: "The codebase becomes a patchwork of AI-generated fragments,"
  { word: "The", startFrame: 5546, endFrame: 5556, segment: 23 },
  { word: "codebase", startFrame: 5558, endFrame: 5586, segment: 23 },
  { word: "becomes", startFrame: 5588, endFrame: 5610, segment: 23 },
  { word: "a", startFrame: 5612, endFrame: 5616, segment: 23 },
  { word: "patchwork", startFrame: 5618, endFrame: 5650, segment: 23 },
  { word: "of", startFrame: 5652, endFrame: 5658, segment: 23 },
  { word: "AI-generated", startFrame: 5660, endFrame: 5700, segment: 23 },
  { word: "fragments,", startFrame: 5702, endFrame: 5736, segment: 23 },

  // Segment 24: "each slightly inconsistent with the others."
  { word: "each", startFrame: 5760, endFrame: 5776, segment: 24 },
  { word: "slightly", startFrame: 5778, endFrame: 5802, segment: 24 },
  { word: "inconsistent", startFrame: 5804, endFrame: 5846, segment: 24 },
  { word: "with", startFrame: 5848, endFrame: 5862, segment: 24 },
  { word: "the", startFrame: 5864, endFrame: 5872, segment: 24 },
  { word: "others.", startFrame: 5874, endFrame: 5906, segment: 24 },

  // Segment 25: "No single piece is broken. The whole is incoherent."
  { word: "No", startFrame: 5936, endFrame: 5948, segment: 25 },
  { word: "single", startFrame: 5950, endFrame: 5970, segment: 25 },
  { word: "piece", startFrame: 5972, endFrame: 5990, segment: 25 },
  { word: "is", startFrame: 5992, endFrame: 5998, segment: 25 },
  { word: "broken.", startFrame: 6000, endFrame: 6030, segment: 25 },
  { word: "The", startFrame: 6050, endFrame: 6060, segment: 25 },
  { word: "whole", startFrame: 6062, endFrame: 6082, segment: 25 },
  { word: "is", startFrame: 6084, endFrame: 6090, segment: 25 },
  { word: "incoherent.", startFrame: 6092, endFrame: 6136, segment: 25 },

  // Segment 26: "This is the fundamental paradox of AI-assisted development."
  { word: "This", startFrame: 6166, endFrame: 6178, segment: 26 },
  { word: "is", startFrame: 6180, endFrame: 6186, segment: 26 },
  { word: "the", startFrame: 6188, endFrame: 6196, segment: 26 },
  { word: "fundamental", startFrame: 6198, endFrame: 6236, segment: 26 },
  { word: "paradox", startFrame: 6238, endFrame: 6266, segment: 26 },
  { word: "of", startFrame: 6268, endFrame: 6274, segment: 26 },
  { word: "AI-assisted", startFrame: 6276, endFrame: 6312, segment: 26 },
  { word: "development.", startFrame: 6314, endFrame: 6354, segment: 26 },

  // Segment 27: "The tool that makes writing code trivially cheap"
  { word: "The", startFrame: 6384, endFrame: 6394, segment: 27 },
  { word: "tool", startFrame: 6396, endFrame: 6412, segment: 27 },
  { word: "that", startFrame: 6414, endFrame: 6424, segment: 27 },
  { word: "makes", startFrame: 6426, endFrame: 6444, segment: 27 },
  { word: "writing", startFrame: 6446, endFrame: 6468, segment: 27 },
  { word: "code", startFrame: 6470, endFrame: 6486, segment: 27 },
  { word: "trivially", startFrame: 6488, endFrame: 6520, segment: 27 },
  { word: "cheap", startFrame: 6522, endFrame: 6544, segment: 27 },

  // Segment 28: "also makes maintaining it exponentially expensive."
  { word: "also", startFrame: 6568, endFrame: 6584, segment: 28 },
  { word: "makes", startFrame: 6586, endFrame: 6604, segment: 28 },
  { word: "maintaining", startFrame: 6606, endFrame: 6646, segment: 28 },
  { word: "it", startFrame: 6648, endFrame: 6654, segment: 28 },
  { word: "exponentially", startFrame: 6656, endFrame: 6704, segment: 28 },
  { word: "expensive.", startFrame: 6706, endFrame: 6748, segment: 28 },

  // Segment 29: "Unless you change the equation."
  { word: "Unless", startFrame: 6778, endFrame: 6800, segment: 29 },
  { word: "you", startFrame: 6802, endFrame: 6814, segment: 29 },
  { word: "change", startFrame: 6816, endFrame: 6838, segment: 29 },
  { word: "the", startFrame: 6840, endFrame: 6850, segment: 29 },
  { word: "equation.", startFrame: 6852, endFrame: 6892, segment: 29 },
];
