// Part3Mold13SubtitleTrack constants

// Duration: ~280.73s at 30fps = 8422 frames
export const TOTAL_FRAMES = 8422;
export const FPS = 30;

// Subtitle region (bottom portion of 1080p frame)
export const BACKDROP_Y_START = 860;
export const BACKDROP_HEIGHT = 160; // 860 to 1020
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

// Word states — current=#FFF bold, recent=#FFF 90%, older=#CBD5E1 70%
export const CURRENT_COLOR = "#FFFFFF";
export const CURRENT_OPACITY = 1.0;
export const CURRENT_WEIGHT = 700;
export const CURRENT_SCALE = 1.05;

export const RECENT_COLOR = "#FFFFFF";
export const RECENT_OPACITY = 0.9;
export const RECENT_WEIGHT = 500;

export const OLDER_COLOR = "#CBD5E1";
export const OLDER_OPACITY = 0.7;
export const OLDER_WEIGHT = 400;

// Accent underline (teal, matching Part 3 mold theme)
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
export const TRACK_FADE_OUT_FRAMES = 30;
export const WINDOW_SIZE = 12;

// Subtitle start offset (after title card fades)
export const SUBTITLE_START_FRAME = 150;

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

// Embedded word timestamps for Part 3 Mold narration
// Full narration covering ~280.73 seconds of content, organized by 25 segments
// Covering the "mold" metaphor — how prompts serve as reusable specifications,
// the three parts of a prompt-driven mold, and the ratchet effect of accumulating tests.
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "A mold is a reusable specification."
  { word: "A", startFrame: 150, endFrame: 162, segment: 0 },
  { word: "mold", startFrame: 164, endFrame: 194, segment: 0 },
  { word: "is", startFrame: 196, endFrame: 208, segment: 0 },
  { word: "a", startFrame: 210, endFrame: 216, segment: 0 },
  { word: "reusable", startFrame: 218, endFrame: 258, segment: 0 },
  { word: "specification.", startFrame: 260, endFrame: 320, segment: 0 },

  // Segment 1: "In manufacturing, you design the mold once, then stamp out identical parts."
  { word: "In", startFrame: 350, endFrame: 362, segment: 1 },
  { word: "manufacturing,", startFrame: 364, endFrame: 416, segment: 1 },
  { word: "you", startFrame: 418, endFrame: 432, segment: 1 },
  { word: "design", startFrame: 434, endFrame: 466, segment: 1 },
  { word: "the", startFrame: 468, endFrame: 480, segment: 1 },
  { word: "mold", startFrame: 482, endFrame: 510, segment: 1 },
  { word: "once,", startFrame: 512, endFrame: 542, segment: 1 },
  { word: "then", startFrame: 544, endFrame: 562, segment: 1 },
  { word: "stamp", startFrame: 564, endFrame: 594, segment: 1 },
  { word: "out", startFrame: 596, endFrame: 614, segment: 1 },
  { word: "identical", startFrame: 616, endFrame: 658, segment: 1 },
  { word: "parts.", startFrame: 660, endFrame: 706, segment: 1 },

  // Segment 2: "In software, the prompt is the mold."
  { word: "In", startFrame: 736, endFrame: 748, segment: 2 },
  { word: "software,", startFrame: 750, endFrame: 792, segment: 2 },
  { word: "the", startFrame: 794, endFrame: 806, segment: 2 },
  { word: "prompt", startFrame: 808, endFrame: 842, segment: 2 },
  { word: "is", startFrame: 844, endFrame: 856, segment: 2 },
  { word: "the", startFrame: 858, endFrame: 870, segment: 2 },
  { word: "mold.", startFrame: 872, endFrame: 916, segment: 2 },

  // Segment 3: "You describe what you want, and the AI stamps out the code."
  { word: "You", startFrame: 946, endFrame: 964, segment: 3 },
  { word: "describe", startFrame: 966, endFrame: 1004, segment: 3 },
  { word: "what", startFrame: 1006, endFrame: 1026, segment: 3 },
  { word: "you", startFrame: 1028, endFrame: 1042, segment: 3 },
  { word: "want,", startFrame: 1044, endFrame: 1076, segment: 3 },
  { word: "and", startFrame: 1078, endFrame: 1092, segment: 3 },
  { word: "the", startFrame: 1094, endFrame: 1106, segment: 3 },
  { word: "AI", startFrame: 1108, endFrame: 1130, segment: 3 },
  { word: "stamps", startFrame: 1132, endFrame: 1164, segment: 3 },
  { word: "out", startFrame: 1166, endFrame: 1184, segment: 3 },
  { word: "the", startFrame: 1186, endFrame: 1198, segment: 3 },
  { word: "code.", startFrame: 1200, endFrame: 1244, segment: 3 },

  // Segment 4: "But a mold has three parts."
  { word: "But", startFrame: 1274, endFrame: 1294, segment: 4 },
  { word: "a", startFrame: 1296, endFrame: 1302, segment: 4 },
  { word: "mold", startFrame: 1304, endFrame: 1332, segment: 4 },
  { word: "has", startFrame: 1334, endFrame: 1350, segment: 4 },
  { word: "three", startFrame: 1352, endFrame: 1380, segment: 4 },
  { word: "parts.", startFrame: 1382, endFrame: 1426, segment: 4 },

  // Segment 5: "The prompt defines the shape."
  { word: "The", startFrame: 1456, endFrame: 1470, segment: 5 },
  { word: "prompt", startFrame: 1472, endFrame: 1506, segment: 5 },
  { word: "defines", startFrame: 1508, endFrame: 1544, segment: 5 },
  { word: "the", startFrame: 1546, endFrame: 1558, segment: 5 },
  { word: "shape.", startFrame: 1560, endFrame: 1604, segment: 5 },

  // Segment 6: "The tests define the tolerances."
  { word: "The", startFrame: 1634, endFrame: 1648, segment: 6 },
  { word: "tests", startFrame: 1650, endFrame: 1684, segment: 6 },
  { word: "define", startFrame: 1686, endFrame: 1720, segment: 6 },
  { word: "the", startFrame: 1722, endFrame: 1734, segment: 6 },
  { word: "tolerances.", startFrame: 1736, endFrame: 1800, segment: 6 },

  // Segment 7: "The examples define the finish."
  { word: "The", startFrame: 1830, endFrame: 1844, segment: 7 },
  { word: "examples", startFrame: 1846, endFrame: 1892, segment: 7 },
  { word: "define", startFrame: 1894, endFrame: 1928, segment: 7 },
  { word: "the", startFrame: 1930, endFrame: 1942, segment: 7 },
  { word: "finish.", startFrame: 1944, endFrame: 1990, segment: 7 },

  // Segment 8: "Together, they form a complete specification."
  { word: "Together,", startFrame: 2020, endFrame: 2068, segment: 8 },
  { word: "they", startFrame: 2070, endFrame: 2090, segment: 8 },
  { word: "form", startFrame: 2092, endFrame: 2120, segment: 8 },
  { word: "a", startFrame: 2122, endFrame: 2128, segment: 8 },
  { word: "complete", startFrame: 2130, endFrame: 2172, segment: 8 },
  { word: "specification.", startFrame: 2174, endFrame: 2240, segment: 8 },

  // Segment 9: "When the code drifts, you don't patch the output."
  { word: "When", startFrame: 2270, endFrame: 2294, segment: 9 },
  { word: "the", startFrame: 2296, endFrame: 2308, segment: 9 },
  { word: "code", startFrame: 2310, endFrame: 2340, segment: 9 },
  { word: "drifts,", startFrame: 2342, endFrame: 2382, segment: 9 },
  { word: "you", startFrame: 2384, endFrame: 2398, segment: 9 },
  { word: "don't", startFrame: 2400, endFrame: 2426, segment: 9 },
  { word: "patch", startFrame: 2428, endFrame: 2460, segment: 9 },
  { word: "the", startFrame: 2462, endFrame: 2474, segment: 9 },
  { word: "output.", startFrame: 2476, endFrame: 2524, segment: 9 },

  // Segment 10: "You fix the mold."
  { word: "You", startFrame: 2554, endFrame: 2572, segment: 10 },
  { word: "fix", startFrame: 2574, endFrame: 2600, segment: 10 },
  { word: "the", startFrame: 2602, endFrame: 2614, segment: 10 },
  { word: "mold.", startFrame: 2616, endFrame: 2660, segment: 10 },

  // Segment 11: "Re-run the generation."
  { word: "Re-run", startFrame: 2690, endFrame: 2726, segment: 11 },
  { word: "the", startFrame: 2728, endFrame: 2740, segment: 11 },
  { word: "generation.", startFrame: 2742, endFrame: 2804, segment: 11 },

  // Segment 12: "Every part comes out identical."
  { word: "Every", startFrame: 2834, endFrame: 2862, segment: 12 },
  { word: "part", startFrame: 2864, endFrame: 2892, segment: 12 },
  { word: "comes", startFrame: 2894, endFrame: 2924, segment: 12 },
  { word: "out", startFrame: 2926, endFrame: 2944, segment: 12 },
  { word: "identical.", startFrame: 2946, endFrame: 3010, segment: 12 },

  // Segment 13: "This is the ratchet effect."
  { word: "This", startFrame: 3040, endFrame: 3062, segment: 13 },
  { word: "is", startFrame: 3064, endFrame: 3076, segment: 13 },
  { word: "the", startFrame: 3078, endFrame: 3090, segment: 13 },
  { word: "ratchet", startFrame: 3092, endFrame: 3132, segment: 13 },
  { word: "effect.", startFrame: 3134, endFrame: 3182, segment: 13 },

  // Segment 14: "Each test you write is a pawl that prevents backward slippage."
  { word: "Each", startFrame: 3212, endFrame: 3236, segment: 14 },
  { word: "test", startFrame: 3238, endFrame: 3264, segment: 14 },
  { word: "you", startFrame: 3266, endFrame: 3280, segment: 14 },
  { word: "write", startFrame: 3282, endFrame: 3312, segment: 14 },
  { word: "is", startFrame: 3314, endFrame: 3326, segment: 14 },
  { word: "a", startFrame: 3328, endFrame: 3334, segment: 14 },
  { word: "pawl", startFrame: 3336, endFrame: 3368, segment: 14 },
  { word: "that", startFrame: 3370, endFrame: 3388, segment: 14 },
  { word: "prevents", startFrame: 3390, endFrame: 3430, segment: 14 },
  { word: "backward", startFrame: 3432, endFrame: 3470, segment: 14 },
  { word: "slippage.", startFrame: 3472, endFrame: 3530, segment: 14 },

  // Segment 15: "The system can only move forward."
  { word: "The", startFrame: 3560, endFrame: 3574, segment: 15 },
  { word: "system", startFrame: 3576, endFrame: 3610, segment: 15 },
  { word: "can", startFrame: 3612, endFrame: 3632, segment: 15 },
  { word: "only", startFrame: 3634, endFrame: 3660, segment: 15 },
  { word: "move", startFrame: 3662, endFrame: 3690, segment: 15 },
  { word: "forward.", startFrame: 3692, endFrame: 3744, segment: 15 },

  // Segment 16: "Quality accumulates."
  { word: "Quality", startFrame: 3774, endFrame: 3814, segment: 16 },
  { word: "accumulates.", startFrame: 3816, endFrame: 3886, segment: 16 },

  // Segment 17: "Traditional code review catches issues after the fact."
  { word: "Traditional", startFrame: 3916, endFrame: 3968, segment: 17 },
  { word: "code", startFrame: 3970, endFrame: 4000, segment: 17 },
  { word: "review", startFrame: 4002, endFrame: 4038, segment: 17 },
  { word: "catches", startFrame: 4040, endFrame: 4076, segment: 17 },
  { word: "issues", startFrame: 4078, endFrame: 4114, segment: 17 },
  { word: "after", startFrame: 4116, endFrame: 4144, segment: 17 },
  { word: "the", startFrame: 4146, endFrame: 4158, segment: 17 },
  { word: "fact.", startFrame: 4160, endFrame: 4204, segment: 17 },

  // Segment 18: "Test-driven molds catch issues before generation."
  { word: "Test-driven", startFrame: 4234, endFrame: 4290, segment: 18 },
  { word: "molds", startFrame: 4292, endFrame: 4324, segment: 18 },
  { word: "catch", startFrame: 4326, endFrame: 4356, segment: 18 },
  { word: "issues", startFrame: 4358, endFrame: 4394, segment: 18 },
  { word: "before", startFrame: 4396, endFrame: 4430, segment: 18 },
  { word: "generation.", startFrame: 4432, endFrame: 4498, segment: 18 },

  // Segment 19: "The feedback loop tightens."
  { word: "The", startFrame: 4528, endFrame: 4542, segment: 19 },
  { word: "feedback", startFrame: 4544, endFrame: 4586, segment: 19 },
  { word: "loop", startFrame: 4588, endFrame: 4616, segment: 19 },
  { word: "tightens.", startFrame: 4618, endFrame: 4672, segment: 19 },

  // Segment 20: "Each cycle, the mold gets sharper."
  { word: "Each", startFrame: 4702, endFrame: 4726, segment: 20 },
  { word: "cycle,", startFrame: 4728, endFrame: 4764, segment: 20 },
  { word: "the", startFrame: 4766, endFrame: 4778, segment: 20 },
  { word: "mold", startFrame: 4780, endFrame: 4810, segment: 20 },
  { word: "gets", startFrame: 4812, endFrame: 4838, segment: 20 },
  { word: "sharper.", startFrame: 4840, endFrame: 4898, segment: 20 },

  // Segment 21: "Defects shrink. Throughput rises."
  { word: "Defects", startFrame: 4928, endFrame: 4968, segment: 21 },
  { word: "shrink.", startFrame: 4970, endFrame: 5018, segment: 21 },
  { word: "Throughput", startFrame: 5028, endFrame: 5080, segment: 21 },
  { word: "rises.", startFrame: 5082, endFrame: 5132, segment: 21 },

  // Segment 22: "The mold becomes the product."
  { word: "The", startFrame: 5162, endFrame: 5176, segment: 22 },
  { word: "mold", startFrame: 5178, endFrame: 5208, segment: 22 },
  { word: "becomes", startFrame: 5210, endFrame: 5248, segment: 22 },
  { word: "the", startFrame: 5250, endFrame: 5262, segment: 22 },
  { word: "product.", startFrame: 5264, endFrame: 5318, segment: 22 },

  // Segment 23: "Not the code. The specification."
  { word: "Not", startFrame: 5348, endFrame: 5370, segment: 23 },
  { word: "the", startFrame: 5372, endFrame: 5384, segment: 23 },
  { word: "code.", startFrame: 5386, endFrame: 5428, segment: 23 },
  { word: "The", startFrame: 5438, endFrame: 5452, segment: 23 },
  { word: "specification.", startFrame: 5454, endFrame: 5530, segment: 23 },

  // Segment 24: "That's what you ship."
  { word: "That's", startFrame: 5560, endFrame: 5594, segment: 24 },
  { word: "what", startFrame: 5596, endFrame: 5618, segment: 24 },
  { word: "you", startFrame: 5620, endFrame: 5638, segment: 24 },
  { word: "ship.", startFrame: 5640, endFrame: 5694, segment: 24 },
];
