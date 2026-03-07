// Part1Economics14SubtitleTrack constants

// Duration: ~382.25s at 30fps = 11468 frames
export const TOTAL_FRAMES = 11468;
export const FPS = 30;

// Subtitle starts after title card (frame 150), fades out at end
export const SUBTITLE_START_FRAME = 150;

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
export const CURRENT_SCALE = 1.05;
export const CURRENT_WEIGHT = 700;

export const RECENT_COLOR = "#FFFFFF";
export const RECENT_OPACITY = 0.9;
export const RECENT_WEIGHT = 500;

export const OLDER_COLOR = "#CBD5E1";
export const OLDER_OPACITY = 0.7;
export const OLDER_WEIGHT = 400;

// How many frames back a word is still "recent" (0.5s at 30fps)
export const RECENT_WINDOW_FRAMES = 15;

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

// Embedded word timestamps for Part 1 Economics narration
// Full narration covering ~382 seconds of content, organized by segments.
// Narration text: "Software development has always been about economics. Every line
// of code represents an investment — time, talent, and infrastructure. For decades,
// the cost curve has been predictable: more features means more developers, more
// time, more money. But something is changing. AI code generation is bending that
// curve. The crossover point — where AI-assisted development becomes cheaper than
// traditional methods — is approaching faster than anyone predicted. This isn't
// about replacing developers. It's about amplifying their output. One developer
// with AI assistance can now produce what previously took a team of five. The
// economics are shifting. Prompt-driven development captures this shift. Instead
// of writing code directly, you write specifications. Instead of debugging line
// by line, you iterate on prompts. The feedback loop tightens. Costs compress.
// But there's a catch. Cheaper code isn't better code. Without discipline, AI
// generates technical debt at unprecedented speed. The economics only work if
// quality keeps pace with velocity. That's the fundamental trade-off. Speed
// versus quality. Cost versus correctness. Volume versus value. The winners
// in this new landscape will be those who master both — who use AI to move
// fast while maintaining the engineering rigor that keeps systems reliable."
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "Software development has always been about economics."
  { word: "Software", startFrame: 30, endFrame: 60, segment: 0 },
  { word: "development", startFrame: 62, endFrame: 98, segment: 0 },
  { word: "has", startFrame: 100, endFrame: 112, segment: 0 },
  { word: "always", startFrame: 114, endFrame: 140, segment: 0 },
  { word: "been", startFrame: 142, endFrame: 160, segment: 0 },
  { word: "about", startFrame: 162, endFrame: 184, segment: 0 },
  { word: "economics.", startFrame: 186, endFrame: 232, segment: 0 },

  // Segment 1: "Every line of code represents an investment — time, talent, and infrastructure."
  { word: "Every", startFrame: 262, endFrame: 286, segment: 1 },
  { word: "line", startFrame: 288, endFrame: 310, segment: 1 },
  { word: "of", startFrame: 312, endFrame: 320, segment: 1 },
  { word: "code", startFrame: 322, endFrame: 348, segment: 1 },
  { word: "represents", startFrame: 350, endFrame: 392, segment: 1 },
  { word: "an", startFrame: 394, endFrame: 406, segment: 1 },
  { word: "investment", startFrame: 408, endFrame: 452, segment: 1 },
  { word: "—", startFrame: 454, endFrame: 466, segment: 1 },
  { word: "time,", startFrame: 468, endFrame: 494, segment: 1 },
  { word: "talent,", startFrame: 496, endFrame: 528, segment: 1 },
  { word: "and", startFrame: 530, endFrame: 544, segment: 1 },
  { word: "infrastructure.", startFrame: 546, endFrame: 610, segment: 1 },

  // Segment 2: "For decades, the cost curve has been predictable: more features means more developers, more time, more money."
  { word: "For", startFrame: 640, endFrame: 656, segment: 2 },
  { word: "decades,", startFrame: 658, endFrame: 698, segment: 2 },
  { word: "the", startFrame: 700, endFrame: 712, segment: 2 },
  { word: "cost", startFrame: 714, endFrame: 740, segment: 2 },
  { word: "curve", startFrame: 742, endFrame: 770, segment: 2 },
  { word: "has", startFrame: 772, endFrame: 786, segment: 2 },
  { word: "been", startFrame: 788, endFrame: 806, segment: 2 },
  { word: "predictable:", startFrame: 808, endFrame: 860, segment: 2 },
  { word: "more", startFrame: 870, endFrame: 892, segment: 2 },
  { word: "features", startFrame: 894, endFrame: 930, segment: 2 },
  { word: "means", startFrame: 932, endFrame: 958, segment: 2 },
  { word: "more", startFrame: 960, endFrame: 980, segment: 2 },
  { word: "developers,", startFrame: 982, endFrame: 1032, segment: 2 },
  { word: "more", startFrame: 1034, endFrame: 1054, segment: 2 },
  { word: "time,", startFrame: 1056, endFrame: 1082, segment: 2 },
  { word: "more", startFrame: 1084, endFrame: 1104, segment: 2 },
  { word: "money.", startFrame: 1106, endFrame: 1148, segment: 2 },

  // Segment 3: "But something is changing."
  { word: "But", startFrame: 1178, endFrame: 1198, segment: 3 },
  { word: "something", startFrame: 1200, endFrame: 1238, segment: 3 },
  { word: "is", startFrame: 1240, endFrame: 1252, segment: 3 },
  { word: "changing.", startFrame: 1254, endFrame: 1300, segment: 3 },

  // Segment 4: "AI code generation is bending that curve."
  { word: "AI", startFrame: 1330, endFrame: 1350, segment: 4 },
  { word: "code", startFrame: 1352, endFrame: 1376, segment: 4 },
  { word: "generation", startFrame: 1378, endFrame: 1420, segment: 4 },
  { word: "is", startFrame: 1422, endFrame: 1434, segment: 4 },
  { word: "bending", startFrame: 1436, endFrame: 1468, segment: 4 },
  { word: "that", startFrame: 1470, endFrame: 1490, segment: 4 },
  { word: "curve.", startFrame: 1492, endFrame: 1536, segment: 4 },

  // Segment 5: "The crossover point — where AI-assisted development becomes cheaper than traditional methods — is approaching faster than anyone predicted."
  { word: "The", startFrame: 1566, endFrame: 1580, segment: 5 },
  { word: "crossover", startFrame: 1582, endFrame: 1620, segment: 5 },
  { word: "point", startFrame: 1622, endFrame: 1650, segment: 5 },
  { word: "—", startFrame: 1652, endFrame: 1664, segment: 5 },
  { word: "where", startFrame: 1666, endFrame: 1690, segment: 5 },
  { word: "AI-assisted", startFrame: 1692, endFrame: 1740, segment: 5 },
  { word: "development", startFrame: 1742, endFrame: 1786, segment: 5 },
  { word: "becomes", startFrame: 1788, endFrame: 1818, segment: 5 },
  { word: "cheaper", startFrame: 1820, endFrame: 1854, segment: 5 },
  { word: "than", startFrame: 1856, endFrame: 1874, segment: 5 },
  { word: "traditional", startFrame: 1876, endFrame: 1920, segment: 5 },
  { word: "methods", startFrame: 1922, endFrame: 1958, segment: 5 },
  { word: "—", startFrame: 1960, endFrame: 1972, segment: 5 },
  { word: "is", startFrame: 1974, endFrame: 1986, segment: 5 },
  { word: "approaching", startFrame: 1988, endFrame: 2036, segment: 5 },
  { word: "faster", startFrame: 2038, endFrame: 2068, segment: 5 },
  { word: "than", startFrame: 2070, endFrame: 2088, segment: 5 },
  { word: "anyone", startFrame: 2090, endFrame: 2120, segment: 5 },
  { word: "predicted.", startFrame: 2122, endFrame: 2174, segment: 5 },

  // Segment 6: "This isn't about replacing developers."
  { word: "This", startFrame: 2204, endFrame: 2224, segment: 6 },
  { word: "isn't", startFrame: 2226, endFrame: 2252, segment: 6 },
  { word: "about", startFrame: 2254, endFrame: 2278, segment: 6 },
  { word: "replacing", startFrame: 2280, endFrame: 2320, segment: 6 },
  { word: "developers.", startFrame: 2322, endFrame: 2378, segment: 6 },

  // Segment 7: "It's about amplifying their output."
  { word: "It's", startFrame: 2408, endFrame: 2428, segment: 7 },
  { word: "about", startFrame: 2430, endFrame: 2454, segment: 7 },
  { word: "amplifying", startFrame: 2456, endFrame: 2502, segment: 7 },
  { word: "their", startFrame: 2504, endFrame: 2526, segment: 7 },
  { word: "output.", startFrame: 2528, endFrame: 2574, segment: 7 },

  // Segment 8: "One developer with AI assistance can now produce what previously took a team of five."
  { word: "One", startFrame: 2604, endFrame: 2624, segment: 8 },
  { word: "developer", startFrame: 2626, endFrame: 2668, segment: 8 },
  { word: "with", startFrame: 2670, endFrame: 2690, segment: 8 },
  { word: "AI", startFrame: 2692, endFrame: 2710, segment: 8 },
  { word: "assistance", startFrame: 2712, endFrame: 2756, segment: 8 },
  { word: "can", startFrame: 2758, endFrame: 2776, segment: 8 },
  { word: "now", startFrame: 2778, endFrame: 2798, segment: 8 },
  { word: "produce", startFrame: 2800, endFrame: 2836, segment: 8 },
  { word: "what", startFrame: 2838, endFrame: 2858, segment: 8 },
  { word: "previously", startFrame: 2860, endFrame: 2904, segment: 8 },
  { word: "took", startFrame: 2906, endFrame: 2930, segment: 8 },
  { word: "a", startFrame: 2932, endFrame: 2940, segment: 8 },
  { word: "team", startFrame: 2942, endFrame: 2966, segment: 8 },
  { word: "of", startFrame: 2968, endFrame: 2978, segment: 8 },
  { word: "five.", startFrame: 2980, endFrame: 3024, segment: 8 },

  // Segment 9: "The economics are shifting."
  { word: "The", startFrame: 3054, endFrame: 3068, segment: 9 },
  { word: "economics", startFrame: 3070, endFrame: 3114, segment: 9 },
  { word: "are", startFrame: 3116, endFrame: 3132, segment: 9 },
  { word: "shifting.", startFrame: 3134, endFrame: 3180, segment: 9 },

  // Segment 10: "Prompt-driven development captures this shift."
  { word: "Prompt-driven", startFrame: 3210, endFrame: 3264, segment: 10 },
  { word: "development", startFrame: 3266, endFrame: 3310, segment: 10 },
  { word: "captures", startFrame: 3312, endFrame: 3350, segment: 10 },
  { word: "this", startFrame: 3352, endFrame: 3372, segment: 10 },
  { word: "shift.", startFrame: 3374, endFrame: 3416, segment: 10 },

  // Segment 11: "Instead of writing code directly, you write specifications."
  { word: "Instead", startFrame: 3446, endFrame: 3478, segment: 11 },
  { word: "of", startFrame: 3480, endFrame: 3490, segment: 11 },
  { word: "writing", startFrame: 3492, endFrame: 3524, segment: 11 },
  { word: "code", startFrame: 3526, endFrame: 3550, segment: 11 },
  { word: "directly,", startFrame: 3552, endFrame: 3594, segment: 11 },
  { word: "you", startFrame: 3596, endFrame: 3614, segment: 11 },
  { word: "write", startFrame: 3616, endFrame: 3642, segment: 11 },
  { word: "specifications.", startFrame: 3644, endFrame: 3712, segment: 11 },

  // Segment 12: "Instead of debugging line by line, you iterate on prompts."
  { word: "Instead", startFrame: 3742, endFrame: 3774, segment: 12 },
  { word: "of", startFrame: 3776, endFrame: 3786, segment: 12 },
  { word: "debugging", startFrame: 3788, endFrame: 3830, segment: 12 },
  { word: "line", startFrame: 3832, endFrame: 3856, segment: 12 },
  { word: "by", startFrame: 3858, endFrame: 3872, segment: 12 },
  { word: "line,", startFrame: 3874, endFrame: 3902, segment: 12 },
  { word: "you", startFrame: 3904, endFrame: 3920, segment: 12 },
  { word: "iterate", startFrame: 3922, endFrame: 3958, segment: 12 },
  { word: "on", startFrame: 3960, endFrame: 3974, segment: 12 },
  { word: "prompts.", startFrame: 3976, endFrame: 4024, segment: 12 },

  // Segment 13: "The feedback loop tightens."
  { word: "The", startFrame: 4054, endFrame: 4068, segment: 13 },
  { word: "feedback", startFrame: 4070, endFrame: 4108, segment: 13 },
  { word: "loop", startFrame: 4110, endFrame: 4136, segment: 13 },
  { word: "tightens.", startFrame: 4138, endFrame: 4186, segment: 13 },

  // Segment 14: "Costs compress."
  { word: "Costs", startFrame: 4216, endFrame: 4244, segment: 14 },
  { word: "compress.", startFrame: 4246, endFrame: 4296, segment: 14 },

  // Segment 15: "But there's a catch."
  { word: "But", startFrame: 4326, endFrame: 4346, segment: 15 },
  { word: "there's", startFrame: 4348, endFrame: 4378, segment: 15 },
  { word: "a", startFrame: 4380, endFrame: 4388, segment: 15 },
  { word: "catch.", startFrame: 4390, endFrame: 4434, segment: 15 },

  // Segment 16: "Cheaper code isn't better code."
  { word: "Cheaper", startFrame: 4464, endFrame: 4498, segment: 16 },
  { word: "code", startFrame: 4500, endFrame: 4524, segment: 16 },
  { word: "isn't", startFrame: 4526, endFrame: 4554, segment: 16 },
  { word: "better", startFrame: 4556, endFrame: 4584, segment: 16 },
  { word: "code.", startFrame: 4586, endFrame: 4626, segment: 16 },

  // Segment 17: "Without discipline, AI generates technical debt at unprecedented speed."
  { word: "Without", startFrame: 4656, endFrame: 4690, segment: 17 },
  { word: "discipline,", startFrame: 4692, endFrame: 4740, segment: 17 },
  { word: "AI", startFrame: 4742, endFrame: 4760, segment: 17 },
  { word: "generates", startFrame: 4762, endFrame: 4804, segment: 17 },
  { word: "technical", startFrame: 4806, endFrame: 4846, segment: 17 },
  { word: "debt", startFrame: 4848, endFrame: 4876, segment: 17 },
  { word: "at", startFrame: 4878, endFrame: 4890, segment: 17 },
  { word: "unprecedented", startFrame: 4892, endFrame: 4950, segment: 17 },
  { word: "speed.", startFrame: 4952, endFrame: 4998, segment: 17 },

  // Segment 18: "The economics only work if quality keeps pace with velocity."
  { word: "The", startFrame: 5028, endFrame: 5042, segment: 18 },
  { word: "economics", startFrame: 5044, endFrame: 5088, segment: 18 },
  { word: "only", startFrame: 5090, endFrame: 5112, segment: 18 },
  { word: "work", startFrame: 5114, endFrame: 5138, segment: 18 },
  { word: "if", startFrame: 5140, endFrame: 5152, segment: 18 },
  { word: "quality", startFrame: 5154, endFrame: 5190, segment: 18 },
  { word: "keeps", startFrame: 5192, endFrame: 5218, segment: 18 },
  { word: "pace", startFrame: 5220, endFrame: 5246, segment: 18 },
  { word: "with", startFrame: 5248, endFrame: 5268, segment: 18 },
  { word: "velocity.", startFrame: 5270, endFrame: 5322, segment: 18 },

  // Segment 19: "That's the fundamental trade-off."
  { word: "That's", startFrame: 5352, endFrame: 5380, segment: 19 },
  { word: "the", startFrame: 5382, endFrame: 5394, segment: 19 },
  { word: "fundamental", startFrame: 5396, endFrame: 5446, segment: 19 },
  { word: "trade-off.", startFrame: 5448, endFrame: 5502, segment: 19 },

  // Segment 20: "Speed versus quality."
  { word: "Speed", startFrame: 5532, endFrame: 5560, segment: 20 },
  { word: "versus", startFrame: 5562, endFrame: 5592, segment: 20 },
  { word: "quality.", startFrame: 5594, endFrame: 5640, segment: 20 },

  // Segment 21: "Cost versus correctness."
  { word: "Cost", startFrame: 5670, endFrame: 5698, segment: 21 },
  { word: "versus", startFrame: 5700, endFrame: 5730, segment: 21 },
  { word: "correctness.", startFrame: 5732, endFrame: 5790, segment: 21 },

  // Segment 22: "Volume versus value."
  { word: "Volume", startFrame: 5820, endFrame: 5852, segment: 22 },
  { word: "versus", startFrame: 5854, endFrame: 5884, segment: 22 },
  { word: "value.", startFrame: 5886, endFrame: 5932, segment: 22 },

  // Segment 23: "The winners in this new landscape will be those who master both"
  { word: "The", startFrame: 5962, endFrame: 5976, segment: 23 },
  { word: "winners", startFrame: 5978, endFrame: 6016, segment: 23 },
  { word: "in", startFrame: 6018, endFrame: 6030, segment: 23 },
  { word: "this", startFrame: 6032, endFrame: 6052, segment: 23 },
  { word: "new", startFrame: 6054, endFrame: 6076, segment: 23 },
  { word: "landscape", startFrame: 6078, endFrame: 6122, segment: 23 },
  { word: "will", startFrame: 6124, endFrame: 6144, segment: 23 },
  { word: "be", startFrame: 6146, endFrame: 6160, segment: 23 },
  { word: "those", startFrame: 6162, endFrame: 6188, segment: 23 },
  { word: "who", startFrame: 6190, endFrame: 6208, segment: 23 },
  { word: "master", startFrame: 6210, endFrame: 6244, segment: 23 },
  { word: "both", startFrame: 6246, endFrame: 6274, segment: 23 },

  // Segment 24: "— who use AI to move fast while maintaining the engineering rigor that keeps systems reliable."
  { word: "—", startFrame: 6290, endFrame: 6302, segment: 24 },
  { word: "who", startFrame: 6304, endFrame: 6322, segment: 24 },
  { word: "use", startFrame: 6324, endFrame: 6346, segment: 24 },
  { word: "AI", startFrame: 6348, endFrame: 6368, segment: 24 },
  { word: "to", startFrame: 6370, endFrame: 6382, segment: 24 },
  { word: "move", startFrame: 6384, endFrame: 6408, segment: 24 },
  { word: "fast", startFrame: 6410, endFrame: 6438, segment: 24 },
  { word: "while", startFrame: 6440, endFrame: 6464, segment: 24 },
  { word: "maintaining", startFrame: 6466, endFrame: 6516, segment: 24 },
  { word: "the", startFrame: 6518, endFrame: 6530, segment: 24 },
  { word: "engineering", startFrame: 6532, endFrame: 6580, segment: 24 },
  { word: "rigor", startFrame: 6582, endFrame: 6614, segment: 24 },
  { word: "that", startFrame: 6616, endFrame: 6636, segment: 24 },
  { word: "keeps", startFrame: 6638, endFrame: 6664, segment: 24 },
  { word: "systems", startFrame: 6666, endFrame: 6702, segment: 24 },
  { word: "reliable.", startFrame: 6704, endFrame: 6760, segment: 24 },
];
