// Part4Precision10SubtitleTrack constants

// Duration: ~96.91s at 30fps = 2907 frames
export const TOTAL_FRAMES = 2907;
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

// Accent underline (amber, matching Part 4 theme)
export const UNDERLINE_COLOR = "#F59E0B";
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

// Embedded word timestamps for Part 4 Precision narration
// Full narration covering ~96.91 seconds of content, organized by segments
// "Precision has a cost. More detailed prompts mean slower generation.
// More comprehensive tests mean longer feedback cycles. This is the trade-off.
// There's a sweet spot between vagueness and over-specification. Too little
// precision — AI hallucinates. Too much — you're writing the code yourself.
// The U-curve has a minimum. Adjust precision based on context. Greenfield
// project? Lighter prompts, explore fast. Legacy system with strict contracts?
// Heavy test walls, precise prompts. The spectrum is a tool, not a rule."
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "Precision has a cost."
  { word: "Precision", startFrame: 30, endFrame: 60, segment: 0 },
  { word: "has", startFrame: 62, endFrame: 74, segment: 0 },
  { word: "a", startFrame: 76, endFrame: 82, segment: 0 },
  { word: "cost.", startFrame: 84, endFrame: 114, segment: 0 },

  // Segment 1: "More detailed prompts mean slower generation."
  { word: "More", startFrame: 144, endFrame: 162, segment: 1 },
  { word: "detailed", startFrame: 164, endFrame: 196, segment: 1 },
  { word: "prompts", startFrame: 198, endFrame: 228, segment: 1 },
  { word: "mean", startFrame: 230, endFrame: 250, segment: 1 },
  { word: "slower", startFrame: 252, endFrame: 278, segment: 1 },
  { word: "generation.", startFrame: 280, endFrame: 326, segment: 1 },

  // Segment 2: "More comprehensive tests mean longer feedback cycles."
  { word: "More", startFrame: 356, endFrame: 374, segment: 2 },
  { word: "comprehensive", startFrame: 376, endFrame: 424, segment: 2 },
  { word: "tests", startFrame: 426, endFrame: 454, segment: 2 },
  { word: "mean", startFrame: 456, endFrame: 476, segment: 2 },
  { word: "longer", startFrame: 478, endFrame: 504, segment: 2 },
  { word: "feedback", startFrame: 506, endFrame: 542, segment: 2 },
  { word: "cycles.", startFrame: 544, endFrame: 586, segment: 2 },

  // Segment 3: "This is the trade-off."
  { word: "This", startFrame: 616, endFrame: 636, segment: 3 },
  { word: "is", startFrame: 638, endFrame: 650, segment: 3 },
  { word: "the", startFrame: 652, endFrame: 664, segment: 3 },
  { word: "trade-off.", startFrame: 666, endFrame: 714, segment: 3 },

  // Segment 4: "There's a sweet spot between vagueness and over-specification."
  { word: "There's", startFrame: 744, endFrame: 770, segment: 4 },
  { word: "a", startFrame: 772, endFrame: 778, segment: 4 },
  { word: "sweet", startFrame: 780, endFrame: 806, segment: 4 },
  { word: "spot", startFrame: 808, endFrame: 832, segment: 4 },
  { word: "between", startFrame: 834, endFrame: 862, segment: 4 },
  { word: "vagueness", startFrame: 864, endFrame: 906, segment: 4 },
  { word: "and", startFrame: 908, endFrame: 920, segment: 4 },
  { word: "over-specification.", startFrame: 922, endFrame: 990, segment: 4 },

  // Segment 5: "Too little precision — AI hallucinates."
  { word: "Too", startFrame: 1020, endFrame: 1038, segment: 5 },
  { word: "little", startFrame: 1040, endFrame: 1064, segment: 5 },
  { word: "precision", startFrame: 1066, endFrame: 1104, segment: 5 },
  { word: "—", startFrame: 1106, endFrame: 1116, segment: 5 },
  { word: "AI", startFrame: 1118, endFrame: 1138, segment: 5 },
  { word: "hallucinates.", startFrame: 1140, endFrame: 1198, segment: 5 },

  // Segment 6: "Too much — you're writing the code yourself."
  { word: "Too", startFrame: 1228, endFrame: 1246, segment: 6 },
  { word: "much", startFrame: 1248, endFrame: 1270, segment: 6 },
  { word: "—", startFrame: 1272, endFrame: 1282, segment: 6 },
  { word: "you're", startFrame: 1284, endFrame: 1308, segment: 6 },
  { word: "writing", startFrame: 1310, endFrame: 1340, segment: 6 },
  { word: "the", startFrame: 1342, endFrame: 1354, segment: 6 },
  { word: "code", startFrame: 1356, endFrame: 1380, segment: 6 },
  { word: "yourself.", startFrame: 1382, endFrame: 1426, segment: 6 },

  // Segment 7: "The U-curve has a minimum."
  { word: "The", startFrame: 1456, endFrame: 1470, segment: 7 },
  { word: "U-curve", startFrame: 1472, endFrame: 1506, segment: 7 },
  { word: "has", startFrame: 1508, endFrame: 1522, segment: 7 },
  { word: "a", startFrame: 1524, endFrame: 1530, segment: 7 },
  { word: "minimum.", startFrame: 1532, endFrame: 1578, segment: 7 },

  // Segment 8: "Adjust precision based on context."
  { word: "Adjust", startFrame: 1608, endFrame: 1640, segment: 8 },
  { word: "precision", startFrame: 1642, endFrame: 1680, segment: 8 },
  { word: "based", startFrame: 1682, endFrame: 1706, segment: 8 },
  { word: "on", startFrame: 1708, endFrame: 1720, segment: 8 },
  { word: "context.", startFrame: 1722, endFrame: 1766, segment: 8 },

  // Segment 9: "Greenfield project? Lighter prompts, explore fast."
  { word: "Greenfield", startFrame: 1796, endFrame: 1840, segment: 9 },
  { word: "project?", startFrame: 1842, endFrame: 1878, segment: 9 },
  { word: "Lighter", startFrame: 1888, endFrame: 1918, segment: 9 },
  { word: "prompts,", startFrame: 1920, endFrame: 1954, segment: 9 },
  { word: "explore", startFrame: 1956, endFrame: 1986, segment: 9 },
  { word: "fast.", startFrame: 1988, endFrame: 2024, segment: 9 },

  // Segment 10: "Legacy system with strict contracts?"
  { word: "Legacy", startFrame: 2054, endFrame: 2088, segment: 10 },
  { word: "system", startFrame: 2090, endFrame: 2118, segment: 10 },
  { word: "with", startFrame: 2120, endFrame: 2138, segment: 10 },
  { word: "strict", startFrame: 2140, endFrame: 2170, segment: 10 },
  { word: "contracts?", startFrame: 2172, endFrame: 2220, segment: 10 },

  // Segment 11: "Heavy test walls, precise prompts."
  { word: "Heavy", startFrame: 2250, endFrame: 2278, segment: 11 },
  { word: "test", startFrame: 2280, endFrame: 2304, segment: 11 },
  { word: "walls,", startFrame: 2306, endFrame: 2340, segment: 11 },
  { word: "precise", startFrame: 2342, endFrame: 2374, segment: 11 },
  { word: "prompts.", startFrame: 2376, endFrame: 2420, segment: 11 },

  // Segment 12: "The spectrum is a tool, not a rule."
  { word: "The", startFrame: 2450, endFrame: 2464, segment: 12 },
  { word: "spectrum", startFrame: 2466, endFrame: 2502, segment: 12 },
  { word: "is", startFrame: 2504, endFrame: 2516, segment: 12 },
  { word: "a", startFrame: 2518, endFrame: 2524, segment: 12 },
  { word: "tool,", startFrame: 2526, endFrame: 2558, segment: 12 },
  { word: "not", startFrame: 2560, endFrame: 2578, segment: 12 },
  { word: "a", startFrame: 2580, endFrame: 2586, segment: 12 },
  { word: "rule.", startFrame: 2588, endFrame: 2630, segment: 12 },
];
