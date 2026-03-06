// Part5Compound11SubtitleTrack constants

// Duration: ~98.42s at 30fps = 2953 frames
export const TOTAL_FRAMES = 2953;
export const FPS = 30;

// Subtitle region (bottom portion of 1080p frame)
export const BACKDROP_Y_START = 870;
export const BACKDROP_Y_END = 1050;
export const BACKDROP_HEIGHT = 180; // 1050 - 870
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

// Word states — spec: current=#FFF 100%, previous=#FFF 50%, next=#FFF 30%
export const CURRENT_COLOR = "#FFFFFF";
export const CURRENT_WEIGHT = 600;
export const CURRENT_SCALE = 1.05;

export const PREVIOUS_COLOR = "#FFFFFF";
export const PREVIOUS_OPACITY = 0.5;
export const PREVIOUS_WEIGHT = 600;

export const UPCOMING_COLOR = "#FFFFFF";
export const UPCOMING_OPACITY = 0.3;
export const UPCOMING_WEIGHT = 600;

// Accent underline (green, matching Part 5 theme)
export const UNDERLINE_COLOR = "#22C55E";
export const UNDERLINE_OPACITY = 0.6;
export const UNDERLINE_HEIGHT = 2;

// "Recent" = spoken within last 0.5s = 15 frames
export const RECENT_WINDOW_FRAMES = 15;

// Background color
export const BG_COLOR = "#0A1628";

// Animation timing (frames)
export const WORD_APPEAR_DURATION = 6;
export const HIGHLIGHT_SCALE_UP_FRAMES = 3;
export const HIGHLIGHT_SCALE_DOWN_FRAMES = 6;
export const WORD_FADE_DURATION = 6;
export const WINDOW_SLIDE_DURATION = 10;
export const TRACK_FADE_IN_FRAMES = 15;
export const TRACK_FADE_OUT_FRAMES = 15;
export const WINDOW_SIZE = 12;

// Subtitle start frame (begins immediately for this overlay)
export const SUBTITLE_START_FRAME = 0;

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
// Full narration covering ~98.42 seconds of content, organized by segments
// Narration: "Eighty to ninety percent of software cost is maintenance. Not features.
// Not launch. Maintenance. This is the elephant in the room. Patching accumulates
// debt linearly — each patch adds residual complexity. Generation resets debt each
// cycle — fresh code, no residue. The gap compounds. Over months and years, the
// trajectories diverge dramatically. Teams that patch sink deeper. Teams that generate
// compound their advantage. Early adoption creates exponential separation. Your
// grandmother didn't need a study to figure this out. When the economics flip, you
// stop darning. You start buying new socks. We're at that moment for code."
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "Eighty to ninety percent of software cost is maintenance."
  { word: "Eighty", startFrame: 30, endFrame: 56, segment: 0 },
  { word: "to", startFrame: 58, endFrame: 68, segment: 0 },
  { word: "ninety", startFrame: 70, endFrame: 94, segment: 0 },
  { word: "percent", startFrame: 96, endFrame: 122, segment: 0 },
  { word: "of", startFrame: 124, endFrame: 132, segment: 0 },
  { word: "software", startFrame: 134, endFrame: 162, segment: 0 },
  { word: "cost", startFrame: 164, endFrame: 186, segment: 0 },
  { word: "is", startFrame: 188, endFrame: 198, segment: 0 },
  { word: "maintenance.", startFrame: 200, endFrame: 248, segment: 0 },

  // Segment 1: "Not features. Not launch. Maintenance."
  { word: "Not", startFrame: 274, endFrame: 290, segment: 1 },
  { word: "features.", startFrame: 292, endFrame: 326, segment: 1 },
  { word: "Not", startFrame: 336, endFrame: 352, segment: 1 },
  { word: "launch.", startFrame: 354, endFrame: 386, segment: 1 },
  { word: "Maintenance.", startFrame: 400, endFrame: 452, segment: 1 },

  // Segment 2: "This is the elephant in the room."
  { word: "This", startFrame: 478, endFrame: 496, segment: 2 },
  { word: "is", startFrame: 498, endFrame: 508, segment: 2 },
  { word: "the", startFrame: 510, endFrame: 520, segment: 2 },
  { word: "elephant", startFrame: 522, endFrame: 554, segment: 2 },
  { word: "in", startFrame: 556, endFrame: 566, segment: 2 },
  { word: "the", startFrame: 568, endFrame: 578, segment: 2 },
  { word: "room.", startFrame: 580, endFrame: 616, segment: 2 },

  // Segment 3: "Patching accumulates debt linearly — each patch adds residual complexity."
  { word: "Patching", startFrame: 642, endFrame: 676, segment: 3 },
  { word: "accumulates", startFrame: 678, endFrame: 722, segment: 3 },
  { word: "debt", startFrame: 724, endFrame: 748, segment: 3 },
  { word: "linearly", startFrame: 750, endFrame: 786, segment: 3 },
  { word: "—", startFrame: 788, endFrame: 798, segment: 3 },
  { word: "each", startFrame: 800, endFrame: 820, segment: 3 },
  { word: "patch", startFrame: 822, endFrame: 848, segment: 3 },
  { word: "adds", startFrame: 850, endFrame: 872, segment: 3 },
  { word: "residual", startFrame: 874, endFrame: 908, segment: 3 },
  { word: "complexity.", startFrame: 910, endFrame: 958, segment: 3 },

  // Segment 4: "Generation resets debt each cycle — fresh code, no residue."
  { word: "Generation", startFrame: 984, endFrame: 1024, segment: 4 },
  { word: "resets", startFrame: 1026, endFrame: 1052, segment: 4 },
  { word: "debt", startFrame: 1054, endFrame: 1076, segment: 4 },
  { word: "each", startFrame: 1078, endFrame: 1096, segment: 4 },
  { word: "cycle", startFrame: 1098, endFrame: 1124, segment: 4 },
  { word: "—", startFrame: 1126, endFrame: 1136, segment: 4 },
  { word: "fresh", startFrame: 1138, endFrame: 1160, segment: 4 },
  { word: "code,", startFrame: 1162, endFrame: 1186, segment: 4 },
  { word: "no", startFrame: 1188, endFrame: 1200, segment: 4 },
  { word: "residue.", startFrame: 1202, endFrame: 1242, segment: 4 },

  // Segment 5: "The gap compounds."
  { word: "The", startFrame: 1268, endFrame: 1282, segment: 5 },
  { word: "gap", startFrame: 1284, endFrame: 1306, segment: 5 },
  { word: "compounds.", startFrame: 1308, endFrame: 1350, segment: 5 },

  // Segment 6: "Over months and years, the trajectories diverge dramatically."
  { word: "Over", startFrame: 1376, endFrame: 1394, segment: 6 },
  { word: "months", startFrame: 1396, endFrame: 1422, segment: 6 },
  { word: "and", startFrame: 1424, endFrame: 1436, segment: 6 },
  { word: "years,", startFrame: 1438, endFrame: 1466, segment: 6 },
  { word: "the", startFrame: 1468, endFrame: 1478, segment: 6 },
  { word: "trajectories", startFrame: 1480, endFrame: 1528, segment: 6 },
  { word: "diverge", startFrame: 1530, endFrame: 1560, segment: 6 },
  { word: "dramatically.", startFrame: 1562, endFrame: 1614, segment: 6 },

  // Segment 7: "Teams that patch sink deeper."
  { word: "Teams", startFrame: 1640, endFrame: 1664, segment: 7 },
  { word: "that", startFrame: 1666, endFrame: 1682, segment: 7 },
  { word: "patch", startFrame: 1684, endFrame: 1708, segment: 7 },
  { word: "sink", startFrame: 1710, endFrame: 1732, segment: 7 },
  { word: "deeper.", startFrame: 1734, endFrame: 1770, segment: 7 },

  // Segment 8: "Teams that generate compound their advantage."
  { word: "Teams", startFrame: 1796, endFrame: 1820, segment: 8 },
  { word: "that", startFrame: 1822, endFrame: 1838, segment: 8 },
  { word: "generate", startFrame: 1840, endFrame: 1872, segment: 8 },
  { word: "compound", startFrame: 1874, endFrame: 1906, segment: 8 },
  { word: "their", startFrame: 1908, endFrame: 1926, segment: 8 },
  { word: "advantage.", startFrame: 1928, endFrame: 1974, segment: 8 },

  // Segment 9: "Early adoption creates exponential separation."
  { word: "Early", startFrame: 2000, endFrame: 2024, segment: 9 },
  { word: "adoption", startFrame: 2026, endFrame: 2058, segment: 9 },
  { word: "creates", startFrame: 2060, endFrame: 2086, segment: 9 },
  { word: "exponential", startFrame: 2088, endFrame: 2130, segment: 9 },
  { word: "separation.", startFrame: 2132, endFrame: 2176, segment: 9 },

  // Segment 10: "Your grandmother didn't need a study to figure this out."
  { word: "Your", startFrame: 2202, endFrame: 2218, segment: 10 },
  { word: "grandmother", startFrame: 2220, endFrame: 2258, segment: 10 },
  { word: "didn't", startFrame: 2260, endFrame: 2282, segment: 10 },
  { word: "need", startFrame: 2284, endFrame: 2302, segment: 10 },
  { word: "a", startFrame: 2304, endFrame: 2310, segment: 10 },
  { word: "study", startFrame: 2312, endFrame: 2336, segment: 10 },
  { word: "to", startFrame: 2338, endFrame: 2346, segment: 10 },
  { word: "figure", startFrame: 2348, endFrame: 2372, segment: 10 },
  { word: "this", startFrame: 2374, endFrame: 2388, segment: 10 },
  { word: "out.", startFrame: 2390, endFrame: 2418, segment: 10 },

  // Segment 11: "When the economics flip, you stop darning."
  { word: "When", startFrame: 2444, endFrame: 2460, segment: 11 },
  { word: "the", startFrame: 2462, endFrame: 2472, segment: 11 },
  { word: "economics", startFrame: 2474, endFrame: 2510, segment: 11 },
  { word: "flip,", startFrame: 2512, endFrame: 2534, segment: 11 },
  { word: "you", startFrame: 2536, endFrame: 2548, segment: 11 },
  { word: "stop", startFrame: 2550, endFrame: 2568, segment: 11 },
  { word: "darning.", startFrame: 2570, endFrame: 2604, segment: 11 },

  // Segment 12: "You start buying new socks."
  { word: "You", startFrame: 2624, endFrame: 2638, segment: 12 },
  { word: "start", startFrame: 2640, endFrame: 2658, segment: 12 },
  { word: "buying", startFrame: 2660, endFrame: 2682, segment: 12 },
  { word: "new", startFrame: 2684, endFrame: 2698, segment: 12 },
  { word: "socks.", startFrame: 2700, endFrame: 2730, segment: 12 },

  // Segment 13: "We're at that moment for code."
  { word: "We're", startFrame: 2756, endFrame: 2774, segment: 13 },
  { word: "at", startFrame: 2776, endFrame: 2786, segment: 13 },
  { word: "that", startFrame: 2788, endFrame: 2802, segment: 13 },
  { word: "moment", startFrame: 2804, endFrame: 2828, segment: 13 },
  { word: "for", startFrame: 2830, endFrame: 2842, segment: 13 },
  { word: "code.", startFrame: 2844, endFrame: 2880, segment: 13 },
];
