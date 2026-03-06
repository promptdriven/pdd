// Closing08SubtitleTrack constants

// Duration: ~21.07s at 30fps = 632 frames
export const TOTAL_FRAMES = 632;
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

// Accent underline (amber, matching closing theme)
export const UNDERLINE_COLOR = "#F59E0B";
export const UNDERLINE_OPACITY = 0.6;
export const UNDERLINE_HEIGHT = 2;

// Background color
export const BG_COLOR = "#0A1628";

// Animation timing (frames)
export const WORD_APPEAR_DURATION = 6;
export const HIGHLIGHT_SCALE_UP_FRAMES = 3;
export const HIGHLIGHT_SCALE_DOWN_FRAMES = 6;
export const WORD_FADE_DURATION = 6;
export const WINDOW_SLIDE_DURATION = 10;
export const TRACK_FADE_IN_FRAMES = 15;
export const WINDOW_SIZE = 12;

// Subtitle start frame (begins immediately for this overlay)
export const SUBTITLE_START_FRAME = 0;

// Fade-out timing: starts at frame (end-60), ends at frame (end-15)
// Spec: "Frame (end-60) to (end-15): Backdrop bar and all words fade out"
// At 632 total frames: fade starts at 572, ends at 617
export const FADE_OUT_START_BEFORE_END = 60;
export const FADE_OUT_END_BEFORE_END = 15;

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

// Embedded word timestamps for Closing narration (~17s of speech within 21s total)
// Narration: "The economics have flipped. Patching is the old way — expensive,
// fragile, compounding. Design your mold — prompt, tests, grounding — and let
// generation do the rest. Stop darning. Start molding."
// Segments closing_001 through closing_006. Fades out during CTA (0:17-0:21).
export const WORD_DATA: WordEntry[] = [
  // Segment 0 (closing_001): "The economics have flipped."
  { word: "The", startFrame: 15, endFrame: 28, segment: 0 },
  { word: "economics", startFrame: 30, endFrame: 58, segment: 0 },
  { word: "have", startFrame: 60, endFrame: 74, segment: 0 },
  { word: "flipped.", startFrame: 76, endFrame: 106, segment: 0 },

  // Segment 1 (closing_002): "Patching is the old way — expensive, fragile, compounding."
  { word: "Patching", startFrame: 120, endFrame: 150, segment: 1 },
  { word: "is", startFrame: 152, endFrame: 162, segment: 1 },
  { word: "the", startFrame: 164, endFrame: 172, segment: 1 },
  { word: "old", startFrame: 174, endFrame: 186, segment: 1 },
  { word: "way", startFrame: 188, endFrame: 202, segment: 1 },
  { word: "—", startFrame: 204, endFrame: 212, segment: 1 },
  { word: "expensive,", startFrame: 214, endFrame: 244, segment: 1 },
  { word: "fragile,", startFrame: 246, endFrame: 270, segment: 1 },
  { word: "compounding.", startFrame: 272, endFrame: 308, segment: 1 },

  // Segment 2 (closing_003): "Design your mold — prompt, tests, grounding —"
  { word: "Design", startFrame: 322, endFrame: 346, segment: 2 },
  { word: "your", startFrame: 348, endFrame: 360, segment: 2 },
  { word: "mold", startFrame: 362, endFrame: 380, segment: 2 },
  { word: "—", startFrame: 382, endFrame: 388, segment: 2 },
  { word: "prompt,", startFrame: 390, endFrame: 412, segment: 2 },
  { word: "tests,", startFrame: 414, endFrame: 432, segment: 2 },
  { word: "grounding", startFrame: 434, endFrame: 462, segment: 2 },
  { word: "—", startFrame: 464, endFrame: 470, segment: 2 },

  // Segment 3 (closing_004): "and let generation do the rest."
  { word: "and", startFrame: 474, endFrame: 482, segment: 3 },
  { word: "let", startFrame: 484, endFrame: 492, segment: 3 },
  { word: "generation", startFrame: 494, endFrame: 522, segment: 3 },
  { word: "do", startFrame: 524, endFrame: 530, segment: 3 },
  { word: "the", startFrame: 532, endFrame: 538, segment: 3 },
  { word: "rest.", startFrame: 540, endFrame: 558, segment: 3 },

  // Segment 4 (closing_005): "Stop darning."
  { word: "Stop", startFrame: 568, endFrame: 580, segment: 4 },
  { word: "darning.", startFrame: 582, endFrame: 604, segment: 4 },

  // Segment 5 (closing_006): "Start molding."
  { word: "Start", startFrame: 612, endFrame: 624, segment: 5 },
  { word: "molding.", startFrame: 626, endFrame: 648, segment: 5 },
];
