// Closing08SubtitleTrack constants

// Duration: ~21.07s at 30fps = 632 frames
export const TOTAL_FRAMES = 632;
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

// Accent underline (amber, matching closing theme)
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

// Fade out before CTA — starts at (end-60) frames, ends at (end-15)
export const FADE_OUT_START_BEFORE_END = 60; // 2s before end
export const FADE_OUT_END_BEFORE_END = 15; // 0.5s before end

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

// Embedded word timestamps for Closing narration
// Full narration: "The economics have flipped. Patching is the old way —
// expensive, fragile, compounding. Design your mold — prompt, tests,
// grounding — and let generation do the rest. Stop darning. Start molding."
// Narration runs ~0:00.5 to ~0:17s. CTA segment (0:17-0:21) has no narration.
// Subtitle track fades out starting at frame 572 (TOTAL_FRAMES - 60).
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "The economics have flipped." (~0.5s–3.9s)
  { word: "The", startFrame: 15, endFrame: 27, segment: 0 },
  { word: "economics", startFrame: 29, endFrame: 53, segment: 0 },
  { word: "have", startFrame: 55, endFrame: 67, segment: 0 },
  { word: "flipped.", startFrame: 69, endFrame: 99, segment: 0 },

  // Segment 1: "Patching is the old way — expensive, fragile, compounding." (~4.3s–11.4s)
  { word: "Patching", startFrame: 120, endFrame: 144, segment: 1 },
  { word: "is", startFrame: 146, endFrame: 154, segment: 1 },
  { word: "the", startFrame: 156, endFrame: 164, segment: 1 },
  { word: "old", startFrame: 166, endFrame: 178, segment: 1 },
  { word: "way", startFrame: 180, endFrame: 194, segment: 1 },
  { word: "—", startFrame: 196, endFrame: 202, segment: 1 },
  { word: "expensive,", startFrame: 204, endFrame: 230, segment: 1 },
  { word: "fragile,", startFrame: 232, endFrame: 256, segment: 1 },
  { word: "compounding.", startFrame: 258, endFrame: 296, segment: 1 },

  // Segment 2: "Design your mold — prompt, tests, grounding —" (~10.2s–13.6s)
  { word: "Design", startFrame: 306, endFrame: 326, segment: 2 },
  { word: "your", startFrame: 328, endFrame: 338, segment: 2 },
  { word: "mold", startFrame: 340, endFrame: 354, segment: 2 },
  { word: "—", startFrame: 356, endFrame: 362, segment: 2 },
  { word: "prompt,", startFrame: 364, endFrame: 382, segment: 2 },
  { word: "tests,", startFrame: 384, endFrame: 400, segment: 2 },
  { word: "grounding", startFrame: 402, endFrame: 424, segment: 2 },
  { word: "—", startFrame: 426, endFrame: 432, segment: 2 },

  // Segment 3: "and let generation do the rest." (~14.4s–16.0s)
  { word: "and", startFrame: 434, endFrame: 442, segment: 3 },
  { word: "let", startFrame: 444, endFrame: 454, segment: 3 },
  { word: "generation", startFrame: 456, endFrame: 480, segment: 3 },
  { word: "do", startFrame: 482, endFrame: 490, segment: 3 },
  { word: "the", startFrame: 492, endFrame: 500, segment: 3 },
  { word: "rest.", startFrame: 502, endFrame: 522, segment: 3 },

  // Segment 4: "Stop darning." (~17.6s–18.4s)
  // Note: these frames are close to the fade-out zone but still visible
  { word: "Stop", startFrame: 528, endFrame: 542, segment: 4 },
  { word: "darning.", startFrame: 544, endFrame: 564, segment: 4 },

  // Segment 5: "Start molding." (~18.8s–19.6s)
  // Overlaps with fade-out zone — words visible but fading
  { word: "Start", startFrame: 568, endFrame: 582, segment: 5 },
  { word: "molding.", startFrame: 584, endFrame: 604, segment: 5 },
];
