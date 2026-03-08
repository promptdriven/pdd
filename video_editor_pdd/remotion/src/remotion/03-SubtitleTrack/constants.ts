// ColdOpen03SubtitleTrack constants

// Duration: ~15.68s at 30fps = 470 frames
export const TOTAL_FRAMES = 470;
export const FPS = 30;

// Subtitle region (bottom 20% of 1080p frame: y 864–1040)
export const BACKDROP_HEIGHT = 176;

// Backdrop styling
export const BACKDROP_FILL = "rgba(15, 23, 42, 0.75)";
export const BACKDROP_BLUR = 8;
export const BACKDROP_BORDER_COLOR = "rgba(59, 130, 246, 0.15)";
export const BACKDROP_FEATHER_PX = 16;
export const TRACK_FADE_OUT_FRAMES = 20;

// Text container
export const TEXT_MAX_WIDTH = 1280;
export const TEXT_PADDING_V = 24;
export const TEXT_PADDING_H = 40;

// Typography
export const FONT_FAMILY = "'Inter', sans-serif";
export const FONT_SIZE = 32;
export const WORD_SPACING = 12;
export const TEXT_SHADOW = "0 2px 8px rgba(0, 0, 0, 0.5)";

// Active word state
export const ACTIVE_COLOR = "#FFFFFF";
export const ACTIVE_WEIGHT = 600;
export const ACTIVE_SCALE = 1.05;

// Trailing word state
export const TRAIL_COLOR = "rgba(255, 255, 255, 0.6)";
export const TRAIL_WEIGHT = 500;

// Background color (dark navy for standalone preview)
export const BG_COLOR = "#0A1628";

// Animation timing (frames)
export const POP_IN_DURATION = 4; // scale 0.85→1.0, opacity 0→1
export const DIM_DURATION = 3; // active→trail transition
export const EXIT_DURATION = 6; // window overflow fade out
export const EXIT_SLIDE_PX = 20; // sliding left on exit
export const SEGMENT_CLEAR_DURATION = 10; // fade between segments
export const WINDOW_SLIDE_DURATION = 6;

// Animation scales
export const POP_IN_SCALE_START = 0.85;
export const POP_IN_SCALE_END = 1.0;

// Rolling window
export const WINDOW_SIZE = 12;

// Silence gap between narration segments
export const SILENCE_GAP_FRAMES = 9; // 0.3s at 30fps

// Word data type
export interface WordEntry {
  word: string;
  startFrame: number;
  segment: number;
}

// Embedded word timestamps for cold open narration
// "If you use Cursor, Claude Code, or Copilot — you're getting really
// good at this. Your grandmother figured out socks got cheap, and she stopped
// darning. Code just got that cheap. So why are we still patching?"
export const WORD_DATA: WordEntry[] = [
  // Segment 0: "If you use Cursor, Claude Code, or Copilot —"
  { word: "If", startFrame: 3, segment: 0 },
  { word: "you", startFrame: 9, segment: 0 },
  { word: "use", startFrame: 14, segment: 0 },
  { word: "Cursor,", startFrame: 20, segment: 0 },
  { word: "Claude", startFrame: 32, segment: 0 },
  { word: "Code,", startFrame: 40, segment: 0 },
  { word: "or", startFrame: 50, segment: 0 },
  { word: "Copilot", startFrame: 55, segment: 0 },
  { word: "—", startFrame: 68, segment: 0 },

  // Segment 1: "you're getting really good at this."
  { word: "you're", startFrame: 82, segment: 1 },
  { word: "getting", startFrame: 90, segment: 1 },
  { word: "really", startFrame: 100, segment: 1 },
  { word: "good", startFrame: 110, segment: 1 },
  { word: "at", startFrame: 118, segment: 1 },
  { word: "this.", startFrame: 123, segment: 1 },

  // Segment 2: "Your grandmother figured out socks got cheap,"
  { word: "Your", startFrame: 148, segment: 2 },
  { word: "grandmother", startFrame: 155, segment: 2 },
  { word: "figured", startFrame: 172, segment: 2 },
  { word: "out", startFrame: 184, segment: 2 },
  { word: "socks", startFrame: 192, segment: 2 },
  { word: "got", startFrame: 204, segment: 2 },
  { word: "cheap,", startFrame: 212, segment: 2 },

  // Segment 3: "and she stopped darning."
  { word: "and", startFrame: 232, segment: 3 },
  { word: "she", startFrame: 240, segment: 3 },
  { word: "stopped", startFrame: 248, segment: 3 },
  { word: "darning.", startFrame: 262, segment: 3 },

  // Segment 4: "Code just got that cheap."
  { word: "Code", startFrame: 296, segment: 4 },
  { word: "just", startFrame: 306, segment: 4 },
  { word: "got", startFrame: 316, segment: 4 },
  { word: "that", startFrame: 324, segment: 4 },
  { word: "cheap.", startFrame: 334, segment: 4 },

  // Segment 5: "So why are we still patching?"
  { word: "So", startFrame: 368, segment: 5 },
  { word: "why", startFrame: 378, segment: 5 },
  { word: "are", startFrame: 388, segment: 5 },
  { word: "we", startFrame: 396, segment: 5 },
  { word: "still", startFrame: 404, segment: 5 },
  { word: "patching?", startFrame: 418, segment: 5 },
];
