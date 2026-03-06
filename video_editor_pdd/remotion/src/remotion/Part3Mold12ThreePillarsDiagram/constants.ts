// Part3Mold12ThreePillarsDiagram constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Total animation
export const TOTAL_FRAMES = 300;
export const FPS = 30;

// Equation area layout
export const EQUATION_LEFT = 120;
export const EQUATION_RIGHT = 1800;
export const EQUATION_CENTER_X = (EQUATION_LEFT + EQUATION_RIGHT) / 2;

// Row Y positions
export const ROW_1_Y = 420;
export const ROW_2_Y = 620;

// Pillar dimensions
export const PILLAR_WIDTH = 200;
export const PILLAR_HEIGHT = 100;
export const PILLAR_BORDER_RADIUS = 16;
export const PILLAR_BG_OPACITY = 0.2;

// Result box dimensions
export const RESULT_WIDTH = 360;
export const RESULT_HEIGHT = 100;

// Pillar data
export const PILLARS = [
  { label: "Prompt", color: "#F59E0B", icon: "document" as const },
  { label: "Tests", color: "#22C55E", icon: "checkmark" as const },
  { label: "Grounding", color: "#A855F7", icon: "loop" as const },
] as const;

// Row 2 mapping labels
export const ROW_2_ITEMS = [
  { text: "Intent", color: "#F59E0B" },
  { text: "+", color: "#94A3B8" },
  { text: "Constraints", color: "#22C55E" },
  { text: "+", color: "#94A3B8" },
  { text: "Style", color: "#A855F7" },
  { text: "=", color: "#FFFFFF" },
  { text: "The Mold", color: "#FFFFFF" },
] as const;

// Connector colors
export const CONNECTOR_COLOR = "#94A3B8";
export const EQUALS_COLOR = "#FFFFFF";

// Typography
export const PILLAR_LABEL_SIZE = 24;
export const PILLAR_ICON_SIZE = 28;
export const CONNECTOR_FONT_SIZE = 40;
export const EQUALS_FONT_SIZE = 48;
export const RESULT_FONT_SIZE = 28;
export const ROW_2_FONT_SIZE = 20;
export const MOLD_FONT_SIZE = 24;

// Spacing - computed layout positions
// Total equation width: 3 pillars (200ea) + 2 plus signs + 1 equals + result (360)
// Gaps between elements: ~40px
export const GAP = 40;

// Animation timing (frames at 30fps)
// Pillar 1 "Prompt" slides up
export const PILLAR_1_START = 0;
export const PILLAR_1_END = 20;

// First "+" connector
export const PLUS_1_START = 15;
export const PLUS_1_END = 25;

// Pillar 2 "Tests" slides up
export const PILLAR_2_START = 20;
export const PILLAR_2_END = 40;

// Second "+" connector
export const PLUS_2_START = 35;
export const PLUS_2_END = 45;

// Pillar 3 "Grounding" slides up
export const PILLAR_3_START = 40;
export const PILLAR_3_END = 60;

// "=" sign
export const EQUALS_START = 55;
export const EQUALS_END = 70;

// "Complete Specification" result
export const RESULT_START = 65;
export const RESULT_END = 85;

// Row 2 labels (staggered)
export const ROW_2_START = 85;
export const ROW_2_STAGGER = 5;

// Connecting dashed arrows
export const ARROWS_START = 115;
export const ARROWS_END = 130;

// Pulse
export const PULSE_START = 130;
export const PULSE_MID = 138;
export const PULSE_END = 145;

// Fade out
export const FADE_OUT_START = 250;
export const FADE_OUT_END = 300;

// Slide-up distance
export const SLIDE_UP_DISTANCE = 40;

// Glow effect
export const RESULT_GLOW = "0 0 30px rgba(255, 255, 255, 0.3), 0 0 60px rgba(255, 255, 255, 0.1)";
export const MOLD_TEXT_SHADOW = "0 0 20px rgba(255, 255, 255, 0.5), 0 0 40px rgba(255, 255, 255, 0.2)";
