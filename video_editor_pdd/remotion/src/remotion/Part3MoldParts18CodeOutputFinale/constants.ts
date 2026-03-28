// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const DURATION_FRAMES = 90;

// ── Mold Colors ──
export const NOZZLE_COLOR = "#D9944A";
export const WALLS_COLOR = "#4A90D9";
export const CAVITY_COLOR = "#4AD9A0";

// ── Mold Layout ──
export const MOLD_Y_TOP = 150;
export const MOLD_Y_BOTTOM = 500;
export const MOLD_SCALE = 0.7;

// ── Code Block ──
export const CODE_BLOCK_X = 660;
export const CODE_BLOCK_Y = 650;
export const CODE_BLOCK_WIDTH = 600;
export const CODE_BLOCK_HEIGHT = 250;
export const CODE_BG_COLOR = "#1E1E2E";
export const CODE_BORDER_COLOR = "#334155";
export const CODE_BORDER_DIMMED = "#1E293B";
export const CODE_GLOW_COLOR = "#38BDF8";
export const CODE_FONT_SIZE = 11;

// ── Arrow ──
export const ARROW_COLOR = "#334155";
export const ARROW_OPACITY = 0.2;

// ── Animation Frames ──
export const CODE_FADE_IN_END = 20;
export const CODE_GLOW_FADE_START = 20;
export const CODE_GLOW_FADE_END = 40;
export const MOLD_GLOW_START = 40;
export const MOLD_GLOW_END = 60;

// ── Code Glow Data (authoritative from structured data) ──
export const CODE_GLOW_FROM = 0.2;
export const CODE_GLOW_TO = 0.0;
export const CODE_TEXT_FROM = 1.0;
export const CODE_TEXT_TO = 0.4;
export const MOLD_GLOW_FROM = 0.4;
export const MOLD_GLOW_TO = 0.6;

// ── Sample Python Code (syntax highlighted inline) ──
export const PYTHON_CODE_LINES: Array<{
  tokens: Array<{ text: string; color: string }>;
}> = [
  {
    tokens: [
      { text: "def ", color: "#C678DD" },
      { text: "generate_parts", color: "#61AFEF" },
      { text: "(", color: "#ABB2BF" },
      { text: "mold", color: "#E06C75" },
      { text: ",", color: "#ABB2BF" },
      { text: " count", color: "#E06C75" },
      { text: "):", color: "#ABB2BF" },
    ],
  },
  {
    tokens: [
      { text: '    """', color: "#98C379" },
      { text: "Produce identical parts from the mold.", color: "#98C379" },
      { text: '"""', color: "#98C379" },
    ],
  },
  {
    tokens: [
      { text: "    parts ", color: "#ABB2BF" },
      { text: "= ", color: "#56B6C2" },
      { text: "[]", color: "#ABB2BF" },
    ],
  },
  {
    tokens: [
      { text: "    ", color: "#ABB2BF" },
      { text: "for ", color: "#C678DD" },
      { text: "_ ", color: "#ABB2BF" },
      { text: "in ", color: "#C678DD" },
      { text: "range", color: "#61AFEF" },
      { text: "(count):", color: "#ABB2BF" },
    ],
  },
  {
    tokens: [
      { text: "        part ", color: "#ABB2BF" },
      { text: "= ", color: "#56B6C2" },
      { text: "mold", color: "#E06C75" },
      { text: ".", color: "#ABB2BF" },
      { text: "inject", color: "#61AFEF" },
      { text: "()", color: "#ABB2BF" },
    ],
  },
  {
    tokens: [
      { text: "        ", color: "#ABB2BF" },
      { text: "assert ", color: "#C678DD" },
      { text: "part", color: "#E06C75" },
      { text: ".", color: "#ABB2BF" },
      { text: "is_valid", color: "#61AFEF" },
      { text: "()", color: "#ABB2BF" },
    ],
  },
  {
    tokens: [
      { text: "        parts", color: "#ABB2BF" },
      { text: ".", color: "#ABB2BF" },
      { text: "append", color: "#61AFEF" },
      { text: "(part)", color: "#ABB2BF" },
    ],
  },
  {
    tokens: [
      { text: "    ", color: "#ABB2BF" },
      { text: "return ", color: "#C678DD" },
      { text: "parts", color: "#ABB2BF" },
    ],
  },
];
