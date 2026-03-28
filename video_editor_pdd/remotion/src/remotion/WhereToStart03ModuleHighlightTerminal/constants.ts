// === Colors ===
export const BG_COLOR = "#0A0F1A";
export const TERMINAL_BG = "#0D1117";
export const GREEN_ACCENT = "#5AAA6E";
export const TEXT_LIGHT = "#E2E8F0";
export const CODEBASE_DIM = "#94A3B8";
export const ARTIFACT_LABEL_COLOR = "#64748B";
export const PARTICLE_COLOR = "#5AAA6E";

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const MODULE_WIDTH = 300;
export const MODULE_HEIGHT = 200;
export const CODE_FILE_X = 380;
export const CODE_FILE_Y = 400;
export const PROMPT_FILE_X = 1100;
export const PROMPT_FILE_Y = 400;
export const TERMINAL_HEIGHT = 160;
export const TERMINAL_Y = CANVAS_HEIGHT - TERMINAL_HEIGHT;

// === Timing (frames) ===
export const TOTAL_FRAMES = 270;
export const FPS = 30;

// Module highlight
export const HIGHLIGHT_START = 0;
export const HIGHLIGHT_DURATION = 30;

// Terminal slide up
export const TERMINAL_SLIDE_START = 30;
export const TERMINAL_SLIDE_DURATION = 25;

// Command typing
export const TYPE_START = 60;
export const CHAR_DELAY = 3;
export const COMMAND_TEXT = "pdd update auth_handler.py";
export const TYPE_TOTAL_FRAMES = COMMAND_TEXT.length * CHAR_DELAY; // 78 frames

// Prompt materialization
export const MATERIALIZE_START = 120;
export const MATERIALIZE_DURATION = 60;

// Particle flow
export const PARTICLE_START = 150;
export const PARTICLE_DURATION = 60;
export const PARTICLE_COUNT = 25;

// Desaturation
export const DESAT_START = 150;
export const DESAT_DURATION = 40;

// Labels
export const LABELS_START = 210;
export const LABELS_FADE_DURATION = 20;

// === Codebase background modules ===
export const CODEBASE_MODULES = [
  { x: 120, y: 150, w: 140, h: 80, label: "main.py" },
  { x: 320, y: 120, w: 160, h: 90, label: "config.py" },
  { x: 540, y: 180, w: 130, h: 70, label: "utils.py" },
  { x: 160, y: 300, w: 150, h: 85, label: "router.py" },
  { x: 550, y: 320, w: 120, h: 75, label: "models.py" },
  { x: 750, y: 140, w: 140, h: 80, label: "db.py" },
  { x: 800, y: 300, w: 130, h: 70, label: "cache.py" },
  { x: 1300, y: 150, w: 150, h: 85, label: "logger.py" },
  { x: 1500, y: 280, w: 140, h: 80, label: "middleware.py" },
  { x: 1350, y: 350, w: 120, h: 70, label: "tests.py" },
];

// Fake code lines for module interiors
export const CODE_LINES = [
  { width: 0.8, indent: 0 },
  { width: 0.6, indent: 1 },
  { width: 0.9, indent: 1 },
  { width: 0.5, indent: 2 },
  { width: 0.7, indent: 1 },
  { width: 0.4, indent: 2 },
  { width: 0.85, indent: 0 },
  { width: 0.55, indent: 1 },
];

// Fake prompt content lines
export const PROMPT_LINES = [
  { width: 0.7, indent: 0, isHeader: true },
  { width: 0.0, indent: 0 },
  { width: 0.9, indent: 0 },
  { width: 0.6, indent: 0 },
  { width: 0.0, indent: 0 },
  { width: 0.5, indent: 0, isHeader: true },
  { width: 0.8, indent: 1 },
  { width: 0.65, indent: 1 },
];
