// constants.ts — Part3MoldParts16ThreeComponentsPullback

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const TOTAL_FRAMES = 270;
export const FPS = 30;

// Blueprint grid
export const GRID_SPACING = 60;
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.05;

// Mold geometry — centered on canvas
export const MOLD_CENTER_X = CANVAS_WIDTH / 2;
export const MOLD_CENTER_Y = CANVAS_HEIGHT / 2;
export const MOLD_WIDTH = 400;
export const MOLD_HEIGHT = 520;
export const MOLD_TOP = MOLD_CENTER_Y - MOLD_HEIGHT / 2;
export const MOLD_LEFT = MOLD_CENTER_X - MOLD_WIDTH / 2;

// Nozzle dimensions
export const NOZZLE_WIDTH = 80;
export const NOZZLE_HEIGHT = 70;
export const NOZZLE_TOP = MOLD_TOP - NOZZLE_HEIGHT + 10;

// Exit dimensions
export const EXIT_WIDTH = 80;
export const EXIT_HEIGHT = 50;
export const EXIT_TOP = MOLD_TOP + MOLD_HEIGHT - 10;

// Colors — component-level
export const COLOR_PROMPT = "#D9944A";    // amber — nozzle / intent
export const COLOR_GROUNDING = "#4AD9A0"; // teal — cavity / style
export const COLOR_WALLS = "#4A90D9";     // blue — walls / correctness
export const COLOR_OUTPUT = "#38BDF8";    // cyan — code / output
export const COLOR_SHELL = "#334155";     // outer mold shell
export const COLOR_DIM_TEXT = "#64748B";  // dim supporting text

// Glow opacities
export const NOZZLE_GLOW_OPACITY = 0.4;
export const WALL_GLOW_OPACITY = 0.4;
export const CAVITY_FILL_OPACITY = 0.1;

// Flow path Y coordinates (top to bottom)
export const FLOW_ENTRY_Y = NOZZLE_TOP + NOZZLE_HEIGHT / 2;
export const FLOW_NOZZLE_Y = MOLD_TOP + 20;
export const FLOW_CAVITY_Y = MOLD_CENTER_Y;
export const FLOW_WALLS_Y = MOLD_TOP + MOLD_HEIGHT - 80;
export const FLOW_EXIT_Y = EXIT_TOP + EXIT_HEIGHT;

// Pipeline stages with label positions
export const STAGES = [
  {
    component: "Prompt",
    encodes: "Intent",
    color: COLOR_PROMPT,
    labelX: MOLD_LEFT - 180,
    labelY: FLOW_NOZZLE_Y + 10,
    flowStartFrame: 30,
  },
  {
    component: "Grounding",
    encodes: "Style",
    color: COLOR_GROUNDING,
    labelX: MOLD_LEFT + MOLD_WIDTH + 40,
    labelY: FLOW_CAVITY_Y - 20,
    flowStartFrame: 60,
  },
  {
    component: "Tests",
    encodes: "Correctness",
    color: COLOR_WALLS,
    labelX: MOLD_LEFT - 200,
    labelY: FLOW_WALLS_Y - 10,
    flowStartFrame: 90,
  },
  {
    component: "Code",
    encodes: "Output",
    color: COLOR_OUTPUT,
    labelX: MOLD_LEFT + MOLD_WIDTH + 40,
    labelY: FLOW_EXIT_Y + 10,
    flowStartFrame: 120,
  },
] as const;

// Animation timing
export const MOLD_FADE_FRAMES = 20;
export const LABEL_FADE_FRAMES = 15;
export const PARTICLE_CYCLE_FRAMES = 60;
export const PARTICLE_COUNT = 22;
