// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;

export const CENTER_MODULE_FILL = '#1E1E2E';
export const CENTER_MODULE_BORDER = '#4A90D9';
export const CENTER_MODULE_LABEL_COLOR = '#CDD6F4';

export const SURROUND_MODULE_FILL = '#1E1E2E';
export const SURROUND_MODULE_BORDER = '#334155';
export const SURROUND_MODULE_LABEL_COLOR = '#64748B';

export const ARROW_COLOR = '#334155';
export const ARROW_OPACITY = 0.5;

export const BOUNDARY_COLOR = '#4A90D9';
export const BOUNDARY_CIRCLE_OPACITY = 0.15;
export const BOUNDARY_LABEL_OPACITY = 0.4;

export const MAIN_LABEL_COLOR = '#E2E8F0';
export const SUB_LABEL_COLOR = '#94A3B8';

export const GLOW_COLOR = '#4A90D9';
export const GLOW_OPACITY = 0.25;
export const GLOW_BLUR = 20;

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GRID_SPACING = 60;

export const CENTER_MODULE_WIDTH = 240;
export const CENTER_MODULE_HEIGHT = 120;
export const CENTER_X = 960;
export const CENTER_Y = 540;

export const SURROUND_MODULE_WIDTH = 180;
export const SURROUND_MODULE_HEIGHT = 80;

export const BOUNDARY_RADIUS = 180;

// === Animation Frames ===
export const TOTAL_FRAMES = 660;

export const CENTRAL_FADE_START = 0;
export const CENTRAL_FADE_DURATION = 15;

export const SURROUND_FADE_START = 30;
export const SURROUND_FADE_INTERVAL = 10;
export const SURROUND_FADE_DURATION = 15;

export const ARROWS_START = 90;
export const ARROW_DRAW_DURATION = 20;

export const BOUNDARY_START = 150;
export const BOUNDARY_DRAW_DURATION = 30;
export const BOUNDARY_LABEL_START = 165; // 150 + 15

export const DIM_START = 210;
export const DIM_DURATION = 30;

export const MAIN_LABEL_START = 300;
export const MAIN_LABEL_DURATION = 20;

export const SUB_LABEL_START = 420;
export const SUB_LABEL_DURATION = 20;

// === Module Data ===
export interface SurroundModule {
  name: string;
  x: number;
  y: number;
  async: boolean;
}

// 6 modules arranged radially around center (960, 540) at radius ~300px
export const SURROUNDING_MODULES: SurroundModule[] = [
  { name: 'auth_service', x: 960, y: 220, async: false },       // top
  { name: 'db_layer', x: 1260, y: 340, async: false },          // top-right
  { name: 'api_router', x: 1260, y: 740, async: false },        // bottom-right
  { name: 'cache', x: 960, y: 860, async: true },               // bottom
  { name: 'logger', x: 660, y: 740, async: true },              // bottom-left
  { name: 'config', x: 660, y: 340, async: false },             // top-left
];
