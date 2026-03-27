// ── Colors ──────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.05;

export const MODULE_FILL = "#1E1E2E";
export const CENTER_BORDER_COLOR = "#4A90D9";
export const SURROUNDING_BORDER_COLOR = "#334155";
export const CENTER_LABEL_COLOR = "#CDD6F4";
export const SURROUNDING_LABEL_COLOR = "#64748B";

export const GLOW_COLOR = "#4A90D9";
export const GLOW_OPACITY = 0.25;
export const GLOW_BLUR = 20;

export const ARROW_COLOR = "#334155";
export const ARROW_OPACITY = 0.5;
export const ARROW_WIDTH = 1.5;

export const BOUNDARY_COLOR = "#4A90D9";
export const BOUNDARY_OPACITY = 0.15;
export const BOUNDARY_RADIUS = 180;
export const BOUNDARY_LABEL_OPACITY = 0.4;

export const MAIN_LABEL_COLOR = "#E2E8F0";
export const SUB_LABEL_COLOR = "#94A3B8";

// ── Dimensions ──────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GRID_SPACING = 60;

export const CENTER_WIDTH = 240;
export const CENTER_HEIGHT = 120;
export const CENTER_X = 960;
export const CENTER_Y = 540;

export const SURROUND_WIDTH = 180;
export const SURROUND_HEIGHT = 80;

// ── Duration (frames) ───────────────────────────────────────────
export const TOTAL_FRAMES = 660;
export const FPS = 30;

// ── Surrounding module definitions ──────────────────────────────
export interface SurroundingModule {
  name: string;
  x: number;
  y: number;
  async: boolean;
}

const RADIUS = 280;

export const SURROUNDING_MODULES: SurroundingModule[] = [
  { name: "auth_service", x: CENTER_X, y: CENTER_Y - RADIUS, async: false },
  {
    name: "db_layer",
    x: CENTER_X + RADIUS * Math.cos(Math.PI / 6),
    y: CENTER_Y - RADIUS * Math.sin(Math.PI / 6),
    async: false,
  },
  {
    name: "api_router",
    x: CENTER_X + RADIUS * Math.cos(Math.PI / 6),
    y: CENTER_Y + RADIUS * Math.sin(Math.PI / 6),
    async: false,
  },
  { name: "cache", x: CENTER_X, y: CENTER_Y + RADIUS, async: true },
  {
    name: "logger",
    x: CENTER_X - RADIUS * Math.cos(Math.PI / 6),
    y: CENTER_Y + RADIUS * Math.sin(Math.PI / 6),
    async: true,
  },
  {
    name: "config",
    x: CENTER_X - RADIUS * Math.cos(Math.PI / 6),
    y: CENTER_Y - RADIUS * Math.sin(Math.PI / 6),
    async: false,
  },
];
