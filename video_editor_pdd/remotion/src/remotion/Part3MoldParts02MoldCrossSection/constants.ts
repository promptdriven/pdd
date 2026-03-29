// ── Background & Grid ──────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.08;
export const GRID_SPACING = 60;

// ── Canvas ─────────────────────────────────────────────────────────
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;
export const CENTER_X = 960;
export const CENTER_Y = 540;

// ── Mold outline ───────────────────────────────────────────────────
export const OUTER_W = 600;
export const OUTER_H = 400;
export const INNER_W = 400;
export const INNER_H = 280;
export const MOLD_STROKE_COLOR = "#334155";
export const MOLD_STROKE_WIDTH = 3;
export const MOLD_CORNER_RADIUS = 8;

// Nozzle dimensions (funnel top)
export const NOZZLE_TOP_W = 80;
export const NOZZLE_BOTTOM_W = 36;
export const NOZZLE_H = 50;

// ── Regions ────────────────────────────────────────────────────────
export const WALLS_COLOR = "#4A90D9";
export const NOZZLE_COLOR = "#D9944A";
export const CAVITY_COLOR = "#4AD9A0";

export const WALLS_GLOW_RADIUS = 12;
export const WALLS_GLOW_OPACITY = 0.3;
export const NOZZLE_GLOW_RADIUS = 12;
export const NOZZLE_GLOW_OPACITY = 0.3;
export const CAVITY_GLOW_RADIUS = 8;
export const CAVITY_GLOW_OPACITY = 0.2;

export interface RegionDef {
  id: string;
  label: string;
  color: string;
  highlightFrame: number;
  glowRadius: number;
  glowOpacity: number;
  labelPosition: "left" | "top" | "bottom";
}

export const REGIONS: RegionDef[] = [
  {
    id: "walls",
    label: "TESTS",
    color: WALLS_COLOR,
    highlightFrame: 60,
    glowRadius: WALLS_GLOW_RADIUS,
    glowOpacity: WALLS_GLOW_OPACITY,
    labelPosition: "left",
  },
  {
    id: "nozzle",
    label: "PROMPT",
    color: NOZZLE_COLOR,
    highlightFrame: 150,
    glowRadius: NOZZLE_GLOW_RADIUS,
    glowOpacity: NOZZLE_GLOW_OPACITY,
    labelPosition: "top",
  },
  {
    id: "cavity",
    label: "GROUNDING",
    color: CAVITY_COLOR,
    highlightFrame: 240,
    glowRadius: CAVITY_GLOW_RADIUS,
    glowOpacity: CAVITY_GLOW_OPACITY,
    labelPosition: "bottom",
  },
];

// ── Animation timing ───────────────────────────────────────────────
export const TOTAL_FRAMES = 420;
export const MOLD_DRAW_FRAMES = 30;
export const REGION_GLOW_FRAMES = 30;
export const LABEL_FADE_FRAMES = 15;
export const PULSE_CYCLE_FRAMES = 45;
export const PULSE_START_FRAME = 300;

// ── Typography ─────────────────────────────────────────────────────
export const LABEL_FONT_FAMILY = "Inter, sans-serif";
export const LABEL_FONT_SIZE = 18;
export const LABEL_FONT_WEIGHT = 700;
export const CONNECTOR_LINE_WIDTH = 1;
export const CONNECTOR_LINE_OPACITY = 0.4;
