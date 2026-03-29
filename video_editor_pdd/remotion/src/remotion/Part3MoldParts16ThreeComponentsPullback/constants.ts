// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;
export const GRID_SPACING = 60;

export const MOLD_SHELL_COLOR = '#334155';
export const MOLD_SHELL_STROKE = 3;

export const NOZZLE_COLOR = '#D9944A';
export const NOZZLE_GLOW_OPACITY = 0.4;

export const WALL_COLOR = '#4A90D9';
export const WALL_GLOW_OPACITY = 0.4;

export const CAVITY_COLOR = '#4AD9A0';
export const CAVITY_FILL_OPACITY = 0.1;

export const EXIT_COLOR = '#38BDF8';

export const LABEL_MUTED_COLOR = '#64748B';

// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// === Duration ===
export const TOTAL_FRAMES = 270;
export const FPS = 30;

// === Mold Geometry (centered on canvas) ===
export const MOLD_CENTER_X = CANVAS_WIDTH / 2;
export const MOLD_TOP = 160;
export const MOLD_BOTTOM = 880;
export const MOLD_WIDTH = 400;
export const MOLD_LEFT = MOLD_CENTER_X - MOLD_WIDTH / 2;
export const MOLD_RIGHT = MOLD_CENTER_X + MOLD_WIDTH / 2;

// Nozzle region
export const NOZZLE_TOP = MOLD_TOP;
export const NOZZLE_BOTTOM = MOLD_TOP + 120;
export const NOZZLE_NECK_WIDTH = 80;

// Cavity region
export const CAVITY_TOP = NOZZLE_BOTTOM;
export const CAVITY_BOTTOM = MOLD_BOTTOM - 120;

// Wall region (same height as cavity but represents the side walls)
export const WALL_THICKNESS = 30;

// Exit region
export const EXIT_TOP = CAVITY_BOTTOM;
export const EXIT_BOTTOM = MOLD_BOTTOM;
export const EXIT_NECK_WIDTH = 120;

// === Flow stages ===
export interface FlowStage {
  component: string;
  encodes: string;
  color: string;
  labelX: number;
  labelY: number;
  startFrame: number;
}

export const FLOW_STAGES: FlowStage[] = [
  {
    component: 'Prompt',
    encodes: 'Intent',
    color: NOZZLE_COLOR,
    labelX: MOLD_RIGHT + 60,
    labelY: (NOZZLE_TOP + NOZZLE_BOTTOM) / 2,
    startFrame: 30,
  },
  {
    component: 'Grounding',
    encodes: 'Style',
    color: CAVITY_COLOR,
    labelX: MOLD_RIGHT + 60,
    labelY: (CAVITY_TOP + CAVITY_BOTTOM) / 2,
    startFrame: 60,
  },
  {
    component: 'Tests',
    encodes: 'Correctness',
    color: WALL_COLOR,
    labelX: MOLD_RIGHT + 60,
    labelY: CAVITY_BOTTOM - 40,
    startFrame: 90,
  },
  {
    component: 'Code',
    encodes: 'Output',
    color: EXIT_COLOR,
    labelX: MOLD_RIGHT + 60,
    labelY: (EXIT_TOP + EXIT_BOTTOM) / 2,
    startFrame: 120,
  },
];

// === Animation Timing ===
export const MOLD_FADE_IN_FRAMES = 20;
export const LABEL_FADE_IN_FRAMES = 15;
export const FLOW_CYCLE_FRAMES = 60;
export const PARTICLE_COUNT = 20;
