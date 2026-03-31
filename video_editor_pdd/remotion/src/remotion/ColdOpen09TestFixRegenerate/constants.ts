// ── Color palette ──
export const BG_COLOR = '#0A1628';
export const ACCENT_BLUE = '#3B82F6';
export const ACCENT_GREEN = '#22C55E';
export const ACCENT_RED = '#EF4444';
export const ACCENT_AMBER = '#F59E0B';
export const TEXT_PRIMARY = '#FFFFFF';
export const TEXT_SECONDARY = '#94A3B8';
export const GLOW_BLUE = 'rgba(59, 130, 246, 0.35)';
export const GLOW_GREEN = 'rgba(34, 197, 94, 0.35)';
export const GLOW_RED = 'rgba(239, 68, 68, 0.35)';
export const PANEL_BG = 'rgba(15, 23, 42, 0.85)';
export const DIVIDER_COLOR = 'rgba(148, 163, 184, 0.75)';

// ── Dimensions ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 300; // 10 seconds

// ── Cycle icon geometry ──
export const CYCLE_CENTER_X = WIDTH / 2;
export const CYCLE_CENTER_Y = HEIGHT / 2 - 20;
export const CYCLE_RADIUS = 200;
export const ICON_SIZE = 80;

// ── Phase timing (frames) ──
export const PHASE_INTRO_START = 0;
export const PHASE_INTRO_END = 30;
export const PHASE_TEST_START = 30;
export const PHASE_TEST_END = 100;
export const PHASE_FIX_START = 100;
export const PHASE_FIX_END = 180;
export const PHASE_REGEN_START = 180;
export const PHASE_REGEN_END = 250;
export const PHASE_LOOP_START = 250;
export const PHASE_LOOP_END = 300;

// ── Phase definitions ──
export interface CyclePhase {
  label: string;
  color: string;
  glowColor: string;
  angleDeg: number; // position on the cycle (0 = top)
  frameStart: number;
  frameEnd: number;
}

export const PHASES: CyclePhase[] = [
  {
    label: 'TEST',
    color: ACCENT_BLUE,
    glowColor: GLOW_BLUE,
    angleDeg: 270, // left
    frameStart: PHASE_TEST_START,
    frameEnd: PHASE_TEST_END,
  },
  {
    label: 'FIX',
    color: ACCENT_RED,
    glowColor: GLOW_RED,
    angleDeg: 30, // bottom-right
    frameStart: PHASE_FIX_START,
    frameEnd: PHASE_FIX_END,
  },
  {
    label: 'REGENERATE',
    color: ACCENT_GREEN,
    glowColor: GLOW_GREEN,
    angleDeg: 150, // bottom-left
    frameStart: PHASE_REGEN_START,
    frameEnd: PHASE_REGEN_END,
  },
];
