// ── Canvas ──────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 270;
export const CYCLE_FRAMES = 54; // ~1.8s per cycle

// ── Colors ──────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;
export const WALL_COLOR = '#4A90D9';
export const WALL_LABEL_COLOR = '#CDD6F4';
export const FLASH_COLOR = '#EF4444';
export const COUNTER_LABEL_COLOR = '#64748B';
export const COUNTER_NUMBER_COLOR = '#4A90D9';
export const TERMINAL_BG = '#1E1E2E';
export const TERMINAL_CHECK_COLOR = '#A6E3A1';
export const MOLD_BASE_COLOR = '#2A3A5C';
export const LIQUID_COLOR = '#F59E0B';

// ── Grid ────────────────────────────────────────────────────────
export const GRID_SPACING = 60;

// ── Mold geometry ───────────────────────────────────────────────
export const MOLD_CENTER_X = 700;
export const MOLD_CENTER_Y = 480;
export const MOLD_WIDTH = 600;
export const MOLD_HEIGHT = 500;

// ── Wall cycles ─────────────────────────────────────────────────
export interface WallCycle {
  label: string;
  side: 'left' | 'right';
  cycle: number;
}

export const WALL_CYCLES: WallCycle[] = [
  { label: 'handles empty array', side: 'left', cycle: 1 },
  { label: 'timeout at 5s', side: 'right', cycle: 2 },
  { label: 'rejects SQL injection', side: 'left', cycle: 3 },
  { label: 'UTF-8 BOM stripped', side: 'right', cycle: 4 },
];

// Pre-existing walls (displayed from frame 0)
export const BASE_WALLS: { label: string; x: number; y: number; width: number; height: number }[] = [
  { label: 'non-null input', x: 430, y: 280, width: 12, height: 180 },
  { label: 'positive integer', x: 430, y: 480, width: 200, height: 12 },
  { label: 'max length 255', x: 960, y: 280, width: 12, height: 180 },
  { label: 'valid JSON', x: 960, y: 480, width: 200, height: 12 },
  { label: 'auth required', x: 550, y: 700, width: 300, height: 12 },
];

// New wall positions for each cycle (placed to progressively constrain the mold)
export const NEW_WALL_POSITIONS: { x: number; y: number; width: number; height: number }[] = [
  { x: 490, y: 320, width: 12, height: 140 },   // left wall
  { x: 900, y: 320, width: 12, height: 140 },   // right wall
  { x: 530, y: 370, width: 12, height: 120 },   // left wall (inner)
  { x: 860, y: 370, width: 12, height: 120 },   // right wall (inner)
];

// ── Terminal test lines ─────────────────────────────────────────
export const TEST_LINES: string[] = [
  '✓ test_non_null_input',
  '✓ test_positive_int',
  '✓ test_max_length',
  '✓ test_valid_json',
  '✓ test_auth_required',
  '✓ test_null_handling',
  '✓ test_empty_string',
  '✓ test_timeout_5s',
  '✓ test_sql_injection',
  '✓ test_utf8_bom',
  '✓ test_max_payload',
];

// ── Counter ─────────────────────────────────────────────────────
export const COUNTER_X = 1780;
export const COUNTER_Y = 60;
export const START_WALL_COUNT = 5;

// ── Terminal ────────────────────────────────────────────────────
export const TERMINAL_X = 1500;
export const TERMINAL_Y = 880;
export const TERMINAL_WIDTH = 370;
export const TERMINAL_HEIGHT = 150;

// ── Animation timing ────────────────────────────────────────────
export const FLASH_DURATION = 8;
export const WALL_SLIDE_DURATION = 20;
export const RECONFORM_START = 28;
export const COUNTER_PULSE_DURATION = 10;
