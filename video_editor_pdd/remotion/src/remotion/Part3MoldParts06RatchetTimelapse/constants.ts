// ── Colors ──
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.05;
export const WALL_COLOR = '#4A90D9';
export const FLASH_COLOR = '#EF4444';
export const LABEL_TEXT_COLOR = '#CDD6F4';
export const COUNTER_LABEL_COLOR = '#64748B';
export const COUNTER_NUMBER_COLOR = '#4A90D9';
export const TERMINAL_BG = '#1E1E2E';
export const TERMINAL_CHECK_COLOR = '#A6E3A1';
export const MOLD_BASE_COLOR = '#334155';
export const LIQUID_COLOR = '#F59E0B';

// ── Dimensions ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const GRID_SPACING = 60;
export const TOTAL_FRAMES = 270;
export const FPS = 30;
export const CYCLE_FRAMES = 54;
export const FLASH_FRAMES = 8;
export const WALL_SLIDE_FRAMES = 20;
export const RECONFORM_FRAMES = 20;
export const COUNTER_PULSE_FRAMES = 10;

// ── Mold geometry ──
export const MOLD_CENTER_X = 700;
export const MOLD_CENTER_Y = 480;
export const MOLD_WIDTH = 600;
export const MOLD_HEIGHT = 500;

// ── Wall cycles ──
export interface WallCycle {
  label: string;
  side: 'left' | 'right';
  startFrame: number;
}

export const WALL_CYCLES: WallCycle[] = [
  { label: 'handles empty array', side: 'left', startFrame: 0 },
  { label: 'timeout at 5s', side: 'right', startFrame: 54 },
  { label: 'rejects SQL injection', side: 'left', startFrame: 108 },
  { label: 'UTF-8 BOM stripped', side: 'right', startFrame: 162 },
];

// ── Pre-existing walls (the mold already has 5 walls at start) ──
export interface BaseWall {
  label: string;
  x: number;
  y: number;
  wallWidth: number;
  wallHeight: number;
  rotation: number;
}

export const BASE_WALLS: BaseWall[] = [
  { label: 'not null', x: 430, y: 350, wallWidth: 8, wallHeight: 180, rotation: 0 },
  { label: 'type: string', x: 970, y: 350, wallWidth: 8, wallHeight: 180, rotation: 0 },
  { label: 'length > 0', x: 700, y: 250, wallWidth: 280, wallHeight: 8, rotation: 0 },
  { label: 'max 255 chars', x: 700, y: 680, wallWidth: 280, wallHeight: 8, rotation: 0 },
  { label: 'no whitespace', x: 550, y: 480, wallWidth: 8, wallHeight: 120, rotation: 15 },
];

// ── New wall positions for each cycle ──
export interface NewWallPosition {
  x: number;
  y: number;
  wallWidth: number;
  wallHeight: number;
  labelOffsetX: number;
  labelOffsetY: number;
}

export const NEW_WALL_POSITIONS: NewWallPosition[] = [
  { x: 490, y: 400, wallWidth: 8, wallHeight: 140, labelOffsetX: -130, labelOffsetY: 0 },
  { x: 910, y: 420, wallWidth: 8, wallHeight: 130, labelOffsetX: 15, labelOffsetY: 0 },
  { x: 530, y: 330, wallWidth: 8, wallHeight: 150, labelOffsetX: -150, labelOffsetY: 0 },
  { x: 870, y: 370, wallWidth: 8, wallHeight: 140, labelOffsetX: 15, labelOffsetY: 0 },
];

// ── Terminal test lines ──
export const TEST_LINES: string[] = [
  '✓ test_not_null',
  '✓ test_type_string',
  '✓ test_length_check',
  '✓ test_max_chars',
  '✓ test_whitespace',
  '✓ test_null_handling',
  '✓ test_empty_string',
  '✓ test_timeout_5s',
  '✓ test_sql_injection',
  '✓ test_utf8_bom',
];
