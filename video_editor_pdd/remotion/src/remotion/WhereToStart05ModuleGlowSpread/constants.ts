// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const MODULE_FILL = '#1E293B';
export const MODULE_BORDER = '#334155';
export const MODULE_LABEL_COLOR = '#94A3B8';
export const MIGRATED_GLOW_COLOR = '#5AAA6E';

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const CELL_WIDTH = 140;
export const CELL_HEIGHT = 90;
export const CELL_GAP = 30;
export const GRID_COLS = 4;
export const GRID_ROWS = 3;
export const GRID_CENTER_X = 960;
export const GRID_CENTER_Y = 450;
export const PROMPT_ICON_WIDTH = 12;
export const PROMPT_ICON_HEIGHT = 16;

// === Typography ===
export const MODULE_FONT_SIZE = 11;
export const COUNTER_FONT_SIZE = 16;

// === Counter position ===
export const COUNTER_X = 1700;
export const COUNTER_Y = 950;

// === Total frames ===
export const TOTAL_FRAMES = 330;

// === Module definitions ===
export interface ModuleDefinition {
  id: string;
  label: string;
  row: number;
  col: number;
}

export const MODULES: ModuleDefinition[] = [
  { id: 'auth_handler', label: 'auth_handler', row: 0, col: 0 },
  { id: 'user_service', label: 'user_service', row: 0, col: 1 },
  { id: 'payment_proc', label: 'payment_proc', row: 0, col: 2 },
  { id: 'email_templates', label: 'email_templates', row: 0, col: 3 },
  { id: 'api_routes', label: 'api_routes', row: 1, col: 0 },
  { id: 'config_mgr', label: 'config_mgr', row: 1, col: 1 },
  { id: 'db_models', label: 'db_models', row: 1, col: 2 },
  { id: 'test_utils', label: 'test_utils', row: 1, col: 3 },
  { id: 'middleware', label: 'middleware', row: 2, col: 0 },
  { id: 'validators', label: 'validators', row: 2, col: 1 },
  { id: 'cache_layer', label: 'cache_layer', row: 2, col: 2 },
  { id: 'logging_setup', label: 'logging_setup', row: 2, col: 3 },
];

// === Migration sequence (frameStart when each module begins migrating) ===
export interface MigrationStep {
  id: string;
  frameStart: number;
  order: number;
}

export const MIGRATION_SEQUENCE: MigrationStep[] = [
  { id: 'auth_handler', frameStart: 0, order: 1 },
  { id: 'user_service', frameStart: 30, order: 2 },
  { id: 'payment_proc', frameStart: 75, order: 3 },
  { id: 'email_templates', frameStart: 120, order: 4 },
  { id: 'api_routes', frameStart: 140, order: 5 },
  { id: 'config_mgr', frameStart: 165, order: 6 },
];

// === Counter milestones ===
export interface CounterMilestone {
  frame: number;
  count: number;
}

export const COUNTER_MILESTONES: CounterMilestone[] = [
  { frame: 0, count: 1 },
  { frame: 50, count: 2 },
  { frame: 95, count: 3 },
  { frame: 140, count: 5 },
  { frame: 185, count: 6 },
];

// === Animation durations ===
export const MIGRATE_DURATION = 20;
export const ICON_SCALE_DURATION = 10;
export const CONNECTOR_DRAW_DURATION = 20;
export const CONNECTORS_START_FRAME = 210;

// === Computed grid helpers ===
export const GRID_TOTAL_WIDTH =
  GRID_COLS * CELL_WIDTH + (GRID_COLS - 1) * CELL_GAP;
export const GRID_TOTAL_HEIGHT =
  GRID_ROWS * CELL_HEIGHT + (GRID_ROWS - 1) * CELL_GAP;
export const GRID_LEFT = GRID_CENTER_X - GRID_TOTAL_WIDTH / 2;
export const GRID_TOP = GRID_CENTER_Y - GRID_TOTAL_HEIGHT / 2;

export function getModulePosition(row: number, col: number) {
  return {
    x: GRID_LEFT + col * (CELL_WIDTH + CELL_GAP),
    y: GRID_TOP + row * (CELL_HEIGHT + CELL_GAP),
  };
}

export function getModuleCenter(row: number, col: number) {
  const pos = getModulePosition(row, col);
  return {
    x: pos.x + CELL_WIDTH / 2,
    y: pos.y + CELL_HEIGHT / 2,
  };
}
