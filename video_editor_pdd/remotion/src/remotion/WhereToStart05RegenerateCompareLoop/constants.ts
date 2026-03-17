// Component-level constants for WhereToStart05RegenerateCompareLoop

export const DURATION_FRAMES = 180;
export const FPS = 30;

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A0F1A";

// Pipeline positions (x, y)
export const PIPELINE_Y = 420;
export const STEP_POSITIONS: [number, number][] = [
  [200, PIPELINE_Y],
  [540, PIPELINE_Y],
  [880, PIPELINE_Y],
  [1220, PIPELINE_Y],
];

// Colors
export const BLUE = "#4A90D9";
export const AMBER = "#D9944A";
export const GREEN = "#5AAA6E";
export const DIM_BORDER = "#334155";
export const DARK_FILL = "#0F172A";
export const TEXT_LIGHT = "#E2E8F0";
export const TEXT_DIM = "#64748B";
export const TRACK_COLOR = "#1E293B";
export const LINE_COLOR = "#CBD5E1";

// Progress bar
export const PROGRESS_Y = 620;
export const PROGRESS_WIDTH = 1100;
export const PROGRESS_HEIGHT = 6;

// Animation frame ranges
export const STEP1_START = 20;
export const STEP2_START = 50;
export const STEP3_START = 80;
export const STEP4_START = 110;
export const LOOP_START = 140;
export const HOLD_START = 165;

// Step data
export const STEPS = [
  { label: "Generate prompt", sublabel: "pdd update" },
  { label: "Add tests", sublabel: "pdd bug" },
  { label: "Regenerate", sublabel: "pdd fix" },
  { label: "Compare", sublabel: "pdd test" },
] as const;
