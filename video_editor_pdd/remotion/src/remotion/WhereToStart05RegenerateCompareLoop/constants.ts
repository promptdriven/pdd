// constants.ts — Colors, dimensions, and step configuration

export const CANVAS = {
  width: 1920,
  height: 1080,
  background: "#0A0F1A",
} as const;

export const COLORS = {
  blue: "#4A90D9",
  amber: "#D9944A",
  green: "#5AAA6E",
  textPrimary: "#E2E8F0",
  textSecondary: "#64748B",
  border: "#334155",
  cardFill: "#0F172A",
  trackBg: "#1E293B",
  codeLine: "#CBD5E1",
} as const;

export const STEP_POSITIONS = [
  { x: 200, y: 420 },
  { x: 540, y: 420 },
  { x: 880, y: 420 },
  { x: 1220, y: 420 },
] as const;

export const STEPS = [
  { label: "Generate prompt", sublabel: "pdd update", startFrame: 20 },
  { label: "Add tests", sublabel: "pdd bug", startFrame: 50 },
  { label: "Regenerate", sublabel: "pdd fix", startFrame: 80 },
  { label: "Compare", sublabel: "pdd test", startFrame: 110 },
] as const;

export const PROGRESS_KEYFRAMES = [
  { frame: 20, value: 0 },
  { frame: 50, value: 0.25 },
  { frame: 80, value: 0.5 },
  { frame: 110, value: 0.75 },
  { frame: 140, value: 1.0 },
  { frame: 155, value: 0.8 },
] as const;

export const LOOP_ARROW_START_FRAME = 140;
export const TOTAL_FRAMES = 180;
