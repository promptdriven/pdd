import { z } from "zod";

// Video specs from the animation doc
export const COLD_OPEN_FPS = 60;
export const COLD_OPEN_DURATION_SECONDS = 38;
export const COLD_OPEN_DURATION_FRAMES = COLD_OPEN_FPS * COLD_OPEN_DURATION_SECONDS;
export const COLD_OPEN_WIDTH = 1920; // 1080p for now, can upgrade to 4K
export const COLD_OPEN_HEIGHT = 1080;

// Beat timings (in seconds, converted to frames when needed)
export const BEATS = {
  ESTABLISH_START: 0,
  ESTABLISH_END: 8,
  SYNC_COMPLETION_START: 8,
  SYNC_COMPLETION_END: 15,
  SATISFACTION_START: 15,
  SATISFACTION_END: 18,
  ZOOM_OUT_START: 18,
  ZOOM_OUT_END: 32,
  HOLD_START: 32,
  HOLD_END: 38,
};

// Convert seconds to frames helper
export const secondsToFrames = (seconds: number) => Math.round(seconds * COLD_OPEN_FPS);

// Color palette from spec
export const COLORS = {
  // Left side (Modern/Developer)
  LEFT_BG: "#1a1a2e",
  LEFT_ACCENT: "#4A90D9",
  CODE_NORMAL: "#e0e0e0",
  CODE_ADDED: "#4ade80",
  CODE_REMOVED: "#f87171",

  // Right side (1950s/Grandmother)
  RIGHT_BG: "#2d2416",
  RIGHT_ACCENT: "#D9944A",

  // Shared
  DIVIDER: "#ffffff",
};

// Props schema
export const ColdOpenProps = z.object({
  // Could add configurable props here
});

export const defaultColdOpenProps: z.infer<typeof ColdOpenProps> = {};

export type ColdOpenPropsType = z.infer<typeof ColdOpenProps>;
