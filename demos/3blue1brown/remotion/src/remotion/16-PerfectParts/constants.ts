import { z } from "zod";

// Video specs
export const PERFECT_PARTS_FPS = 30;
export const PERFECT_PARTS_DURATION_SECONDS = 10;
export const PERFECT_PARTS_DURATION_FRAMES =
  PERFECT_PARTS_FPS * PERFECT_PARTS_DURATION_SECONDS;
export const PERFECT_PARTS_WIDTH = 1920;
export const PERFECT_PARTS_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-60:   Mold shown with "fixed" indicator, sparkle on adjustment point
// Frame 60-120: First new perfect part ejects, green checkmark appears
// Frame 120-180: More perfect parts eject, counter continues from 10,001
// Frame 180-240: Previous defective part fades to gray and falls off-screen
// Frame 240-300: Production continues, perfect parts streaming
export const BEATS = {
  MOLD_FIXED_START: 0,
  MOLD_FIXED_END: 60,
  FIRST_PERFECT_START: 60,
  FIRST_PERFECT_END: 120,
  MORE_PARTS_START: 120,
  MORE_PARTS_END: 180,
  DEFECT_DISCARD_START: 180,
  DEFECT_DISCARD_END: 240,
  STREAMING_START: 240,
  STREAMING_END: 300,
  NARRATION_START: 240,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  MOLD_BODY: "#5a6a7a",
  MOLD_CAVITY: "#2a2a3e",
  MOLD_EDGE: "#8a9aaa",
  PART_AMBER: "#D9944A",
  PART_AMBER_LIGHT: "#e8b070",
  PERFECT_GREEN: "#5AAA6E",
  PERFECT_GREEN_GLOW: "rgba(90, 170, 110, 0.4)",
  DEFECT_GRAY: "#666666",
  COUNTER_WHITE: "#ffffff",
  COUNTER_GLOW: "rgba(74, 144, 217, 0.8)",
  LABEL_GRAY: "#888888",
  SPARKLE_WHITE: "#ffffff",
  SPARKLE_GOLD: "#FFD700",
  MOLD_UPDATED_LABEL: "#5AAA6E",
};

// Mold cross-section configuration (matches 14-PartsEject)
export const MOLD = {
  centerX: 580,
  centerY: 360,
  halfWidth: 160,
  halfHeight: 80,
  cavityWidth: 80,
  cavityHeight: 30,
  gapMax: 50,
  // The adjustment/fix point location (right side of mold)
  fixPointX: 580 + 160 - 20,
  fixPointY: 360,
};

// Part shape (matches 14-PartsEject)
export const PART_SHAPE = {
  width: 68,
  height: 36,
  rx: 8,
};

/**
 * Returns the displayed parts count at a given frame.
 * Continues from 10,001 (picking up from 14-PartsEject's 10,000).
 */
export function getPartsCount(frame: number): number {
  if (frame < BEATS.FIRST_PERFECT_START) return 10001;
  if (frame >= BEATS.STREAMING_END) return 10052;

  const progress = Math.min(
    (frame - BEATS.FIRST_PERFECT_START) /
      (BEATS.STREAMING_END - BEATS.FIRST_PERFECT_START),
    1,
  );

  // Linear ramp from 10,001 to ~10,052
  return 10001 + Math.floor(progress * 51);
}

/**
 * Formats a number with comma separators.
 */
export function formatCount(n: number): string {
  return n.toLocaleString("en-US");
}

// Props schema
export const PerfectPartsProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultPerfectPartsProps: z.infer<typeof PerfectPartsProps> = {
  showNarration: true,
};

export type PerfectPartsPropsType = z.infer<typeof PerfectPartsProps>;
