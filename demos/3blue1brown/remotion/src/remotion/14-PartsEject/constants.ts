import { z } from "zod";

// Video specs
export const PARTS_EJECT_FPS = 30;
export const PARTS_EJECT_DURATION_SECONDS = 20;
export const PARTS_EJECT_DURATION_FRAMES =
  PARTS_EJECT_FPS * PARTS_EJECT_DURATION_SECONDS;
export const PARTS_EJECT_WIDTH = 1920;
export const PARTS_EJECT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-60:   First eject — single slow cycle
// Frame 60-120: Ramp — cycles begin accelerating
// Frame 120-240: Rapid — fast cycling
// Frame 240-420: Blur — near-continuous stream
// Frame 420-600: Hold — counter settled, narration appears
export const BEATS = {
  FIRST_EJECT_START: 0,
  FIRST_EJECT_END: 60,
  RAMP_START: 60,
  RAMP_END: 120,
  RAPID_START: 120,
  RAPID_END: 240,
  BLUR_START: 240,
  BLUR_END: 420,
  HOLD_START: 420,
  HOLD_END: 600,
  NARRATION_START: 460,
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
  COUNTER_WHITE: "#ffffff",
  COUNTER_GLOW: "rgba(74, 144, 217, 0.5)",
  LABEL_GRAY: "#888888",
  STREAM_AMBER: "#D9944A",
};

// Mold cross-section configuration
export const MOLD = {
  centerX: 580,
  centerY: 360,
  halfWidth: 160,
  halfHeight: 80,
  cavityWidth: 80,
  cavityHeight: 30,
  gapMax: 50,
};

// Part shape
export const PART_SHAPE = {
  width: 68,
  height: 36,
  rx: 8,
};

/**
 * Returns the accumulated number of mold cycles at a given frame.
 * Uses a power curve for exponential acceleration.
 */
export function getAccumulatedCycles(frame: number): number {
  if (frame <= 0) return 0;
  // Clamp to active animation range
  const f = Math.min(frame, BEATS.HOLD_START);
  return Math.pow(f / 52, 2.2);
}

/**
 * Returns the fractional phase within the current cycle (0-1).
 * 0 = mold closed, ~0.3 = fully open, ~0.6 = part ejected, 1 = closed again.
 */
export function getCyclePhase(frame: number): number {
  const acc = getAccumulatedCycles(frame);
  return acc - Math.floor(acc);
}

/**
 * Maps cycle phase to mold opening amount (0=closed, 1=fully open).
 * Opens during phase 0-0.3, stays open 0.3-0.5, closes 0.5-0.8.
 */
export function getMoldOpening(frame: number): number {
  if (frame >= BEATS.HOLD_START) return 0;
  const phase = getCyclePhase(frame);
  if (phase < 0.3) {
    return phase / 0.3;
  } else if (phase < 0.5) {
    return 1;
  } else if (phase < 0.8) {
    return 1 - (phase - 0.5) / 0.3;
  }
  return 0;
}

/**
 * Returns the displayed parts count at a given frame.
 * Logarithmic interpolation: 0 -> 1 -> 10 -> 100 -> 1,000 -> 10,000.
 */
export function getPartsCount(frame: number): number {
  if (frame < BEATS.FIRST_EJECT_END * 0.5) return 0;
  if (frame >= BEATS.HOLD_START) return 10000;

  // Map frame to a 0-1 progress across the active range
  const progress = Math.min(
    (frame - BEATS.FIRST_EJECT_END * 0.5) /
      (BEATS.HOLD_START - BEATS.FIRST_EJECT_END * 0.5),
    1
  );

  // Logarithmic scale: 10^(progress * 4) gives 1 -> 10,000
  const value = Math.pow(10, progress * 4);
  return Math.min(Math.round(value), 10000);
}

/**
 * Returns the frame at which cycle N completes (inverse of getAccumulatedCycles).
 */
export function getSpawnFrame(n: number): number {
  if (n <= 0) return 0;
  return Math.round(52 * Math.pow(n, 1 / 2.2));
}

/**
 * Formats a number with comma separators.
 */
export function formatCount(n: number): string {
  return n.toLocaleString("en-US");
}

// Props schema
export const PartsEjectProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultPartsEjectProps: z.infer<typeof PartsEjectProps> = {
  showNarration: true,
};

export type PartsEjectPropsType = z.infer<typeof PartsEjectProps>;
