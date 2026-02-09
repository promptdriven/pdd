import { z } from "zod";

// Video specs
export const DEFECT_FPS = 30;
export const DEFECT_DURATION_SECONDS = 10;
export const DEFECT_DURATION_FRAMES = DEFECT_FPS * DEFECT_DURATION_SECONDS;
export const DEFECT_WIDTH = 1920;
export const DEFECT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-60:    Production continues — mold cycling, parts ejecting
// Frame 60-120:  One part ejects with visible defect (crack/missing section)
// Frame 120-180: Production pauses, red pulsing highlight + "DEFECT" label
// Frame 180-300: Zoom in on defect, hold. Other parts blur/fade.
export const BEATS = {
  PRODUCTION_START: 0,
  PRODUCTION_END: 60,
  DEFECT_EJECT_START: 60,
  DEFECT_EJECT_END: 120,
  PAUSE_HIGHLIGHT_START: 120,
  PAUSE_HIGHLIGHT_END: 180,
  LABEL_APPEAR: 150,
  ZOOM_START: 180,
  ZOOM_END: 300,
  NARRATION_START: 250,
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
  DEFECT_RED: "#D94A4A",
  DEFECT_RED_GLOW: "rgba(217, 74, 74, 0.6)",
  DEFECT_RED_BG: "rgba(217, 74, 74, 0.7)",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Mold cross-section configuration (reuses PartsEject visual layout)
export const MOLD = {
  centerX: 580,
  centerY: 340,
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

// Mold cycling helpers (simplified from PartsEject for steady-pace production)

/**
 * Returns cycle phase (0-1) for a steady cycling mold.
 * Runs at a fixed speed of one full cycle per 30 frames.
 */
export function getCyclePhase(frame: number): number {
  const cycleLength = 30; // frames per full cycle
  return (frame % cycleLength) / cycleLength;
}

/**
 * Maps cycle phase to mold opening amount (0=closed, 1=fully open).
 * Opens during phase 0-0.3, stays open 0.3-0.5, closes 0.5-0.8.
 */
export function getMoldOpening(frame: number, frozen: boolean): number {
  if (frozen) return 0;
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
 * Returns how many complete cycles have happened by a given frame.
 */
export function getCompletedCycles(frame: number): number {
  const cycleLength = 30;
  return Math.floor(frame / cycleLength);
}

// Props schema
export const DefectDiscoveredProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultDefectDiscoveredProps: z.infer<
  typeof DefectDiscoveredProps
> = {
  showNarration: true,
};

export type DefectDiscoveredPropsType = z.infer<typeof DefectDiscoveredProps>;
