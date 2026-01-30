import { z } from "zod";

// Video specs
export const PLASTIC_REGEN_FPS = 30;
export const PLASTIC_REGEN_DURATION_SECONDS = 10;
export const PLASTIC_REGEN_DURATION_FRAMES =
  PLASTIC_REGEN_FPS * PLASTIC_REGEN_DURATION_SECONDS;
export const PLASTIC_REGEN_WIDTH = 1920;
export const PLASTIC_REGEN_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-30:    Setup — part visible, mold glowing in background
// Frame 30-90:   Dissolution — part breaks into 300 particles
// Frame 90-120:  Absence — fully dissolved, only dust remains
// Frame 120-180: Regeneration — particles flow from mold, coalesce
// Frame 180-240: Reformed — part fully back, completion glow
// Frame 240-300: Hold — part exists, mold glowing, narration
export const BEATS = {
  SETUP_START: 0,
  SETUP_END: 30,
  DISSOLVE_START: 30,
  DISSOLVE_END: 90,
  ABSENCE_START: 90,
  ABSENCE_END: 120,
  REGEN_START: 120,
  REGEN_END: 180,
  REFORMED_START: 180,
  REFORMED_END: 240,
  HOLD_START: 240,
  HOLD_END: 300,
  NARRATION_START: 240,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  PART_AMBER: "#D9944A",
  PART_AMBER_LIGHT: "#e8b070",
  PARTICLE_GRAY: "#888888",
  MOLD_BODY: "#5a6a7a",
  MOLD_EDGE: "#8a9aaa",
  MOLD_CAVITY: "#2a2a3e",
  MOLD_GLOW_GOLD: "rgba(217, 148, 74, 0.4)",
  MOLD_GLOW_WHITE: "rgba(255, 255, 255, 0.15)",
  COMPLETION_GLOW: "rgba(255, 255, 255, 0.9)",
};

// Part configuration
export const PART = {
  centerX: 1100,
  centerY: 500,
  width: 80,
  height: 44,
  rx: 10,
};

// Mold (background) configuration
export const MOLD = {
  centerX: 500,
  centerY: 480,
  width: 200,
  height: 110,
  cavityWidth: 90,
  cavityHeight: 34,
};

// Particle system configuration
export const PARTICLE_COUNT = 300;

/**
 * Deterministic pseudo-random based on seed index.
 * Returns a value in [0, 1).
 */
export function seededRandom(seed: number): number {
  const x = Math.sin(seed * 127.1 + 311.7) * 43758.5453;
  return x - Math.floor(x);
}

// Props schema
export const PlasticRegeneratesProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultPlasticRegeneratesProps: z.infer<
  typeof PlasticRegeneratesProps
> = {
  showNarration: true,
};

export type PlasticRegeneratesPropsType = z.infer<
  typeof PlasticRegeneratesProps
>;
