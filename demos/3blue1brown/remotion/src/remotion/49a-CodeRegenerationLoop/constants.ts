import { z } from "zod";

// Video specs
export const CODE_REGEN_LOOP_FPS = 30;
export const CODE_REGEN_LOOP_DURATION_SECONDS = 10;
export const CODE_REGEN_LOOP_DURATION_FRAMES =
  CODE_REGEN_LOOP_FPS * CODE_REGEN_LOOP_DURATION_SECONDS;
export const CODE_REGEN_LOOP_WIDTH = 1920;
export const CODE_REGEN_LOOP_HEIGHT = 1080;

// Cycle structure: 120 frames (4 seconds) per cycle, 2.5 cycles over 300 frames
export const CYCLE_LENGTH = 120;

// Per-cycle beat timings (frame offsets within each 120-frame cycle)
export const CYCLE_BEATS = {
  HOLD_START: 0,
  HOLD_END: 30,
  DISSOLVE_START: 30,
  DISSOLVE_END: 60,
  REGENERATE_START: 60,
  REGENERATE_END: 90,
  VERIFY_START: 90,
  VERIFY_END: 120,
};

// Final hold: after frame 240, stop cycling and hold on v3
export const FINAL_HOLD_START = 240;

// Triangle layout (persistent background)
// Vertices positioned for a large equilateral-ish triangle centered on screen
export const TRIANGLE = {
  PROMPT: { x: 960, y: 200 },      // top vertex
  TESTS: { x: 520, y: 760 },       // bottom-left vertex
  GROUNDING: { x: 1400, y: 760 },  // bottom-right vertex
  CENTROID: { x: 960, y: 573 },    // approximate centroid
};

// Code block position (centered at triangle centroid)
export const CODE_BLOCK = {
  x: 900,
  y: 410,
  width: 120,
  height: 100,
};

// Particle system
export const PARTICLE_COUNT = 100;

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  PROMPT_BLUE: "#4A90D9",
  TESTS_AMBER: "#D9944A",
  GROUNDING_GREEN: "#5AAA6E",
  CODE_GRAY: "#A0A0A0",
  SUCCESS_GREEN: "#5AAA6E",
  LABEL_WHITE: "#ffffff",
  TERMINAL_BG: "rgba(30, 30, 46, 0.7)",
  TERMINAL_BORDER: "rgba(255, 255, 255, 0.08)",
};

/**
 * Deterministic pseudo-random based on seed index.
 * Returns a value in [0, 1).
 */
export function seededRandom(seed: number): number {
  const x = Math.sin(seed * 127.1 + 311.7) * 43758.5453;
  return x - Math.floor(x);
}

/**
 * Generate a deterministic code pattern (array of bar widths as percentages)
 * for a given cycle seed. Each seed produces visibly different bar counts/widths.
 */
export function generateCodePattern(seed: number): number[] {
  const lineCount = 5 + Math.floor(seededRandom(seed * 13 + 7) * 3);
  return Array.from({ length: lineCount }, (_, i) =>
    30 + Math.floor(seededRandom(seed * 13 + 7 + (i + 1) * 31) * 60)
  );
}

// Props schema
export const CodeRegenerationLoopProps = z.object({
  showTerminal: z.boolean().default(true),
});

export const defaultCodeRegenerationLoopProps: z.infer<
  typeof CodeRegenerationLoopProps
> = {
  showTerminal: true,
};

export type CodeRegenerationLoopPropsType = z.infer<
  typeof CodeRegenerationLoopProps
>;
