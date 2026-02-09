import { z } from "zod";

// Video specs
export const TRADITIONAL_VS_PDD_FPS = 30;
export const TRADITIONAL_VS_PDD_DURATION_SECONDS = 25;
export const TRADITIONAL_VS_PDD_DURATION_FRAMES =
  TRADITIONAL_VS_PDD_FPS * TRADITIONAL_VS_PDD_DURATION_SECONDS;
export const TRADITIONAL_VS_PDD_WIDTH = 1920;
export const TRADITIONAL_VS_PDD_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Both sides animate in parallel from frame 0 per spec (simultaneous side-by-side comparison)
export const BEATS = {
  SPLIT_START: 0,
  SPLIT_END: 60,
  TRADITIONAL_ANIMATE_START: 60,
  TRADITIONAL_ANIMATE_END: 450,
  PDD_ANIMATE_START: 60,
  PDD_ANIMATE_END: 450,
  COMPARISON_START: 480,
  INSIGHT_START: 600,
  HOLD_START: 720,
};

// Traditional side cycling: the bug-patch loop repeats every CYCLE_PERIOD frames
// Per spec line 153: const cyclePosition = frame % 180
export const TRADITIONAL_CYCLE_PERIOD = 180;

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  TRADITIONAL_RED: "#E74C3C",
  PDD_GREEN: "#4CAF50",
  WALLS_AMBER: "#D9944A",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
  DIVIDER: "#444444",
};

// Traditional approach steps
export const TRADITIONAL_STEPS = [
  "Write code",
  "Find bug",
  "Fix code",
  "Find bug",
  "Fix code",
  "Find bug...",
];

// PDD approach steps
export const PDD_STEPS = [
  "Define spec (prompt + tests)",
  "Generate code",
  "Bug found → add test",
  "Regenerate code",
  "All tests pass ✓",
];

// Props schema
export const TraditionalVsPddProps = z.object({
  showComparison: z.boolean().default(true),
});

export const defaultTraditionalVsPddProps: z.infer<typeof TraditionalVsPddProps> = {
  showComparison: true,
};

export type TraditionalVsPddPropsType = z.infer<typeof TraditionalVsPddProps>;
