import { z } from "zod";

// Video specs - 15 seconds at 30fps
export const SPLIT_COMPARISON_FPS = 30;
export const SPLIT_COMPARISON_DURATION_SECONDS = 15;
export const SPLIT_COMPARISON_DURATION_FRAMES =
  SPLIT_COMPARISON_FPS * SPLIT_COMPARISON_DURATION_SECONDS;
export const SPLIT_COMPARISON_WIDTH = 1920;
export const SPLIT_COMPARISON_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Based on spec timing
export const BEATS = {
  // Divider fade in (0-1s)
  DIVIDER_FADE_START: 0,
  DIVIDER_FADE_END: 30,
};

// Color palette
export const COLORS = {
  DIVIDER_WHITE: "#ffffff",
};

// Props schema
export const SplitComparisonProps = z.object({
  showDivider: z.boolean().default(true),
  dividerOpacityMax: z.number().default(0.5),
});

export const defaultSplitComparisonProps: z.infer<typeof SplitComparisonProps> = {
  showDivider: true,
  dividerOpacityMax: 0.5,
};

export type SplitComparisonPropsType = z.infer<typeof SplitComparisonProps>;
