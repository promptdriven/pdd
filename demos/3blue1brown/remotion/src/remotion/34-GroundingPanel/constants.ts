import { z } from "zod";

// Video specs
export const GROUNDING_PANEL_FPS = 30;
export const GROUNDING_PANEL_DURATION_SECONDS = 15;
export const GROUNDING_PANEL_DURATION_FRAMES =
  GROUNDING_PANEL_FPS * GROUNDING_PANEL_DURATION_SECONDS;
export const GROUNDING_PANEL_WIDTH = 1920;
export const GROUNDING_PANEL_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  PANEL_START: 0,
  PANEL_END: 90,
  OOP_START: 90,
  OOP_END: 130,
  FUNCTIONAL_START: 180,
  FUNCTIONAL_END: 220,
  TEAM_START: 270,
  TEAM_END: 310,
  HOLD_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  GROUNDING_GREEN: "#5AAA6E",
  OOP_BLUE: "#6688AA",
  FUNCTIONAL_PURPLE: "#9966CC",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Style swatches
export const STYLE_SWATCHES = [
  { label: "OOP", pattern: "grid", color: COLORS.OOP_BLUE },
  { label: "Functional", pattern: "flow", color: COLORS.FUNCTIONAL_PURPLE },
  { label: "Your Team's Style", pattern: "custom", color: COLORS.GROUNDING_GREEN },
];

// Props schema
export const GroundingPanelProps = z.object({
  showSwatches: z.boolean().default(true),
});

export const defaultGroundingPanelProps: z.infer<typeof GroundingPanelProps> = {
  showSwatches: true,
};

export type GroundingPanelPropsType = z.infer<typeof GroundingPanelProps>;
