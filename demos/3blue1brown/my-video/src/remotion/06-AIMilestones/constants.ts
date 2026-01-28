import { z } from "zod";

// Video specs for AI Milestones section
export const AI_MILESTONES_FPS = 30;
export const AI_MILESTONES_DURATION_SECONDS = 15;
export const AI_MILESTONES_DURATION_FRAMES = AI_MILESTONES_FPS * AI_MILESTONES_DURATION_SECONDS;
export const AI_MILESTONES_WIDTH = 1920;
export const AI_MILESTONES_HEIGHT = 1080;

// Animation beat timings (in frames at 30fps)
export const BEATS = {
  // Frame 0-60: Zoom into 2020-2024 region
  ZOOM_START: 0,
  ZOOM_END: 60,

  // Frame 60-120: GPT-3 marker pops in
  GPT3_START: 60,
  GPT3_END: 120,

  // Frame 120-180: Codex marker appears
  CODEX_START: 120,
  CODEX_END: 180,

  // Frame 180-270: GPT-4, Claude, Gemini appear in quick succession (staggered 30 frames)
  GPT4_START: 180,
  CLAUDE_START: 210,
  GEMINI_START: 240,
  RAPID_MARKERS_END: 270,

  // Frame 270-360: All markers visible, line settles
  SETTLE_START: 270,
  SETTLE_END: 360,

  // Frame 360-450: Hold with subtle pulse
  HOLD_START: 360,
  HOLD_END: 450,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  GRID: "#333344",
  AXIS: "#666677",
  AXIS_LABEL: "rgba(255, 255, 255, 0.8)",
  TITLE: "#ffffff",

  // Cost line (from previous chart)
  LINE_COST: "#4A90D9",

  // Milestone marker colors as specified
  GPT3: "#10B981",    // Green
  CODEX: "#3B82F6",   // Blue
  GPT4: "#8B5CF6",    // Purple
  CLAUDE: "#F59E0B",  // Orange
  GEMINI: "#EF4444",  // Red

  // Faded state for non-zoom regions
  FADED: "rgba(255, 255, 255, 0.3)",
};

// AI milestone data
export interface Milestone {
  id: string;
  name: string;
  year: number;
  color: string;
  startFrame: number;
}

export const MILESTONES: Milestone[] = [
  { id: "gpt3", name: "GPT-3", year: 2020, color: COLORS.GPT3, startFrame: BEATS.GPT3_START },
  { id: "codex", name: "Codex", year: 2021, color: COLORS.CODEX, startFrame: BEATS.CODEX_START },
  { id: "gpt4", name: "GPT-4", year: 2023, color: COLORS.GPT4, startFrame: BEATS.GPT4_START },
  { id: "claude", name: "Claude", year: 2023, color: COLORS.CLAUDE, startFrame: BEATS.CLAUDE_START },
  { id: "gemini", name: "Gemini", year: 2023, color: COLORS.GEMINI, startFrame: BEATS.GEMINI_START },
];

// Chart dimensions
export const CHART_MARGINS = {
  top: 100,
  right: 200,
  bottom: 120,
  left: 180,
};

// Year range for the zoomed view (2020-2024)
export const YEAR_RANGE = { min: 2020, max: 2024 };

// Simulated cost data showing the dramatic drop during AI era
// This represents cost in arbitrary units (dropping steeply)
export const COST_DATA = [
  { year: 2020, cost: 100 },
  { year: 2020.5, cost: 85 },
  { year: 2021, cost: 70 },
  { year: 2021.5, cost: 55 },
  { year: 2022, cost: 42 },
  { year: 2022.5, cost: 30 },
  { year: 2023, cost: 18 },
  { year: 2023.5, cost: 10 },
  { year: 2024, cost: 5 },
];

export const COST_RANGE = { min: 0, max: 120 };

// Spring animation config as specified
export const SPRING_CONFIG = {
  damping: 12,
  stiffness: 200,
};

// Props schema
export const AIMilestonesProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultAIMilestonesProps: z.infer<typeof AIMilestonesProps> = {
  showTitle: true,
};

export type AIMilestonesPropsType = z.infer<typeof AIMilestonesProps>;
