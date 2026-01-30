import { z } from "zod";

// Video specs for AI Milestones section
export const AI_MILESTONES_FPS = 30;
export const AI_MILESTONES_DURATION_SECONDS = 18;
export const AI_MILESTONES_DURATION_FRAMES = AI_MILESTONES_FPS * AI_MILESTONES_DURATION_SECONDS;
export const AI_MILESTONES_WIDTH = 1920;
export const AI_MILESTONES_HEIGHT = 1080;

// Animation beat timings (in frames at 30fps)
export const BEATS = {
  // Frame 0-60: Zoom into 2020-2025 region
  ZOOM_START: 0,
  ZOOM_END: 60,

  // Frame 60-150: Codex/Copilot marker appears (2021) — small drop
  CODEX_START: 60,
  CODEX_END: 150,

  // Frame 150-240: GPT-4 marker appears (Mar 2023) — moderate drop
  GPT4_START: 150,
  GPT4_END: 240,

  // Frame 240-330: Claude 3.5 Sonnet marker appears (Jun 2024) — LARGE drop (the cliff)
  CLAUDE35_START: 240,
  CLAUDE35_END: 330,

  // Frame 330-390: Claude 3.7 Sonnet marker appears (Feb 2025) — moderate drop
  CLAUDE37_START: 330,
  CLAUDE37_END: 390,

  // Frame 390-450: Frontier cluster (staggered by 15 frames)
  FRONTIER_START: 390,
  OPUS_START: 390,
  GPT52_START: 405,
  GEMINI3_START: 420,
  FRONTIER_END: 450,

  // Frame 450-540: Hold with subtle pulse
  HOLD_START: 450,
  HOLD_END: 540,
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

  // Milestone marker colors
  CODEX: "#3B82F6",     // Blue
  GPT4: "#8B5CF6",      // Purple
  CLAUDE: "#F59E0B",    // Orange (Claude 3.5, 3.7, Opus 4.5)
  GEMINI: "#EF4444",    // Red

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
  impactScale: number; // 1.0 = small, 1.2 = moderate, 1.5 = large
}

export const MILESTONES: Milestone[] = [
  { id: "codex", name: "Codex / Copilot", year: 2021, color: COLORS.CODEX, startFrame: BEATS.CODEX_START, impactScale: 1.0 },
  { id: "gpt4", name: "GPT-4", year: 2023.25, color: COLORS.GPT4, startFrame: BEATS.GPT4_START, impactScale: 1.2 },
  { id: "claude35", name: "Claude 3.5 Sonnet", year: 2024.5, color: COLORS.CLAUDE, startFrame: BEATS.CLAUDE35_START, impactScale: 1.5 },
  { id: "claude37", name: "Claude 3.7 Sonnet", year: 2025.15, color: COLORS.CLAUDE, startFrame: BEATS.CLAUDE37_START, impactScale: 1.2 },
  { id: "opus45", name: "Opus 4.5", year: 2025.7, color: COLORS.CLAUDE, startFrame: BEATS.OPUS_START, impactScale: 1.0 },
  { id: "gpt52", name: "GPT 5.2", year: 2025.8, color: COLORS.GPT4, startFrame: BEATS.GPT52_START, impactScale: 1.0 },
  { id: "gemini3", name: "Gemini 3", year: 2025.9, color: COLORS.GEMINI, startFrame: BEATS.GEMINI3_START, impactScale: 1.0 },
];

// Chart dimensions
export const CHART_MARGINS = {
  top: 100,
  right: 200,
  bottom: 120,
  left: 180,
};

// Year range for the zoomed view (2020-2026)
export const YEAR_RANGE = { min: 2020, max: 2026 };

// Cost data in Developer Hours — uneven staircase descent
// Each milestone causes a drop of different size
export const COST_DATA = [
  { year: 2020, cost: 30 },
  { year: 2020.5, cost: 29 },
  { year: 2021, cost: 28 },       // Codex: small drop
  { year: 2022, cost: 27 },
  { year: 2023, cost: 26 },
  { year: 2023.25, cost: 20 },    // GPT-4: moderate drop
  { year: 2023.75, cost: 18 },
  { year: 2024, cost: 16 },
  { year: 2024.5, cost: 7 },      // Claude 3.5 Sonnet: LARGE drop (the cliff)
  { year: 2024.75, cost: 6 },
  { year: 2025, cost: 5.5 },
  { year: 2025.15, cost: 4.5 },   // Claude 3.7 Sonnet: moderate drop
  { year: 2025.5, cost: 4 },
  { year: 2025.7, cost: 3.5 },    // Opus 4.5
  { year: 2025.8, cost: 3.2 },    // GPT 5.2
  { year: 2025.9, cost: 3 },      // Gemini 3: settled
];

export const COST_RANGE = { min: 0, max: 35 };

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
