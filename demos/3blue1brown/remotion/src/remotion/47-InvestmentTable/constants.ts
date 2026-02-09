import { z } from "zod";

// Video specs
// NOTE: Duration compressed from 20s to ~8.4s (252 frames) to fit the
// orchestrator allocation in Part5CompoundReturns (Visual 4 window:
// s2f(53.94) to s2f(62.34)).  All BEATS are scaled proportionally so
// Row 3, the blue column pulse, and the hold phase render within the
// available window.
export const INVESTMENT_TABLE_FPS = 30;
export const INVESTMENT_TABLE_DURATION_SECONDS = 9;
export const INVESTMENT_TABLE_DURATION_FRAMES =
  INVESTMENT_TABLE_FPS * INVESTMENT_TABLE_DURATION_SECONDS; // 270 frames (covers 252 with margin)
export const INVESTMENT_TABLE_WIDTH = 1920;
export const INVESTMENT_TABLE_HEIGHT = 1080;

// Beat timings (in frames at 30fps) — compressed to fit ~252 frame window
export const BEATS = {
  // Table fade-in (0-0.67s)
  TABLE_FADE_START: 0,
  TABLE_FADE_END: 20,
  // Row 1 slide-in (0.67-1.67s)
  ROW1_START: 20,
  ROW1_END: 50,
  // Row 2 slide-in (2.17-3.17s)
  ROW2_START: 65,
  ROW2_END: 95,
  // Row 3 slide-in (3.67-4.67s)
  ROW3_START: 110,
  ROW3_END: 140,
  // Column-wide pulse (5.33-6.67s)
  PULSE_START: 160,
  PULSE_END: 200,
  // Hold (7.17-8.4s)
  HOLD_START: 215,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  HEADER_BG: "#252545",
  ROW_DARK: "#1E1E2E",
  ROW_ALT: "#222242",
  PATCHING_AMBER: "#D9944A",
  PDD_BLUE: "#4A90D9",
  LABEL_WHITE: "#ffffff",
  BORDER: "rgba(255, 255, 255, 0.15)",
  BORDER_OUTER: "rgba(255, 255, 255, 0.25)",
};

// Table data
export const TABLE_ROWS = [
  {
    investment: "Fix bug",
    patching: "One place, once",
    pdd: "Impossible forever",
  },
  {
    investment: "Improve code",
    patching: "One version",
    pdd: "All future versions",
  },
  {
    investment: "Document behavior",
    patching: "One snapshot",
    pdd: "Living specification",
  },
] as const;

// Props schema
export const InvestmentTableProps = z.object({
  showTable: z.boolean().default(true),
});

export const defaultInvestmentTableProps: z.infer<typeof InvestmentTableProps> =
  {
    showTable: true,
  };

export type InvestmentTablePropsType = z.infer<typeof InvestmentTableProps>;
