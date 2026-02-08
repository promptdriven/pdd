import { z } from "zod";

// Video specs
export const INVESTMENT_TABLE_FPS = 30;
export const INVESTMENT_TABLE_DURATION_SECONDS = 20;
export const INVESTMENT_TABLE_DURATION_FRAMES =
  INVESTMENT_TABLE_FPS * INVESTMENT_TABLE_DURATION_SECONDS;
export const INVESTMENT_TABLE_WIDTH = 1920;
export const INVESTMENT_TABLE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Table fade-in (0-1.5s)
  TABLE_FADE_START: 0,
  TABLE_FADE_END: 45,
  // Row 1 slide-in (1.5-5s)
  ROW1_START: 45,
  ROW1_END: 120,
  // Row 2 slide-in (5-9s)
  ROW2_START: 150,
  ROW2_END: 225,
  // Row 3 slide-in (9-13s)
  ROW3_START: 270,
  ROW3_END: 345,
  // Column-wide pulse (13-16s)
  PULSE_START: 390,
  PULSE_END: 450,
  // Hold (16-20s)
  HOLD_START: 480,
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
