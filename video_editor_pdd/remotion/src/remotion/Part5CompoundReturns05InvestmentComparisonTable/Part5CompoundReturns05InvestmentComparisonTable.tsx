import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import { TableRow } from "./TableRow";
import { SummaryLine } from "./SummaryLine";
import {
  BG_COLOR,
  LABEL_COLOR,
  PATCHING_COLOR,
  PDD_COLOR,
  TABLE_WIDTH,
  COL_WIDTH,
  HEADER_HEIGHT,
  TABLE_BORDER_RADIUS,
  TABLE_X,
  TABLE_Y,
  TABLE_FADE_START,
  TABLE_FADE_DURATION,
  ROW1_START,
  ROW2_START,
  ROW3_START,
  TABLE_ROWS,
} from "./constants";

export const defaultPart5CompoundReturns05InvestmentComparisonTableProps = {};

export const Part5CompoundReturns05InvestmentComparisonTable: React.FC = () => {
  const frame = useCurrentFrame();

  // Table container fade-in
  const containerOpacity = interpolate(
    frame - TABLE_FADE_START,
    [0, TABLE_FADE_DURATION],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const headerLabelStyle = (
    color: string,
    align: "left" | "center"
  ): React.CSSProperties => ({
    width: COL_WIDTH,
    height: HEADER_HEIGHT,
    display: "flex",
    alignItems: "center",
    justifyContent: align === "center" ? "center" : "flex-start",
    paddingLeft: align === "left" ? 24 : 0,
    boxSizing: "border-box",
    fontFamily: "Inter, sans-serif",
    fontSize: 12,
    fontWeight: 600,
    color,
    opacity: 0.5,
    letterSpacing: 2,
    textTransform: "uppercase" as const,
  });

  const rowStarts = [ROW1_START, ROW2_START, ROW3_START];

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Table container */}
      <div
        style={{
          position: "absolute",
          left: TABLE_X,
          top: TABLE_Y,
          width: TABLE_WIDTH,
          opacity: containerOpacity,
          border: `1px solid rgba(51, 65, 85, 0.3)`,
          borderRadius: TABLE_BORDER_RADIUS,
          overflow: "hidden",
          backgroundColor: BG_COLOR,
        }}
      >
        {/* Header row */}
        <div
          style={{
            display: "flex",
            width: "100%",
            height: HEADER_HEIGHT,
            backgroundColor: `rgba(30, 41, 59, 0.4)`,
          }}
        >
          <div style={headerLabelStyle(LABEL_COLOR, "left")}>INVESTMENT</div>
          <div style={headerLabelStyle(PATCHING_COLOR, "center")}>
            PATCHING
          </div>
          <div style={headerLabelStyle(PDD_COLOR, "center")}>PDD</div>
        </div>

        {/* Data rows */}
        {TABLE_ROWS.map((row, i) => (
          <TableRow
            key={row.investment}
            investment={row.investment}
            icon={row.icon}
            patching={row.patching}
            pdd={row.pdd}
            pddGlow={row.pddGlow}
            pddOpacity={row.pddOpacity}
            alternate={row.alternate}
            rowStart={rowStarts[i]}
          />
        ))}
      </div>

      {/* Summary line */}
      <SummaryLine />
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns05InvestmentComparisonTable;
