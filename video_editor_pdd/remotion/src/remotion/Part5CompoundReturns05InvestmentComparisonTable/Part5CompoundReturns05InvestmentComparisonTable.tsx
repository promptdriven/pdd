import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  TABLE_LEFT,
  TABLE_TOP,
  COL_WIDTH,
  ROW_HEIGHT,
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  HEADER_LETTER_SPACING,
  HEADER_INVESTMENT_COLOR,
  HEADER_PATCHING_COLOR,
  HEADER_PDD_COLOR,
  BORDER_COLOR,
  HEADER_FADE_DURATION,
  UNDERLINE_DRAW_DURATION,
  HEADER_UNDERLINE_Y,
  ROW1_START,
  ROW2_START,
  ROW3_START,
  GLOW_START,
  TABLE_ROWS,
} from "./constants";
import { AnimatedTableRow } from "./AnimatedTableRow";
import { GlowSweep } from "./GlowSweep";

// ── Default Props ───────────────────────────────────────────────────
export const defaultPart5CompoundReturns05InvestmentComparisonTableProps = {};

// ── Header Sub-component ────────────────────────────────────────────
const TableHeader: React.FC = () => {
  const frame = useCurrentFrame();

  // Start at 0.3 so content is visible from frame 0, fade to full
  const opacity = interpolate(frame, [0, HEADER_FADE_DURATION], [0.3, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Underline draw animation (width grows from 0 to full)
  const underlineProgress = interpolate(
    frame,
    [0, UNDERLINE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const headerStyle: React.CSSProperties = {
    fontFamily: "Inter, sans-serif",
    fontSize: HEADER_FONT_SIZE,
    fontWeight: HEADER_FONT_WEIGHT,
    letterSpacing: HEADER_LETTER_SPACING,
    textTransform: "uppercase",
    height: 40,
    display: "flex",
    alignItems: "center",
    paddingLeft: 24,
    paddingRight: 16,
    boxSizing: "border-box",
  };

  const tableWidth = COL_WIDTH * 3;

  return (
    <div
      style={{
        position: "absolute",
        left: TABLE_LEFT,
        top: TABLE_TOP,
        width: tableWidth,
        opacity,
      }}
    >
      {/* Header labels */}
      <div style={{ display: "flex", flexDirection: "row" }}>
        <div style={{ ...headerStyle, width: COL_WIDTH, color: HEADER_INVESTMENT_COLOR }}>
          INVESTMENT
        </div>
        <div
          style={{
            ...headerStyle,
            width: COL_WIDTH,
            color: HEADER_PATCHING_COLOR,
            opacity: 0.7,
          }}
        >
          PATCHING
        </div>
        <div
          style={{
            ...headerStyle,
            width: COL_WIDTH,
            color: HEADER_PDD_COLOR,
            opacity: 0.7,
          }}
        >
          PDD
        </div>
      </div>

      {/* Header underline */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 40,
          width: tableWidth * underlineProgress,
          height: 2,
          backgroundColor: BORDER_COLOR,
          opacity: 0.5,
        }}
      />
    </div>
  );
};

// ── Main Component ──────────────────────────────────────────────────
export const Part5CompoundReturns05InvestmentComparisonTable: React.FC = () => {
  // Row vertical positions: after header (TABLE_TOP + 40 header + 2 underline + gap)
  const firstRowY = HEADER_UNDERLINE_Y + 12;
  const row1Y = firstRowY;
  const row2Y = firstRowY + ROW_HEIGHT;
  const row3Y = firstRowY + ROW_HEIGHT * 2;

  // Glow sweep region covers PDD column across all rows
  const glowRegionX = TABLE_LEFT + COL_WIDTH * 2;
  const glowRegionY = firstRowY;
  const glowRegionHeight = ROW_HEIGHT * 3;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* Table Header */}
      <Sequence from={0} durationInFrames={270}>
        <TableHeader />
      </Sequence>

      {/* Row 1: Fix a bug */}
      <Sequence from={ROW1_START} durationInFrames={270 - ROW1_START}>
        <AnimatedTableRow rowData={TABLE_ROWS[0]} rowY={row1Y} />
      </Sequence>

      {/* Row 2: Improve code */}
      <Sequence from={ROW2_START} durationInFrames={270 - ROW2_START}>
        <AnimatedTableRow rowData={TABLE_ROWS[1]} rowY={row2Y} />
      </Sequence>

      {/* Row 3: Document intent */}
      <Sequence from={ROW3_START} durationInFrames={270 - ROW3_START}>
        <AnimatedTableRow rowData={TABLE_ROWS[2]} rowY={row3Y} />
      </Sequence>

      {/* PDD column glow sweep */}
      <Sequence from={GLOW_START} durationInFrames={270 - GLOW_START}>
        <GlowSweep
          regionX={glowRegionX}
          regionY={glowRegionY}
          regionWidth={COL_WIDTH}
          regionHeight={glowRegionHeight}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns05InvestmentComparisonTable;
