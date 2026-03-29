// Part3MoldParts17ComponentTable.tsx — Main component
import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BACKGROUND_COLOR,
  TABLE_CENTER_X,
  TABLE_WIDTH,
  TABLE_TOP_Y,
  HEADER_HEIGHT,
  ROW_HEIGHT,
  COLUMN_WIDTHS,
  CELL_PADDING_H,
  HEADER_BG,
  HEADER_BORDER_COLOR,
  HEADER_BORDER_WIDTH,
  HEADER_TEXT_COLOR,
  FONT_FAMILY,
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  HEADER_LETTER_SPACING,
  TABLE_ROWS,
  HEADER_COLUMNS,
  HEADER_FADE_START,
  HEADER_FADE_DURATION,
  ROW_SLIDE_START_BASE,
  ROW_SLIDE_INTERVAL,
} from "./constants";
import TableRow from "./TableRow";
import HierarchyText from "./HierarchyText";

export const defaultPart3MoldParts17ComponentTableProps = {};

export const Part3MoldParts17ComponentTable: React.FC = () => {
  const frame = useCurrentFrame();

  // Header fade-in
  const headerOpacity = interpolate(
    frame,
    [HEADER_FADE_START, HEADER_FADE_START + HEADER_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Table header */}
      <div
        style={{
          position: "absolute",
          left: TABLE_CENTER_X,
          top: TABLE_TOP_Y,
          width: TABLE_WIDTH,
          height: HEADER_HEIGHT,
          display: "flex",
          flexDirection: "row",
          alignItems: "center",
          backgroundColor: HEADER_BG,
          borderBottom: `${HEADER_BORDER_WIDTH}px solid ${HEADER_BORDER_COLOR}`,
          opacity: headerOpacity,
        }}
      >
        {HEADER_COLUMNS.map((col, i) => (
          <div
            key={col}
            style={{
              width: COLUMN_WIDTHS[i],
              paddingLeft: CELL_PADDING_H,
              paddingRight: CELL_PADDING_H,
              fontFamily: FONT_FAMILY,
              fontSize: HEADER_FONT_SIZE,
              fontWeight: HEADER_FONT_WEIGHT,
              color: HEADER_TEXT_COLOR,
              textTransform: "uppercase",
              letterSpacing: HEADER_LETTER_SPACING,
            }}
          >
            {col}
          </div>
        ))}
      </div>

      {/* Table rows — each slides in with staggered timing */}
      {TABLE_ROWS.map((row, i) => {
        const rowStart = ROW_SLIDE_START_BASE + i * ROW_SLIDE_INTERVAL;
        const rowTopY = TABLE_TOP_Y + HEADER_HEIGHT + i * ROW_HEIGHT;
        const localFrame = Math.max(0, frame - rowStart);
        const isVisible = frame >= rowStart;

        if (!isVisible) return null;

        return (
          <TableRow
            key={row.component}
            row={row}
            topY={rowTopY}
            localFrame={localFrame}
            isTestsRow={row.component === "Tests"}
          />
        );
      })}

      {/* Hierarchy text and subtext */}
      <HierarchyText absoluteFrame={frame} />
    </AbsoluteFill>
  );
};

export default Part3MoldParts17ComponentTable;
