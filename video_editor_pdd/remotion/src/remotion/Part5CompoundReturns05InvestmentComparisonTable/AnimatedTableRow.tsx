import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TABLE_LEFT,
  COL_WIDTH,
  ROW_HEIGHT,
  ROW_SLIDE_DURATION,
  ROW_SLIDE_DISTANCE,
  CELL_FONT_SIZE,
  CELL_REGULAR_WEIGHT,
  CELL_BOLD_WEIGHT,
  CELL_INVESTMENT_COLOR,
  CELL_PATCHING_COLOR,
  CELL_PDD_COLOR,
  BORDER_COLOR,
} from "./constants";
import type { TableRowData } from "./constants";

interface AnimatedTableRowProps {
  rowData: TableRowData;
  rowY: number;
}

export const AnimatedTableRow: React.FC<AnimatedTableRowProps> = ({
  rowData,
  rowY,
}) => {
  const frame = useCurrentFrame();

  // Slide in from left
  const translateX = interpolate(frame, [0, ROW_SLIDE_DURATION], [-ROW_SLIDE_DISTANCE, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Fade in
  const opacity = interpolate(frame, [0, ROW_SLIDE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // PDD emphasis scale — easeOut(back) from 1.02 to 1.0
  const pddScale = interpolate(
    frame,
    [0, ROW_SLIDE_DURATION, ROW_SLIDE_DURATION + 10],
    [1.02, 1.02, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  const cellBase: React.CSSProperties = {
    height: ROW_HEIGHT,
    display: "flex",
    alignItems: "center",
    paddingLeft: 24,
    paddingRight: 16,
    fontFamily: "Inter, sans-serif",
    fontSize: CELL_FONT_SIZE,
    lineHeight: "1.4",
    boxSizing: "border-box",
  };

  return (
    <div
      style={{
        position: "absolute",
        left: TABLE_LEFT,
        top: rowY,
        width: COL_WIDTH * 3,
        display: "flex",
        flexDirection: "row",
        opacity,
        transform: `translateX(${translateX}px)`,
        borderBottom: `1px solid ${BORDER_COLOR}4D`, // 0.3 opacity
      }}
    >
      {/* Investment column */}
      <div
        style={{
          ...cellBase,
          width: COL_WIDTH,
          color: CELL_INVESTMENT_COLOR,
          fontWeight: CELL_REGULAR_WEIGHT,
        }}
      >
        {rowData.investment}
      </div>

      {/* Patching column */}
      <div
        style={{
          ...cellBase,
          width: COL_WIDTH,
          color: CELL_PATCHING_COLOR,
          fontWeight: CELL_REGULAR_WEIGHT,
          opacity: 0.8,
        }}
      >
        {rowData.patching}
      </div>

      {/* PDD column */}
      <div
        style={{
          ...cellBase,
          width: COL_WIDTH,
          color: CELL_PDD_COLOR,
          fontWeight: CELL_BOLD_WEIGHT,
          transform: `scale(${pddScale})`,
          transformOrigin: "left center",
        }}
      >
        {rowData.pdd}
      </div>
    </div>
  );
};
