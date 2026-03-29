// TableRow.tsx — Animated table row with accent border and slide-in
import React from "react";
import { interpolate, Easing } from "remotion";
import {
  TABLE_CENTER_X,
  TABLE_WIDTH,
  ROW_HEIGHT,
  CELL_PADDING_H,
  ACCENT_BORDER_WIDTH,
  ROW_BG,
  ROW_BORDER_COLOR,
  ROW_BORDER_WIDTH,
  COLUMN_WIDTHS,
  FONT_FAMILY,
  COMPONENT_FONT_SIZE,
  COMPONENT_FONT_WEIGHT,
  VALUE_FONT_SIZE,
  VALUE_FONT_WEIGHT,
  PARENTHETICAL_FONT_SIZE,
  PARENTHETICAL_TEXT_COLOR,
  VALUE_TEXT_COLOR,
  OWNER_TEXT_COLOR,
  ROW_SLIDE_DURATION,
  ROW_SLIDE_DISTANCE,
  TESTS_GLOW_DURATION,
} from "./constants";
import type { TableRowData } from "./constants";

interface TableRowProps {
  row: TableRowData;
  topY: number;
  /** Frame offset within this row's Sequence (starts at 0) */
  localFrame: number;
  isTestsRow: boolean;
}

const TableRow: React.FC<TableRowProps> = ({
  row,
  topY,
  localFrame,
  isTestsRow,
}) => {
  // Slide from left
  const translateX = interpolate(
    localFrame,
    [0, ROW_SLIDE_DURATION],
    [-ROW_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const opacity = interpolate(localFrame, [0, ROW_SLIDE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Tests row glow effect — ramp up then fade
  let glowBoxShadow = "none";
  if (isTestsRow) {
    const peakFrame = ROW_SLIDE_DURATION + TESTS_GLOW_DURATION;
    const fadeEndFrame = peakFrame + 20;
    const glowAlpha = interpolate(
      localFrame,
      [ROW_SLIDE_DURATION, peakFrame, fadeEndFrame],
      [0, 0.3, 0.05],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      }
    );
    glowBoxShadow = `0 0 20px rgba(74, 144, 217, ${glowAlpha})`;
  }

  return (
    <div
      style={{
        position: "absolute",
        left: TABLE_CENTER_X,
        top: topY,
        width: TABLE_WIDTH,
        height: ROW_HEIGHT,
        display: "flex",
        flexDirection: "row",
        alignItems: "center",
        backgroundColor: ROW_BG,
        borderBottom: `${ROW_BORDER_WIDTH}px solid ${ROW_BORDER_COLOR}`,
        borderLeft: `${ACCENT_BORDER_WIDTH}px solid ${row.color}`,
        opacity,
        transform: `translateX(${translateX}px)`,
        boxShadow: glowBoxShadow,
      }}
    >
      {/* Component name column */}
      <div
        style={{
          width: COLUMN_WIDTHS[0],
          paddingLeft: CELL_PADDING_H,
          paddingRight: CELL_PADDING_H,
          fontFamily: FONT_FAMILY,
          fontSize: COMPONENT_FONT_SIZE,
          fontWeight: COMPONENT_FONT_WEIGHT,
          color: row.color,
        }}
      >
        {row.component}
      </div>

      {/* Encodes column */}
      <div
        style={{
          width: COLUMN_WIDTHS[1],
          paddingLeft: CELL_PADDING_H,
          paddingRight: CELL_PADDING_H,
          fontFamily: FONT_FAMILY,
          fontSize: VALUE_FONT_SIZE,
          fontWeight: VALUE_FONT_WEIGHT,
          color: VALUE_TEXT_COLOR,
        }}
      >
        {row.encodes}
        {row.parenthetical ? (
          <span
            style={{
              fontSize: PARENTHETICAL_FONT_SIZE,
              color: PARENTHETICAL_TEXT_COLOR,
              marginLeft: 6,
            }}
          >
            {row.parenthetical}
          </span>
        ) : null}
      </div>

      {/* Owner column */}
      <div
        style={{
          width: COLUMN_WIDTHS[2],
          paddingLeft: CELL_PADDING_H,
          paddingRight: CELL_PADDING_H,
          fontFamily: FONT_FAMILY,
          fontSize: VALUE_FONT_SIZE,
          fontWeight: VALUE_FONT_WEIGHT,
          color: OWNER_TEXT_COLOR,
        }}
      >
        {row.owner}
      </div>
    </div>
  );
};

export default TableRow;
