import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TABLE_X,
  TABLE_Y,
  TABLE_WIDTH,
  TABLE_ROW_HEIGHT,
  COL_WIDTHS,
  TABLE_BORDER_RADIUS,
  TABLE_BG,
  TABLE_HEADER_BG,
  DIVIDER_COLOR,
  TEXT_SECONDARY,
  TEXT_PRIMARY,
  AMBER,
  TABLE_ROWS,
  TIMING,
} from "./constants";

const HEADER_HEIGHT = 50;
const HEADERS = ["COMPONENT", "ENCODES", "OWNER"];

// Row appearance start frames (relative to component mount, not global)
const ROW_APPEAR_FRAMES = [
  TIMING.row1Start,
  TIMING.row2Start,
  TIMING.row3Start,
];

export const SummaryTable: React.FC = () => {
  const frame = useCurrentFrame();

  // Table container fade-in (frames 60-80 global → 0-20 relative to sequence from=60)
  // We use global frame since this component receives it directly
  const tableBgOpacity = interpolate(
    frame,
    [TIMING.moldSlideStart, TIMING.moldSlideStart + 20],
    [0, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Header text opacity (frames 120-150)
  const headerOpacity = interpolate(
    frame,
    [TIMING.tableHeaderStart, TIMING.tableHeaderStart + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Divider draw progress (frames 150-180)
  const dividerProgress = interpolate(
    frame,
    [150, 180],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  // Tests row pulse (starts at conflict line, frame 310)
  const testsPulse =
    frame >= TIMING.conflictStart
      ? interpolate(
          (frame - TIMING.conflictStart) % 30,
          [0, 15, 30],
          [0.5, 0.9, 0.5],
          { extrapolateRight: "clamp" }
        )
      : 0.5;

  const totalHeight = HEADER_HEIGHT + TABLE_ROWS.length * TABLE_ROW_HEIGHT + 20;

  return (
    <div
      style={{
        position: "absolute",
        left: TABLE_X,
        top: TABLE_Y,
        width: TABLE_WIDTH,
        height: totalHeight,
        backgroundColor: TABLE_BG,
        opacity: tableBgOpacity > 0 ? 1 : 0,
        borderRadius: TABLE_BORDER_RADIUS,
        overflow: "hidden",
      }}
    >
      {/* Table background with opacity */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundColor: TABLE_BG,
          opacity: tableBgOpacity,
          borderRadius: TABLE_BORDER_RADIUS,
        }}
      />

      {/* Header row */}
      <div
        style={{
          position: "relative",
          display: "flex",
          height: HEADER_HEIGHT,
          backgroundColor: TABLE_HEADER_BG,
          opacity: headerOpacity,
          alignItems: "center",
          paddingLeft: 20,
        }}
      >
        {HEADERS.map((header, i) => (
          <div
            key={header}
            style={{
              width: COL_WIDTHS[i],
              fontFamily: "Inter, sans-serif",
              fontSize: 12,
              fontWeight: 600,
              color: TEXT_SECONDARY,
              letterSpacing: 2,
              textTransform: "uppercase",
            }}
          >
            {header}
          </div>
        ))}
      </div>

      {/* Header divider */}
      <div
        style={{
          position: "relative",
          height: 1,
          backgroundColor: DIVIDER_COLOR,
          opacity: 0.2,
          transform: `scaleX(${dividerProgress})`,
          transformOrigin: "left",
        }}
      />

      {/* Data rows */}
      {TABLE_ROWS.map((row, i) => {
        const appearStart = ROW_APPEAR_FRAMES[i];
        const duration = row.bold ? 25 : 20; // Tests row is slower

        const rowOpacity = interpolate(
          frame,
          [appearStart, appearStart + duration],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
        );

        const rowSlideX = interpolate(
          frame,
          [appearStart, appearStart + duration],
          [30, 0],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
        );

        const isTests = row.bold;
        const accentOpacity = isTests ? testsPulse : 0.5;

        return (
          <div key={row.component}>
            <div
              style={{
                position: "relative",
                display: "flex",
                height: TABLE_ROW_HEIGHT,
                alignItems: "center",
                paddingLeft: 20,
                opacity: rowOpacity,
                transform: `translateX(${rowSlideX}px)`,
                backgroundColor: isTests
                  ? `${AMBER}0A` // ~0.04 opacity amber wash
                  : "transparent",
              }}
            >
              {/* Left accent border */}
              <div
                style={{
                  position: "absolute",
                  left: 0,
                  top: 0,
                  bottom: 0,
                  width: row.accentWidth,
                  backgroundColor: row.color,
                  opacity: accentOpacity,
                }}
              />

              {/* Component name with color dot */}
              <div
                style={{
                  width: COL_WIDTHS[0],
                  display: "flex",
                  alignItems: "center",
                  gap: 10,
                }}
              >
                <div
                  style={{
                    width: 10,
                    height: 10,
                    borderRadius: "50%",
                    backgroundColor: row.color,
                    boxShadow: `0 0 8px ${row.color}80`,
                  }}
                />
                <span
                  style={{
                    fontFamily: "Inter, sans-serif",
                    fontSize: 18,
                    fontWeight: row.bold ? 700 : 600,
                    color: row.color,
                  }}
                >
                  {row.component}
                </span>
              </div>

              {/* Encodes */}
              <div
                style={{
                  width: COL_WIDTHS[1],
                  fontFamily: "Inter, sans-serif",
                  fontSize: 16,
                  fontWeight: row.bold ? 700 : 400,
                  color: TEXT_PRIMARY,
                  opacity: 0.8,
                }}
              >
                {row.encodes}
              </div>

              {/* Owner */}
              <div
                style={{
                  width: COL_WIDTHS[2],
                  fontFamily: "Inter, sans-serif",
                  fontSize: 14,
                  color: TEXT_SECONDARY,
                  opacity: 0.6,
                }}
              >
                {row.owner}
              </div>
            </div>

            {/* Row divider */}
            {i < TABLE_ROWS.length - 1 && (
              <div
                style={{
                  height: 1,
                  backgroundColor: DIVIDER_COLOR,
                  opacity: 0.2 * rowOpacity,
                }}
              />
            )}
          </div>
        );
      })}
    </div>
  );
};
