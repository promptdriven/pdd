import React from "react";
import {
  CANVAS_W,
  CANVAS_H,
  GRID_SPACING,
  GRID_COLOR,
  GRID_OPACITY,
} from "./constants";

/**
 * Faint drafting grid background — engineering diagram aesthetic.
 */
export const DraftGrid: React.FC = () => {
  const cols = Math.ceil(CANVAS_W / GRID_SPACING);
  const rows = Math.ceil(CANVAS_H / GRID_SPACING);

  return (
    <svg
      width={CANVAS_W}
      height={CANVAS_H}
      viewBox={`0 0 ${CANVAS_W} ${CANVAS_H}`}
      style={{ position: "absolute", left: 0, top: 0 }}
    >
      {/* Vertical lines */}
      {Array.from({ length: cols + 1 }, (_, i) => (
        <line
          key={`v${i}`}
          x1={i * GRID_SPACING}
          y1={0}
          x2={i * GRID_SPACING}
          y2={CANVAS_H}
          stroke={GRID_COLOR}
          strokeWidth={1}
          strokeOpacity={GRID_OPACITY}
        />
      ))}
      {/* Horizontal lines */}
      {Array.from({ length: rows + 1 }, (_, i) => (
        <line
          key={`h${i}`}
          x1={0}
          y1={i * GRID_SPACING}
          x2={CANVAS_W}
          y2={i * GRID_SPACING}
          stroke={GRID_COLOR}
          strokeWidth={1}
          strokeOpacity={GRID_OPACITY}
        />
      ))}
    </svg>
  );
};

export default DraftGrid;
