import React from "react";
import { interpolate } from "remotion";
import { COLORS, FILE_GRID, BEATS } from "./constants";

/**
 * Renders the grid of file rectangles representing the codebase.
 * Files fade in progressively as the zoom reveals them.
 */
export const FileGrid: React.FC<{ frame: number }> = ({ frame }) => {
  // Files become visible as zoom progresses
  const gridOpacity = interpolate(
    frame,
    [BEATS.TRANSITION_END - 20, BEATS.TRANSITION_END + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (gridOpacity <= 0) return null;

  return (
    <g opacity={gridOpacity}>
      {FILE_GRID.map((file, i) => {
        // Stagger appearance: files further from center appear later
        const dist = Math.sqrt(
          Math.pow(file.x - 3000, 2) + Math.pow(file.y - 1688, 2)
        );
        const staggerDelay = (dist / 4000) * 40;
        const fileOpacity = interpolate(
          frame,
          [
            BEATS.TRANSITION_END + staggerDelay,
            BEATS.TRANSITION_END + staggerDelay + 20,
          ],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        );

        return (
          <rect
            key={i}
            x={file.x}
            y={file.y}
            width={file.w}
            height={file.h}
            rx={3}
            fill={file.isActive ? COLORS.FILE_ACTIVE : COLORS.FILE_DEFAULT}
            stroke={
              file.isActive ? COLORS.FILE_ACTIVE_BORDER : COLORS.FILE_BORDER
            }
            strokeWidth={file.isActive ? 2 : 1}
            opacity={fileOpacity}
          />
        );
      })}
    </g>
  );
};
