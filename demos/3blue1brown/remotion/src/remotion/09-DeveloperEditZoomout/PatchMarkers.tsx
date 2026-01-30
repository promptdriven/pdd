import React from "react";
import { interpolate, Easing } from "remotion";
import { COLORS, FILE_GRID, BEATS } from "./constants";

/**
 * Yellow/orange patch markers on files that have been previously edited.
 * Appear in a staggered wave during the patches phase.
 */
export const PatchMarkers: React.FC<{ frame: number }> = ({ frame }) => {
  if (frame < BEATS.PATCHES_START - 10) return null;

  const patchedFiles = FILE_GRID.filter((f) => f.hasPatch && !f.isActive);

  return (
    <g>
      {patchedFiles.map((file, i) => {
        // Stagger: each patch appears at a different time within the phase
        const staggerOffset = (i / patchedFiles.length) * 50;
        const patchOpacity = interpolate(
          frame,
          [
            BEATS.PATCHES_START + staggerOffset,
            BEATS.PATCHES_START + staggerOffset + 12,
          ],
          [0, 0.85],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        if (patchOpacity <= 0) return null;

        // Small yellow/orange marker on the file
        const markerW = Math.min(file.w * 0.4, 28);
        const markerH = Math.min(file.h * 0.35, 12);
        const isOrange = i % 3 === 0;

        return (
          <rect
            key={i}
            x={file.x + file.w - markerW - 4}
            y={file.y + 4}
            width={markerW}
            height={markerH}
            rx={2}
            fill={isOrange ? COLORS.PATCH_ORANGE : COLORS.PATCH_YELLOW}
            opacity={patchOpacity}
          />
        );
      })}
    </g>
  );
};
