import React from 'react';
import { MOLD, COLORS } from './constants';

/**
 * Renders the injection mold cross-section with animated wall drawing
 * and a funnel nozzle at the top.
 */
export const MoldCrossSection: React.FC<{
  wallDrawProgress: number;
}> = ({ wallDrawProgress }) => {
  const { width, height, wallWidth, centerX, centerY } = MOLD;

  const left = centerX - width / 2;
  const top = centerY - height / 2;
  const right = left + width;
  const bottom = top + height;

  // Wall segments: left, bottom, right, top-left gap, top-right gap (opening at top center)
  const gapWidth = 60; // nozzle opening
  const halfGap = gapWidth / 2;
  const midX = centerX;

  // Total perimeter for animation
  // We draw walls progressively: left wall, bottom wall, right wall, top walls (with gap)
  const wallSegments = [
    // Left wall (top to bottom)
    { x1: left, y1: top, x2: left, y2: bottom },
    // Bottom wall (left to right)
    { x1: left, y1: bottom, x2: right, y2: bottom },
    // Right wall (bottom to top)
    { x1: right, y1: bottom, x2: right, y2: top },
    // Top-left wall segment
    { x1: left, y1: top, x2: midX - halfGap, y2: top },
    // Top-right wall segment
    { x1: midX + halfGap, y1: top, x2: right, y2: top },
  ];

  const segmentCount = wallSegments.length;

  return (
    <svg
      width={958}
      height={860}
      style={{ position: 'absolute', top: 60, left: 0 }}
    >
      {/* Mold walls */}
      {wallSegments.map((seg, i) => {
        const segProgress = Math.max(
          0,
          Math.min(1, wallDrawProgress * segmentCount - i)
        );
        if (segProgress <= 0) return null;

        const dx = seg.x2 - seg.x1;
        const dy = seg.y2 - seg.y1;

        return (
          <line
            key={`wall-${i}`}
            x1={seg.x1}
            y1={seg.y1}
            x2={seg.x1 + dx * segProgress}
            y2={seg.y1 + dy * segProgress}
            stroke={COLORS.wallColor}
            strokeWidth={wallWidth}
            strokeOpacity={0.8}
            strokeLinecap="round"
          />
        );
      })}

      {/* Wall labels (appear after walls are drawn) */}
      {wallDrawProgress >= 1 && (
        <>
          {/* Left wall label */}
          <text
            x={left - 14}
            y={centerY}
            fill={COLORS.wallColor}
            opacity={0.4}
            fontSize={8}
            fontFamily="Inter, sans-serif"
            fontWeight={600}
            textAnchor="middle"
            transform={`rotate(-90, ${left - 14}, ${centerY})`}
          >
            WALL
          </text>
          {/* Right wall label */}
          <text
            x={right + 14}
            y={centerY}
            fill={COLORS.wallColor}
            opacity={0.4}
            fontSize={8}
            fontFamily="Inter, sans-serif"
            fontWeight={600}
            textAnchor="middle"
            transform={`rotate(90, ${right + 14}, ${centerY})`}
          >
            WALL
          </text>
          {/* Bottom wall label */}
          <text
            x={centerX}
            y={bottom + 16}
            fill={COLORS.wallColor}
            opacity={0.4}
            fontSize={8}
            fontFamily="Inter, sans-serif"
            fontWeight={600}
            textAnchor="middle"
          >
            WALL
          </text>
          {/* Top wall label (split) */}
          <text
            x={left + (midX - halfGap - left) / 2}
            y={top - 8}
            fill={COLORS.wallColor}
            opacity={0.4}
            fontSize={8}
            fontFamily="Inter, sans-serif"
            fontWeight={600}
            textAnchor="middle"
          >
            WALL
          </text>
        </>
      )}

      {/* Nozzle funnel at top center */}
      <polygon
        points={`${midX - 20},${top - 30} ${midX + 20},${top - 30} ${midX + halfGap / 2},${top - 2} ${midX - halfGap / 2},${top - 2}`}
        fill={COLORS.moldNozzle}
        opacity={0.5 * wallDrawProgress}
      />
    </svg>
  );
};
