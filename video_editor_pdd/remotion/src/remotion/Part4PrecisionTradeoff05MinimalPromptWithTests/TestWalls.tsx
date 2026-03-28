import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  BLUE_ACCENT,
  EDITOR_X,
  EDITOR_Y,
  EDITOR_WIDTH,
  EDITOR_HEIGHT,
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_WIDTH,
  WALL_COUNT,
  WALL_DRAW_DURATION,
  WALL_STAGGER,
  WALLS_START,
} from "./constants";

/**
 * Generates wall line endpoints connecting terminal area to prompt editor area.
 * Lines radiate from the terminal perimeter toward the editor perimeter.
 */
function getWallLines(count: number) {
  const lines: Array<{
    x1: number;
    y1: number;
    x2: number;
    y2: number;
  }> = [];

  const editorBottom = EDITOR_Y + EDITOR_HEIGHT;
  const terminalTop = TERMINAL_Y;

  // Distribute lines across the width, some on left side, some on right, some center
  for (let i = 0; i < count; i++) {
    const t = count === 1 ? 0.5 : i / (count - 1);

    // Source points along terminal top edge
    const srcX = TERMINAL_X + 40 + t * (TERMINAL_WIDTH - 80);
    const srcY = terminalTop;

    // Target points along editor bottom edge + sides
    let tgtX: number;
    let tgtY: number;

    if (i < 2) {
      // Left side walls
      tgtX = EDITOR_X;
      tgtY = editorBottom - 20 - i * 60;
    } else if (i >= count - 2) {
      // Right side walls
      tgtX = EDITOR_X + EDITOR_WIDTH;
      tgtY = editorBottom - 20 - (count - 1 - i) * 60;
    } else {
      // Bottom edge walls
      const innerT = (i - 2) / (count - 5);
      tgtX = EDITOR_X + 30 + innerT * (EDITOR_WIDTH - 60);
      tgtY = editorBottom;
    }

    lines.push({ x1: srcX, y1: srcY, x2: tgtX, y2: tgtY });
  }

  return lines;
}

export const TestWalls: React.FC = () => {
  const frame = useCurrentFrame();
  const lines = getWallLines(WALL_COUNT);

  return (
    <svg
      width={1920}
      height={1080}
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        pointerEvents: "none",
      }}
    >
      <defs>
        <filter id="wallGlow">
          <feGaussianBlur stdDeviation="3" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
      {lines.map((line, i) => {
        const lineStart = WALLS_START + i * WALL_STAGGER;
        const lineEnd = lineStart + WALL_DRAW_DURATION;

        const drawProgress = interpolate(
          frame,
          [lineStart, lineEnd],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        // Glow pulse after draw completes
        const pulseProgress = interpolate(
          frame,
          [lineEnd, lineEnd + 10],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        );

        if (drawProgress <= 0) return null;

        // Interpolate from source to target based on draw progress
        const currentX2 = line.x1 + (line.x2 - line.x1) * drawProgress;
        const currentY2 = line.y1 + (line.y2 - line.y1) * drawProgress;

        const glowOpacity = 0.15 + pulseProgress * 0.2;
        const lineOpacity = 0.4;

        return (
          <g key={i}>
            {/* Glow line */}
            <line
              x1={line.x1}
              y1={line.y1}
              x2={currentX2}
              y2={currentY2}
              stroke={BLUE_ACCENT}
              strokeWidth={6}
              strokeOpacity={glowOpacity}
              filter="url(#wallGlow)"
            />
            {/* Main line */}
            <line
              x1={line.x1}
              y1={line.y1}
              x2={currentX2}
              y2={currentY2}
              stroke={BLUE_ACCENT}
              strokeWidth={2}
              strokeOpacity={lineOpacity}
            />
          </g>
        );
      })}
    </svg>
  );
};

export default TestWalls;
