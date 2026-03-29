import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
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
  WALL_STAGGER,
  WALL_DRAW_DURATION,
  WALLS_START,
} from './constants';

interface WallLine {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

function generateWallLines(): WallLine[] {
  const lines: WallLine[] = [];
  const termCenterX = TERMINAL_X + TERMINAL_WIDTH / 2;
  const termTopY = TERMINAL_Y;
  const editorCenterX = EDITOR_X + EDITOR_WIDTH / 2;
  const editorBottom = EDITOR_Y + EDITOR_HEIGHT;

  // Lines from terminal top area reaching up to frame the editor
  for (let i = 0; i < WALL_COUNT; i++) {
    const t = i / (WALL_COUNT - 1); // 0 to 1
    // Spread across the width of the terminal/editor
    const spreadX = EDITOR_X + t * EDITOR_WIDTH;

    // Source: spread along top of terminal
    const srcX = TERMINAL_X + t * TERMINAL_WIDTH;
    const srcY = termTopY;

    // Destination: frame the editor — some go to bottom, some to sides
    let dstX: number;
    let dstY: number;

    if (i < 3) {
      // Left side framing
      dstX = EDITOR_X - 10;
      dstY = editorBottom - (2 - i) * 60;
    } else if (i >= WALL_COUNT - 3) {
      // Right side framing
      dstX = EDITOR_X + EDITOR_WIDTH + 10;
      dstY = editorBottom - (i - (WALL_COUNT - 3)) * 60;
    } else {
      // Bottom framing
      dstX = spreadX;
      dstY = editorBottom + 10;
    }

    lines.push({ x1: srcX, y1: srcY, x2: dstX, y2: dstY });
  }

  return lines;
}

const wallLines = generateWallLines();

export const TestWalls: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={1920}
      height={1080}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        pointerEvents: 'none',
      }}
    >
      {wallLines.map((line, i) => {
        const lineStart = i * WALL_STAGGER;
        const progress = interpolate(
          frame,
          [lineStart, lineStart + WALL_DRAW_DURATION],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

        // Glow pulse after draw completes
        const pulseStart = lineStart + WALL_DRAW_DURATION;
        const pulseOpacity = interpolate(
          frame,
          [pulseStart, pulseStart + 10],
          [0.4, 0.15],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        const currentX2 = line.x1 + (line.x2 - line.x1) * progress;
        const currentY2 = line.y1 + (line.y2 - line.y1) * progress;

        if (progress <= 0) return null;

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
              opacity={pulseOpacity > 0.15 ? pulseOpacity : 0.15}
              style={{ filter: 'blur(3px)' }}
            />
            {/* Main line */}
            <line
              x1={line.x1}
              y1={line.y1}
              x2={currentX2}
              y2={currentY2}
              stroke={BLUE_ACCENT}
              strokeWidth={2}
              opacity={0.4}
            />
          </g>
        );
      })}
    </svg>
  );
};
