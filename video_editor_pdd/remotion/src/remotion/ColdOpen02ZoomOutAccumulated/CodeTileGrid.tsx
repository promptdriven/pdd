import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GRID_ROWS,
  GRID_COLS,
  TILE_WIDTH,
  TILE_HEIGHT,
  TILE_GAP,
  TILE_PADDING,
  TILE_BG,
  TILE_BORDER_RADIUS,
  DIFF_MARKER_WIDTH,
  DIFF_GREEN,
  DIFF_RED,
  DIFF_MARKER_PERCENT,
  TILE_STAGGER_FRAMES,
  TODO_COLOR,
  TODO_OPACITY,
  TODO_FONT_SIZE,
  COMMENT_COLOR,
  COMMENT_FONT_SIZE,
  SYNTAX_KEYWORD,
  SYNTAX_STRING,
  SYNTAX_FUNCTION,
  SYNTAX_OPERATOR,
  ZOOM_START_FRAME,
  INLINE_COMMENTS,
} from "./constants";

// Deterministic pseudo-random based on index
const pseudoRandom = (seed: number): number => {
  const x = Math.sin(seed * 127.1 + 311.7) * 43758.5453;
  return x - Math.floor(x);
};

const CodeTile: React.FC<{
  row: number;
  col: number;
  index: number;
  revealProgress: number;
}> = ({ row, col, index, revealProgress }) => {
  const frame = useCurrentFrame();
  const staggerDelay = row * TILE_STAGGER_FRAMES;
  const tileProgress = interpolate(
    revealProgress,
    [staggerDelay / 105, Math.min(1, (staggerDelay + 30) / 105)],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const tileOpacity = tileProgress;
  const rand = pseudoRandom(index);
  const hasDiff = rand < DIFF_MARKER_PERCENT;
  const diffColor = pseudoRandom(index + 100) > 0.5 ? DIFF_GREEN : DIFF_RED;
  const hasTodo = pseudoRandom(index + 200) < 0.15;
  const commentIndex = Math.floor(pseudoRandom(index + 300) * INLINE_COMMENTS.length);
  const hasComment = pseudoRandom(index + 400) < 0.4;

  // Skip center tile area (that's the initial code block)
  const centerRow = Math.floor(GRID_ROWS / 2);
  const centerCol = Math.floor(GRID_COLS / 2);
  const isCenter = row >= centerRow - 1 && row <= centerRow && col >= centerCol - 1 && col <= centerCol;

  const totalGridWidth = GRID_COLS * (TILE_WIDTH + TILE_GAP) - TILE_GAP;
  const totalGridHeight = GRID_ROWS * (TILE_HEIGHT + TILE_GAP) - TILE_GAP;
  const offsetX = (958 - totalGridWidth) / 2;
  const offsetY = (1080 - totalGridHeight) / 2;

  const x = offsetX + col * (TILE_WIDTH + TILE_GAP);
  const y = offsetY + row * (TILE_HEIGHT + TILE_GAP);

  // TODO badge pop-in with back easing
  const todoPopIn = hasTodo
    ? interpolate(
        frame,
        [ZOOM_START_FRAME + staggerDelay + 20, ZOOM_START_FRAME + staggerDelay + 35],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  // Generate fake code lines
  const lineCount = 3 + Math.floor(pseudoRandom(index + 500) * 3);
  const codeLines = Array.from({ length: lineCount }, (_, i) => {
    const lineWidth = 30 + pseudoRandom(index * 10 + i) * 60;
    return lineWidth;
  });

  if (isCenter) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: TILE_WIDTH,
        height: TILE_HEIGHT,
        backgroundColor: TILE_BG,
        borderRadius: TILE_BORDER_RADIUS,
        opacity: tileOpacity,
        overflow: "hidden",
        padding: TILE_PADDING,
      }}
    >
      {/* Diff marker */}
      {hasDiff && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: 0,
            width: DIFF_MARKER_WIDTH,
            height: "100%",
            backgroundColor: diffColor,
            opacity: 0.7,
          }}
        />
      )}

      {/* Fake code lines */}
      {codeLines.map((width, i) => {
        const colors = [SYNTAX_KEYWORD, SYNTAX_STRING, SYNTAX_FUNCTION, SYNTAX_OPERATOR];
        const color = colors[Math.floor(pseudoRandom(index * 100 + i) * colors.length)];
        return (
          <div
            key={i}
            style={{
              width: `${width}%`,
              height: 3,
              backgroundColor: color,
              opacity: 0.4,
              marginBottom: 4,
              marginLeft: hasDiff ? DIFF_MARKER_WIDTH + 2 : 0,
              borderRadius: 1,
            }}
          />
        );
      })}

      {/* Inline comment */}
      {hasComment && (
        <div
          style={{
            position: "absolute",
            bottom: 4,
            left: TILE_PADDING,
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: COMMENT_FONT_SIZE,
            color: COMMENT_COLOR,
            opacity: tileOpacity * 0.5,
            whiteSpace: "nowrap",
          }}
        >
          {INLINE_COMMENTS[commentIndex]}
        </div>
      )}

      {/* TODO badge */}
      {hasTodo && (
        <div
          style={{
            position: "absolute",
            top: 4,
            right: 4,
            backgroundColor: TODO_COLOR,
            opacity: TODO_OPACITY * todoPopIn,
            color: "#FFFFFF",
            fontFamily: "'Inter', sans-serif",
            fontSize: TODO_FONT_SIZE,
            fontWeight: 700,
            padding: "1px 4px",
            borderRadius: 2,
            transform: `scale(${interpolate(todoPopIn, [0, 1], [0.5, 1])})`,
          }}
        >
          TODO
        </div>
      )}
    </div>
  );
};

export const CodeTileGrid: React.FC<{ revealProgress: number }> = ({
  revealProgress,
}) => {
  const tiles: React.ReactNode[] = [];
  for (let row = 0; row < GRID_ROWS; row++) {
    for (let col = 0; col < GRID_COLS; col++) {
      const index = row * GRID_COLS + col;
      tiles.push(
        <CodeTile
          key={index}
          row={row}
          col={col}
          index={index}
          revealProgress={revealProgress}
        />
      );
    }
  }

  return <>{tiles}</>;
};
