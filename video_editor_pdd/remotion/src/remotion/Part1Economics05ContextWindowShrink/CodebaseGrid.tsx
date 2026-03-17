import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GRID_CENTER_X,
  GRID_CENTER_Y,
  GRID_MAX_SIZE,
  BLOCK_FILL,
  BLOCK_BORDER,
  BLOCK_CODE_COLOR,
  CODE_FONT_FAMILY,
  GRID_STAGES,
  GRID_APPEAR_START,
  GRID_APPEAR_END,
} from "./constants";

const FAUX_CODE_LINES = [
  "fn main() {",
  "  let x = 42;",
  "  loop { .. }",
  "}",
];

/**
 * CodebaseGrid — renders the morphing grid of code blocks.
 *
 * Starts as 4x4 blocks, then grows to 8x8, 16x16, 32x32 while
 * the blocks shrink to maintain the overall grid size.
 */
export const CodebaseGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in the grid
  const gridOpacity = interpolate(
    frame,
    [GRID_APPEAR_START, GRID_APPEAR_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Determine current grid size by interpolating between stages
  let currentGridSize = GRID_STAGES[0].gridSize;

  for (let i = 1; i < GRID_STAGES.length; i++) {
    const stage = GRID_STAGES[i];
    if (frame >= stage.morphStart) {
      const progress = interpolate(
        frame,
        [stage.morphStart, stage.morphEnd],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.inOut(Easing.cubic),
        }
      );
      currentGridSize =
        GRID_STAGES[i - 1].gridSize +
        (stage.gridSize - GRID_STAGES[i - 1].gridSize) * progress;
    }
  }

  // Render with the nearest integer grid size for actual blocks
  const renderGridSize = Math.round(currentGridSize);
  const gap = renderGridSize <= 8 ? 8 : renderGridSize <= 16 ? 4 : 2;
  const totalGap = (renderGridSize - 1) * gap;
  const blockSize = (GRID_MAX_SIZE - totalGap) / renderGridSize;
  const gridTotalSize = renderGridSize * blockSize + totalGap;
  const gridLeft = GRID_CENTER_X - gridTotalSize / 2;
  const gridTop = GRID_CENTER_Y - gridTotalSize / 2;

  // Show faux code only when blocks are large enough
  const showCode = blockSize > 30;
  const codeFontSize = Math.max(5, Math.min(8, blockSize * 0.06));

  const blocks: React.ReactNode[] = [];
  for (let row = 0; row < renderGridSize; row++) {
    for (let col = 0; col < renderGridSize; col++) {
      const x = gridLeft + col * (blockSize + gap);
      const y = gridTop + row * (blockSize + gap);
      blocks.push(
        <div
          key={`${row}-${col}`}
          style={{
            position: "absolute",
            left: x,
            top: y,
            width: blockSize,
            height: blockSize,
            backgroundColor: BLOCK_FILL,
            border: `1px solid ${BLOCK_BORDER}`,
            borderRadius: Math.max(2, blockSize * 0.05),
            opacity: 0.3,
            overflow: "hidden",
          }}
        >
          {showCode &&
            FAUX_CODE_LINES.map((line, i) => (
              <div
                key={i}
                style={{
                  fontFamily: CODE_FONT_FAMILY,
                  fontSize: codeFontSize,
                  color: BLOCK_CODE_COLOR,
                  opacity: 0.15,
                  whiteSpace: "nowrap" as const,
                  overflow: "hidden",
                  lineHeight: 1.4,
                  paddingLeft: 3,
                }}
              >
                {line}
              </div>
            ))}
        </div>
      );
    }
  }

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        opacity: gridOpacity,
      }}
    >
      {blocks}
    </div>
  );
};

export default CodebaseGrid;
