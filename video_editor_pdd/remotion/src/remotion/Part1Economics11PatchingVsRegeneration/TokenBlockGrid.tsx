import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TOKEN_ROWS,
  TOKEN_COLS,
  TOKEN_GAP,
  PANEL_PADDING,
  PANEL_WIDTH,
  PANEL_HEIGHT,
  COLOR_RED_BLOCK,
  COLOR_GREEN_BLOCK,
  COLOR_GRAY_BLOCK,
  DIST_IRRELEVANT,
  DIST_RELEVANT,
  LEFT_FILL_START,
  LEFT_FILL_END,
} from './constants';

type BlockType = 'red' | 'green' | 'gray';

interface TokenBlockGridProps {
  panelX: number;
  panelY: number;
}

/**
 * Generates a deterministic grid of token block types based on the distribution.
 */
function generateGrid(rows: number, cols: number): BlockType[][] {
  const grid: BlockType[][] = [];
  // Use a simple seeded approach for deterministic layout
  let seed = 42;
  const nextRand = () => {
    seed = (seed * 16807 + 0) % 2147483647;
    return (seed - 1) / 2147483646;
  };

  for (let r = 0; r < rows; r++) {
    const row: BlockType[] = [];
    for (let c = 0; c < cols; c++) {
      const val = nextRand();
      if (val < DIST_IRRELEVANT) {
        row.push('red');
      } else if (val < DIST_IRRELEVANT + DIST_RELEVANT) {
        row.push('green');
      } else {
        row.push('gray');
      }
    }
    grid.push(row);
  }
  return grid;
}

const BLOCK_COLORS: Record<BlockType, { color: string; opacity: number }> = {
  red: { color: COLOR_RED_BLOCK, opacity: 0.25 },
  green: { color: COLOR_GREEN_BLOCK, opacity: 0.3 },
  gray: { color: COLOR_GRAY_BLOCK, opacity: 0.15 },
};

const TokenBlockGrid: React.FC<TokenBlockGridProps> = ({ panelX, panelY }) => {
  const frame = useCurrentFrame();

  const grid = useMemo(() => generateGrid(TOKEN_ROWS, TOKEN_COLS), []);

  // Compute available space inside the panel
  const innerWidth = PANEL_WIDTH - PANEL_PADDING * 2;
  const innerHeight = PANEL_HEIGHT - PANEL_PADDING * 2;
  const blockWidth = (innerWidth - (TOKEN_COLS - 1) * TOKEN_GAP) / TOKEN_COLS;
  const blockHeight = (innerHeight - (TOKEN_ROWS - 1) * TOKEN_GAP) / TOKEN_ROWS;

  // Total animation frames for the fill
  const fillDuration = LEFT_FILL_END - LEFT_FILL_START;
  const staggerPerRow = 3;

  return (
    <>
      {grid.map((row, rowIdx) =>
        row.map((blockType, colIdx) => {
          const rowStart = LEFT_FILL_START + rowIdx * staggerPerRow;
          const rowEnd = Math.min(rowStart + 30, LEFT_FILL_START + fillDuration);

          const opacity = interpolate(
            frame,
            [rowStart, rowEnd],
            [0, BLOCK_COLORS[blockType].opacity],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            }
          );

          const x = panelX + PANEL_PADDING + colIdx * (blockWidth + TOKEN_GAP);
          const y = panelY + PANEL_PADDING + rowIdx * (blockHeight + TOKEN_GAP);

          return (
            <div
              key={`${rowIdx}-${colIdx}`}
              style={{
                position: 'absolute',
                left: x,
                top: y,
                width: blockWidth,
                height: blockHeight,
                backgroundColor: BLOCK_COLORS[blockType].color,
                opacity,
                borderRadius: 2,
              }}
            />
          );
        })
      )}
    </>
  );
};

export default TokenBlockGrid;
