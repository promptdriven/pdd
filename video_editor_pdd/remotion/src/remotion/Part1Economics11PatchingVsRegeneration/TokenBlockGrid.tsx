import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TOKEN_ROWS,
  TOKEN_COLS,
  TOKEN_BLOCK_GAP,
  BLOCK_RED,
  BLOCK_GREEN_RELEVANT,
  BLOCK_GRAY,
  DISTRIBUTION,
  LEFT_FILL_START,
} from './constants';

// Deterministic seeded random for consistent block colors
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 9301 + 49297) * 49297;
  return x - Math.floor(x);
}

interface TokenBlockGridProps {
  panelWidth: number;
  panelHeight: number;
}

const TokenBlockGrid: React.FC<TokenBlockGridProps> = ({
  panelWidth,
  panelHeight,
}) => {
  const frame = useCurrentFrame();

  const innerPadding = 12;
  const availableW = panelWidth - innerPadding * 2;
  const availableH = panelHeight - innerPadding * 2;
  const blockW =
    (availableW - (TOKEN_COLS - 1) * TOKEN_BLOCK_GAP) / TOKEN_COLS;
  const blockH =
    (availableH - (TOKEN_ROWS - 1) * TOKEN_BLOCK_GAP) / TOKEN_ROWS;

  // Pre-compute the color assignment for each cell
  const blockColors = useMemo(() => {
    const colors: string[] = [];
    for (let row = 0; row < TOKEN_ROWS; row++) {
      for (let col = 0; col < TOKEN_COLS; col++) {
        const idx = row * TOKEN_COLS + col;
        const r = seededRandom(idx + 42);
        if (r < DISTRIBUTION.irrelevant) {
          colors.push(BLOCK_RED);
        } else if (r < DISTRIBUTION.irrelevant + DISTRIBUTION.relevant) {
          colors.push(BLOCK_GREEN_RELEVANT);
        } else {
          colors.push(BLOCK_GRAY);
        }
      }
    }
    return colors;
  }, []);

  return (
    <div
      style={{
        position: 'absolute',
        top: innerPadding,
        left: innerPadding,
        width: availableW,
        height: availableH,
      }}
    >
      {Array.from({ length: TOKEN_ROWS }).map((_, row) => {
        // Stagger: each row starts 3 frames after the previous
        const rowStart = LEFT_FILL_START + row * 3;
        const rowProgress = interpolate(frame, [rowStart, rowStart + 20], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        });

        return Array.from({ length: TOKEN_COLS }).map((_, col) => {
          const idx = row * TOKEN_COLS + col;
          const color = blockColors[idx];

          // Opacity based on color type
          let baseOpacity: number;
          if (color === BLOCK_RED) {
            baseOpacity = 0.25;
          } else if (color === BLOCK_GREEN_RELEVANT) {
            baseOpacity = 0.3;
          } else {
            baseOpacity = 0.15;
          }

          const x = col * (blockW + TOKEN_BLOCK_GAP);
          const y = row * (blockH + TOKEN_BLOCK_GAP);

          return (
            <div
              key={`${row}-${col}`}
              style={{
                position: 'absolute',
                left: x,
                top: y,
                width: blockW,
                height: blockH,
                backgroundColor: color,
                opacity: baseOpacity * rowProgress,
                borderRadius: 2,
              }}
            />
          );
        });
      })}
    </div>
  );
};

export default TokenBlockGrid;
