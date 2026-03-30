import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

/**
 * Generates a deterministic pseudo-random number from a seed.
 */
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 9301 + 49297) * 49297;
  return x - Math.floor(x);
}

type TokenType = 'irrelevant' | 'relevant' | 'neutral';

interface TokenBlockGridProps {
  rows: number;
  cols: number;
  blockWidth: number;
  blockHeight: number;
  gap: number;
  padding: number;
  irrelevantColor: string;
  relevantColor: string;
  neutralColor: string;
  irrelevantRatio: number;
  relevantRatio: number;
  fillStartFrame: number;
  fillEndFrame: number;
  staggerPerRow: number;
}

const TokenBlockGrid: React.FC<TokenBlockGridProps> = ({
  rows,
  cols,
  blockWidth,
  blockHeight,
  gap,
  padding,
  irrelevantColor,
  relevantColor,
  neutralColor,
  irrelevantRatio,
  relevantRatio,
  fillStartFrame,
  fillEndFrame,
  staggerPerRow,
}) => {
  const frame = useCurrentFrame();

  // Build a deterministic grid of token types
  const grid = useMemo(() => {
    const cells: TokenType[][] = [];
    for (let r = 0; r < rows; r++) {
      const row: TokenType[] = [];
      for (let c = 0; c < cols; c++) {
        const rand = seededRandom(r * cols + c + 42);
        if (rand < irrelevantRatio) {
          row.push('irrelevant');
        } else if (rand < irrelevantRatio + relevantRatio) {
          row.push('relevant');
        } else {
          row.push('neutral');
        }
      }
      cells.push(row);
    }
    return cells;
  }, [rows, cols, irrelevantRatio, relevantRatio]);

  const colorMap: Record<TokenType, string> = {
    irrelevant: irrelevantColor,
    relevant: relevantColor,
    neutral: neutralColor,
  };

  const opacityMap: Record<TokenType, number> = {
    irrelevant: 0.25,
    relevant: 0.3,
    neutral: 0.15,
  };

  const totalFillDuration = fillEndFrame - fillStartFrame;
  const rowDuration = Math.max(
    6,
    (totalFillDuration - staggerPerRow * (rows - 1)) / rows
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: padding,
        left: padding,
        width: cols * (blockWidth + gap) - gap,
        height: rows * (blockHeight + gap) - gap,
      }}
    >
      {grid.map((row, r) =>
        row.map((type, c) => {
          const rowStartFrame = fillStartFrame + r * staggerPerRow;
          const rowEndFrame = rowStartFrame + rowDuration;

          // Each block within a row also has a tiny stagger
          const blockDelay = c * 0.3;
          const effectiveStart = rowStartFrame + blockDelay;
          const effectiveEnd = Math.min(
            effectiveStart + rowDuration,
            rowEndFrame + blockDelay
          );

          const clampedStart = Math.max(0, effectiveStart);
          const clampedEnd = Math.max(clampedStart + 0.001, effectiveEnd);

          const opacity = interpolate(
            frame,
            [clampedStart, clampedEnd],
            [0, opacityMap[type]],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            }
          );

          const scale = interpolate(
            frame,
            [clampedStart, clampedEnd],
            [0.3, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            }
          );

          return (
            <div
              key={`${r}-${c}`}
              style={{
                position: 'absolute',
                left: c * (blockWidth + gap),
                top: r * (blockHeight + gap),
                width: blockWidth,
                height: blockHeight,
                backgroundColor: colorMap[type],
                borderRadius: 3,
                opacity,
                transform: `scale(${scale})`,
              }}
            />
          );
        })
      )}
    </div>
  );
};

export default TokenBlockGrid;
