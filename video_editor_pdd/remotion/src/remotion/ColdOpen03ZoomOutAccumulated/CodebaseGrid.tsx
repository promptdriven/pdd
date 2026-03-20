import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CODE_BLOCK_WIDTH,
  CODE_BLOCK_HEIGHT,
  CODE_BLOCK_FILL,
  CODE_BLOCK_BORDER,
  CODE_BLOCK_BORDER_OPACITY,
  DIFF_RED,
  DIFF_GREEN,
  DIFF_MARKER_PERCENT,
  CODE_BLOCK_COLS,
  CODE_BLOCK_ROWS,
  CODE_BLOCK_GAP_X,
  CODE_BLOCK_GAP_Y,
  GLOW_RED_OPACITY,
  ZOOM_START,
  ZOOM_END,
  seededRandom,
} from './constants';

interface CodeBlock {
  x: number;
  y: number;
  hasDiff: boolean;
  diffColor: string;
  distFromCenter: number;
  seed: number;
}

function generateBlocks(): CodeBlock[] {
  const blocks: CodeBlock[] = [];
  const centerCol = CODE_BLOCK_COLS / 2;
  const centerRow = CODE_BLOCK_ROWS / 2;
  const totalW = CODE_BLOCK_COLS * (CODE_BLOCK_WIDTH + CODE_BLOCK_GAP_X);
  const totalH = CODE_BLOCK_ROWS * (CODE_BLOCK_HEIGHT + CODE_BLOCK_GAP_Y);
  const offsetX = -totalW / 2;
  const offsetY = -totalH / 2;

  for (let row = 0; row < CODE_BLOCK_ROWS; row++) {
    for (let col = 0; col < CODE_BLOCK_COLS; col++) {
      const idx = row * CODE_BLOCK_COLS + col;
      const rand = seededRandom(idx + 1);
      const hasDiff = rand < DIFF_MARKER_PERCENT / 100;
      const diffColor = seededRandom(idx + 100) > 0.5 ? DIFF_RED : DIFF_GREEN;
      const dist = Math.sqrt(
        Math.pow(col - centerCol, 2) + Math.pow(row - centerRow, 2)
      );
      blocks.push({
        x: offsetX + col * (CODE_BLOCK_WIDTH + CODE_BLOCK_GAP_X),
        y: offsetY + row * (CODE_BLOCK_HEIGHT + CODE_BLOCK_GAP_Y),
        hasDiff,
        diffColor,
        distFromCenter: dist,
        seed: idx,
      });
    }
  }
  return blocks;
}

const codeBlocks = generateBlocks();
const maxDist = Math.max(...codeBlocks.map((b) => b.distFromCenter));

export const CodebaseGrid: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
      }}
    >
      {/* Red glow behind */}
      <div
        style={{
          position: 'absolute',
          left: '50%',
          top: '50%',
          width: 600,
          height: 400,
          transform: 'translate(-50%, -50%)',
          background: `radial-gradient(ellipse, ${DIFF_RED} 0%, transparent 70%)`,
          opacity: GLOW_RED_OPACITY,
          pointerEvents: 'none',
        }}
      />

      {codeBlocks.map((block, i) => {
        // Staggered fade-in from center outward during zoom
        const delayFrames = (block.distFromCenter / maxDist) * 40;
        const fadeStart = ZOOM_START + delayFrames;
        const blockOpacity = interpolate(
          frame,
          [fadeStart, fadeStart + 30],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        // Diff marker pulse at frame 90-100
        const diffPulse =
          block.hasDiff
            ? interpolate(frame, [90, 95, 100], [1, 1.4, 1], {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
              })
            : 1;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: block.x,
              top: block.y,
              width: CODE_BLOCK_WIDTH,
              height: CODE_BLOCK_HEIGHT,
              backgroundColor: CODE_BLOCK_FILL,
              border: `1px solid ${CODE_BLOCK_BORDER}`,
              borderColor: `rgba(48, 54, 61, ${CODE_BLOCK_BORDER_OPACITY})`,
              opacity: blockOpacity,
              borderRadius: 2,
            }}
          >
            {block.hasDiff && (
              <div
                style={{
                  position: 'absolute',
                  left: 2,
                  top: Math.floor(seededRandom(block.seed + 50) * 14) + 2,
                  width: CODE_BLOCK_WIDTH - 8,
                  height: 4,
                  backgroundColor: block.diffColor,
                  opacity: 0.7,
                  borderRadius: 1,
                  transform: `scaleY(${diffPulse})`,
                }}
              />
            )}
          </div>
        );
      })}
    </div>
  );
};

export default CodebaseGrid;
