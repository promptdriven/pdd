import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  GRID_STAGES,
  GRID_AREA_SIZE,
  GAP,
  MORPH_DURATION,
  BLOCK_FILL,
  BLOCK_BORDER,
  TEXT_MUTED,
  FAUX_CODE_LINES,
  GRID_CENTER_X,
  GRID_CENTER_Y,
} from './constants';

export const CodebaseGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine the current grid size with smooth interpolation
  const currentGridSize = useMemo(() => {
    let size = GRID_STAGES[0].gridSize;
    for (let i = 1; i < GRID_STAGES.length; i++) {
      const stage = GRID_STAGES[i];
      const prevStage = GRID_STAGES[i - 1];
      if (frame >= stage.startFrame) {
        size = stage.gridSize;
      } else if (frame >= stage.startFrame - MORPH_DURATION) {
        const progress = interpolate(
          frame,
          [stage.startFrame - MORPH_DURATION, stage.startFrame],
          [0, 1],
          { easing: Easing.inOut(Easing.cubic), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );
        size = prevStage.gridSize + (stage.gridSize - prevStage.gridSize) * progress;
      }
    }
    return size;
  }, [frame]);

  const roundedGridSize = Math.round(currentGridSize);
  const blockSize = (GRID_AREA_SIZE - (roundedGridSize - 1) * GAP) / roundedGridSize;
  const totalGridSize = roundedGridSize * blockSize + (roundedGridSize - 1) * GAP;

  // Fade in
  const opacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Morph scale effect during transitions
  const morphScale = useMemo(() => {
    for (let i = 1; i < GRID_STAGES.length; i++) {
      const stage = GRID_STAGES[i];
      if (frame >= stage.startFrame - MORPH_DURATION && frame < stage.startFrame) {
        const progress = interpolate(
          frame,
          [stage.startFrame - MORPH_DURATION, stage.startFrame - MORPH_DURATION / 2, stage.startFrame],
          [1, 1.02, 1],
          { easing: Easing.inOut(Easing.cubic), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );
        return progress;
      }
    }
    return 1;
  }, [frame]);

  const showFauxCode = blockSize > 20;

  return (
    <div
      style={{
        position: 'absolute',
        left: GRID_CENTER_X - totalGridSize / 2,
        top: GRID_CENTER_Y - totalGridSize / 2,
        width: totalGridSize,
        height: totalGridSize,
        opacity,
        transform: `scale(${morphScale})`,
      }}
    >
      {Array.from({ length: roundedGridSize }).map((_, row) =>
        Array.from({ length: roundedGridSize }).map((_, col) => (
          <div
            key={`${row}-${col}`}
            style={{
              position: 'absolute',
              left: col * (blockSize + GAP),
              top: row * (blockSize + GAP),
              width: blockSize,
              height: blockSize,
              backgroundColor: BLOCK_FILL,
              border: `1px solid ${BLOCK_BORDER}`,
              borderRadius: Math.max(2, blockSize * 0.06),
              opacity: 0.3,
              overflow: 'hidden',
            }}
          >
            {showFauxCode && (
              <div
                style={{
                  padding: 3,
                  fontFamily: 'JetBrains Mono, monospace',
                  fontSize: Math.min(6, blockSize * 0.08),
                  color: TEXT_MUTED,
                  opacity: 0.15,
                  lineHeight: 1.4,
                  whiteSpace: 'pre',
                }}
              >
                {FAUX_CODE_LINES.join('\n')}
              </div>
            )}
          </div>
        ))
      )}
    </div>
  );
};

export default CodebaseGrid;
