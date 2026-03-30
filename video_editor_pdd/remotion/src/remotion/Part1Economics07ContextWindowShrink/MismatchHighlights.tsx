// MismatchHighlights.tsx — Phase 3 overlays showing red (irrelevant) blocks inside
// the context window and green (needed) blocks outside it.
// Appears starting at frame 720, fades in over 20 frames.
// Uses global frames (not wrapped in a Sequence) so grid geometry is correct.

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MISMATCH_START_FRAME,
  HIGHLIGHT_FADE_DURATION,
  RED_HIGHLIGHT_COLOR,
  GREEN_HIGHLIGHT_COLOR,
  HIGHLIGHT_OVERLAY_OPACITY,
  RED_BLOCK_INDICES,
  GREEN_BLOCK_INDICES,
  RED_TOOLTIP_LABEL,
  GREEN_TOOLTIP_LABEL,
  TOOLTIP_FONT_SIZE,
  BLOCK_GAP,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  CTX_WINDOW_WIDTH,
  CTX_WINDOW_HEIGHT,
} from './constants';
import { useGridGeometry } from './CodeBlockGrid';

interface HighlightBlockProps {
  row: number;
  col: number;
  blockSize: number;
  originX: number;
  originY: number;
  color: string;
  label: string;
  /** Stagger delay in frames after MISMATCH_START_FRAME */
  delayFrames: number;
}

const HighlightBlock: React.FC<HighlightBlockProps> = ({
  row,
  col,
  blockSize,
  originX,
  originY,
  color,
  label,
  delayFrames,
}) => {
  const frame = useCurrentFrame();

  // Fade starts at MISMATCH_START_FRAME + per-block stagger
  const fadeStart = MISMATCH_START_FRAME + delayFrames;
  const fadeEnd = fadeStart + HIGHLIGHT_FADE_DURATION;

  // Don't render at all before fade starts
  if (frame < fadeStart) return null;

  const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, HIGHLIGHT_OVERLAY_OPACITY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const scale = interpolate(frame, [fadeStart, fadeEnd], [0.95, 1.0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const labelOpacity = interpolate(
    frame,
    [fadeStart + 10, fadeEnd + 10],
    [0, 0.7],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const x = originX + col * (blockSize + BLOCK_GAP);
  const y = originY + row * (blockSize + BLOCK_GAP);

  // For very small blocks at 32×32 grid, render a brighter marker dot
  if (blockSize < 4) {
    return (
      <div
        style={{
          position: 'absolute',
          left: x - 3,
          top: y - 3,
          width: Math.max(blockSize, 6),
          height: Math.max(blockSize, 6),
          borderRadius: '50%',
          backgroundColor: color,
          opacity: Math.min(opacity * 3, 0.8),
          transform: `scale(${scale})`,
          zIndex: 15,
        }}
      />
    );
  }

  return (
    <>
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width: blockSize,
          height: blockSize,
          backgroundColor: color,
          opacity,
          borderRadius: blockSize > 10 ? 2 : 0,
          transform: `scale(${scale})`,
          transformOrigin: 'center',
          zIndex: 15,
        }}
      />
      {blockSize >= 14 && (
        <div
          style={{
            position: 'absolute',
            left: x + blockSize / 2,
            top: y - TOOLTIP_FONT_SIZE - 4,
            transform: 'translateX(-50%)',
            fontFamily: 'Inter, sans-serif',
            fontSize: TOOLTIP_FONT_SIZE,
            color,
            opacity: labelOpacity,
            whiteSpace: 'nowrap',
            zIndex: 16,
          }}
        >
          {label}
        </div>
      )}
    </>
  );
};

export const MismatchHighlights: React.FC = () => {
  const frame = useCurrentFrame();
  const { gridSize, blockSize, originX, originY } = useGridGeometry();

  // Don't render anything before the mismatch phase
  if (frame < MISMATCH_START_FRAME) return null;

  // Context window bounds (screen coords)
  const cwLeft = GRID_CENTER_X - CTX_WINDOW_WIDTH / 2;
  const cwTop = GRID_CENTER_Y - CTX_WINDOW_HEIGHT / 2;
  const cwRight = cwLeft + CTX_WINDOW_WIDTH;
  const cwBottom = cwTop + CTX_WINDOW_HEIGHT;

  const toRowCol = (idx: number) => ({
    row: Math.floor(idx / gridSize) % gridSize,
    col: idx % gridSize,
  });

  const isInsideWindow = (row: number, col: number) => {
    const bx = originX + col * (blockSize + BLOCK_GAP);
    const by = originY + row * (blockSize + BLOCK_GAP);
    return (
      bx >= cwLeft &&
      bx + blockSize <= cwRight &&
      by >= cwTop &&
      by + blockSize <= cwBottom
    );
  };

  // Red blocks: inside the context window (irrelevant code the AI grabbed)
  const redBlocks = React.useMemo(() => {
    const candidates: Array<{ row: number; col: number }> = [];

    for (const idx of RED_BLOCK_INDICES) {
      if (idx < gridSize * gridSize) {
        const { row, col } = toRowCol(idx);
        if (isInsideWindow(row, col)) {
          candidates.push({ row, col });
        }
      }
    }

    // Fill up if needed — find blocks inside the window
    if (candidates.length < 3) {
      for (let r = 0; r < gridSize && candidates.length < 4; r++) {
        for (let c = 0; c < gridSize && candidates.length < 4; c++) {
          if (
            isInsideWindow(r, c) &&
            !candidates.some((b) => b.row === r && b.col === c)
          ) {
            candidates.push({ row: r, col: c });
          }
        }
      }
    }

    return candidates.slice(0, 4);
  }, [gridSize, blockSize, originX, originY]);

  // Green blocks: outside the context window (needed code that was missed)
  const greenBlocks = React.useMemo(() => {
    const candidates: Array<{ row: number; col: number }> = [];

    for (const idx of GREEN_BLOCK_INDICES) {
      if (idx < gridSize * gridSize) {
        const { row, col } = toRowCol(idx);
        if (!isInsideWindow(row, col)) {
          candidates.push({ row, col });
        }
      }
    }

    // Fill up if needed — scatter outside the window
    if (candidates.length < 4) {
      const step = Math.max(1, Math.floor(gridSize / 6));
      for (let r = 0; r < gridSize && candidates.length < 6; r += step) {
        for (let c = 0; c < gridSize && candidates.length < 6; c += step) {
          if (
            !isInsideWindow(r, c) &&
            !candidates.some((b) => b.row === r && b.col === c)
          ) {
            candidates.push({ row: r, col: c });
          }
        }
      }
    }

    return candidates.slice(0, 6);
  }, [gridSize, blockSize, originX, originY]);

  return (
    <>
      {redBlocks.map((b, i) => (
        <HighlightBlock
          key={`red-${i}`}
          row={b.row}
          col={b.col}
          blockSize={blockSize}
          originX={originX}
          originY={originY}
          color={RED_HIGHLIGHT_COLOR}
          label={RED_TOOLTIP_LABEL}
          delayFrames={i * 5}
        />
      ))}
      {greenBlocks.map((b, i) => (
        <HighlightBlock
          key={`green-${i}`}
          row={b.row}
          col={b.col}
          blockSize={blockSize}
          originX={originX}
          originY={originY}
          color={GREEN_HIGHLIGHT_COLOR}
          label={GREEN_TOOLTIP_LABEL}
          delayFrames={i * 4 + 10}
        />
      ))}
    </>
  );
};

export default MismatchHighlights;
