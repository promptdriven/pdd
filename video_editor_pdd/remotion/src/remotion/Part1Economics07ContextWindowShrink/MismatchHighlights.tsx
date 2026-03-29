import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  HIGHLIGHT_RED,
  HIGHLIGHT_GREEN,
  BLOCK_GAP,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  MISMATCH_START_FRAME,
  MISMATCH_FADE_FRAMES,
  RED_BLOCK_INDICES,
  GREEN_BLOCK_INDICES,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

/**
 * Renders colored overlays on specific grid blocks:
 * - Red blocks inside the context window (irrelevant code grabbed)
 * - Green blocks outside the context window (needed code missed)
 *
 * Appears starting at MISMATCH_START_FRAME with a fade-in.
 */

const GRID_SIZE = 32;
const MAX_GRID_AREA = Math.min(CANVAS_WIDTH - 200, CANVAS_HEIGHT - 160);

function getBlockSize(): number {
  return Math.max(2, (MAX_GRID_AREA - (GRID_SIZE - 1) * BLOCK_GAP) / GRID_SIZE);
}

function indexToXY(index: number): { row: number; col: number } {
  return {
    row: Math.floor(index / GRID_SIZE),
    col: index % GRID_SIZE,
  };
}

interface HighlightBlockProps {
  index: number;
  color: string;
  label: string;
  fadeProgress: number;
  blockPx: number;
  gridOriginX: number;
  gridOriginY: number;
}

const HighlightBlock: React.FC<HighlightBlockProps> = ({
  index,
  color,
  label,
  fadeProgress,
  blockPx,
  gridOriginX,
  gridOriginY,
}) => {
  const { row, col } = indexToXY(index);
  const x = gridOriginX + col * (blockPx + BLOCK_GAP);
  const y = gridOriginY + row * (blockPx + BLOCK_GAP);

  const scale = 0.95 + 0.05 * fadeProgress;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: blockPx,
        height: blockPx,
        backgroundColor: color,
        opacity: 0.3 * fadeProgress,
        borderRadius: Math.max(1, blockPx > 10 ? 3 : 1),
        transform: `scale(${scale})`,
        zIndex: 15,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
      }}
    >
      {blockPx > 14 && (
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 11,
            color: color,
            opacity: 0.7 * fadeProgress,
            whiteSpace: "nowrap",
          }}
        >
          {label}
        </span>
      )}
    </div>
  );
};

const MismatchHighlights: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeProgress = interpolate(
    frame,
    [MISMATCH_START_FRAME, MISMATCH_START_FRAME + MISMATCH_FADE_FRAMES],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const blockPx = getBlockSize();
  const gridDim = GRID_SIZE * blockPx + (GRID_SIZE - 1) * BLOCK_GAP;
  const gridOriginX = GRID_CENTER_X - gridDim / 2;
  const gridOriginY = GRID_CENTER_Y - gridDim / 2;

  if (fadeProgress <= 0) return null;

  return (
    <>
      {RED_BLOCK_INDICES.map((idx) => (
        <HighlightBlock
          key={`red-${idx}`}
          index={idx}
          color={HIGHLIGHT_RED}
          label="Irrelevant"
          fadeProgress={fadeProgress}
          blockPx={blockPx}
          gridOriginX={gridOriginX}
          gridOriginY={gridOriginY}
        />
      ))}
      {GREEN_BLOCK_INDICES.map((idx) => (
        <HighlightBlock
          key={`green-${idx}`}
          index={idx}
          color={HIGHLIGHT_GREEN}
          label="Needed"
          fadeProgress={fadeProgress}
          blockPx={blockPx}
          gridOriginX={gridOriginX}
          gridOriginY={gridOriginY}
        />
      ))}
    </>
  );
};

export default MismatchHighlights;
