import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RED_HIGHLIGHT,
  GREEN_HIGHLIGHT,
  HIGHLIGHT_OVERLAY_OPACITY,
  RED_BLOCK_INDICES,
  GREEN_BLOCK_INDICES,
  HIGHLIGHT_FADE_FRAMES,
  GRID_STAGE_SIZES,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

interface HighlightBlockProps {
  row: number;
  col: number;
  blockPixelSize: number;
  gap: number;
  gridLeft: number;
  gridTop: number;
  color: string;
  localFrame: number;
  delayIndex: number;
}

const HighlightBlock: React.FC<HighlightBlockProps> = ({
  row,
  col,
  blockPixelSize,
  gap,
  gridLeft,
  gridTop,
  color,
  localFrame,
  delayIndex,
}) => {
  const delay = delayIndex * 5;
  const fadeStart = delay;
  const fadeEnd = delay + HIGHLIGHT_FADE_FRAMES;

  const opacity = interpolate(localFrame, [fadeStart, fadeEnd], [0, HIGHLIGHT_OVERLAY_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const scale = interpolate(localFrame, [fadeStart, fadeEnd], [0.95, 1.0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const x = gridLeft + col * (blockPixelSize + gap);
  const y = gridTop + row * (blockPixelSize + gap);

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: blockPixelSize,
        height: blockPixelSize,
        backgroundColor: color,
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: "center center",
        borderRadius: 2,
        pointerEvents: "none",
        zIndex: 15,
      }}
    />
  );
};

/**
 * Renders red (irrelevant, inside window) and green (needed, outside window)
 * highlight overlays on the 32×32 grid during Phase 3.
 * Labels are provided by the MismatchLegend in the main component.
 */
export const MismatchHighlights: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame;

  const gridSize = 32;
  const cfg = GRID_STAGE_SIZES[gridSize];
  const gap = cfg.gapPx;
  const blockPixelSize = cfg.blockPx;
  const totalGapSpace = (gridSize - 1) * gap;

  const gridTotalWidth = gridSize * blockPixelSize + totalGapSpace;
  const gridLeft = (CANVAS_WIDTH - gridTotalWidth) / 2;
  const gridTop = (CANVAS_HEIGHT - gridTotalWidth) / 2;

  const indexToRowCol = (index: number) => ({
    row: Math.floor(index / gridSize),
    col: index % gridSize,
  });

  const redBlocks = useMemo(
    () =>
      RED_BLOCK_INDICES.map((idx, i) => {
        const { row, col } = indexToRowCol(idx);
        return (
          <HighlightBlock
            key={`red-${idx}`}
            row={row}
            col={col}
            blockPixelSize={blockPixelSize}
            gap={gap}
            gridLeft={gridLeft}
            gridTop={gridTop}
            color={RED_HIGHLIGHT}
            localFrame={localFrame}
            delayIndex={i}
          />
        );
      }),
    [localFrame, blockPixelSize, gridLeft, gridTop, gap]
  );

  const greenBlocks = useMemo(
    () =>
      GREEN_BLOCK_INDICES.map((idx, i) => {
        const { row, col } = indexToRowCol(idx);
        return (
          <HighlightBlock
            key={`green-${idx}`}
            row={row}
            col={col}
            blockPixelSize={blockPixelSize}
            gap={gap}
            gridLeft={gridLeft}
            gridTop={gridTop}
            color={GREEN_HIGHLIGHT}
            localFrame={localFrame}
            delayIndex={i + RED_BLOCK_INDICES.length}
          />
        );
      }),
    [localFrame, blockPixelSize, gridLeft, gridTop, gap]
  );

  return (
    <>
      {redBlocks}
      {greenBlocks}
    </>
  );
};

export default MismatchHighlights;
