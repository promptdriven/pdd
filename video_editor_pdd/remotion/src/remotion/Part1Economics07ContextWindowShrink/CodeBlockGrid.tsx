import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BLOCK_FILL,
  BLOCK_BORDER,
  GRID_STAGE_SIZES,
  GROWTH_STAGES,
  TRANSITION_FRAMES,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

/**
 * Renders the growing code-block grid.
 * The grid grows through 4 stages (4×4 → 8×8 → 16×16 → 32×32),
 * each transition animated over TRANSITION_FRAMES.
 */
export const CodeBlockGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine the current discrete stage index and transition progress
  const { renderGridSize, blockPixelSize, gap } = useMemo(() => {
    let currentStageIdx = 0;

    for (let i = 1; i < GROWTH_STAGES.length; i++) {
      const transitionEnd = GROWTH_STAGES[i].startFrame + TRANSITION_FRAMES;
      if (frame >= transitionEnd) {
        currentStageIdx = i;
      } else if (frame >= GROWTH_STAGES[i].startFrame) {
        // Mid-transition: interpolate between stages
        const progress = interpolate(
          frame,
          [GROWTH_STAGES[i].startFrame, transitionEnd],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.cubic),
          }
        );

        const prevSize = GROWTH_STAGES[i - 1].gridSize;
        const nextSize = GROWTH_STAGES[i].gridSize;
        const prevCfg = GRID_STAGE_SIZES[prevSize];
        const nextCfg = GRID_STAGE_SIZES[nextSize];

        // Use the target grid count once past halfway for block rendering
        const snapSize = progress > 0.5 ? nextSize : prevSize;
        const snapCfg = progress > 0.5 ? nextCfg : prevCfg;

        // Smoothly interpolate block and gap pixel sizes
        const bPx = prevCfg.blockPx + (nextCfg.blockPx - prevCfg.blockPx) * progress;
        const gPx = prevCfg.gapPx + (nextCfg.gapPx - prevCfg.gapPx) * progress;

        return {
          renderGridSize: snapSize,
          blockPixelSize: progress > 0.5 ? bPx : snapCfg.blockPx,
          gap: progress > 0.5 ? Math.round(gPx) : snapCfg.gapPx,
        };
      }
    }

    const stageSize = GROWTH_STAGES[currentStageIdx].gridSize;
    const cfg = GRID_STAGE_SIZES[stageSize];
    return {
      renderGridSize: stageSize,
      blockPixelSize: cfg.blockPx,
      gap: cfg.gapPx,
    };
  }, [frame]);

  // Fade-in for initial assembly (frame 0-40)
  const assembleOpacity = interpolate(frame, [0, 40], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Subtle scale pulse during transitions
  const scaleProgress = useMemo(() => {
    for (let i = 1; i < GROWTH_STAGES.length; i++) {
      const transitionStart = GROWTH_STAGES[i].startFrame;
      const transitionEnd = transitionStart + TRANSITION_FRAMES;

      if (frame >= transitionStart && frame < transitionEnd) {
        return interpolate(
          frame,
          [transitionStart, transitionEnd],
          [1.03, 1.0],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.cubic),
          }
        );
      }
    }
    return 1.0;
  }, [frame]);

  const totalGapSpace = (renderGridSize - 1) * gap;
  const gridTotalWidth = renderGridSize * blockPixelSize + totalGapSpace;
  const gridTotalHeight = gridTotalWidth;

  const gridLeft = (CANVAS_WIDTH - gridTotalWidth) / 2;
  const gridTop = (CANVAS_HEIGHT - gridTotalHeight) / 2;

  // Build block elements
  const blocks = useMemo(() => {
    const result: React.ReactNode[] = [];
    for (let row = 0; row < renderGridSize; row++) {
      for (let col = 0; col < renderGridSize; col++) {
        const x = col * (blockPixelSize + gap);
        const y = row * (blockPixelSize + gap);
        result.push(
          <div
            key={`${row}-${col}`}
            style={{
              position: "absolute",
              left: x,
              top: y,
              width: blockPixelSize,
              height: blockPixelSize,
              backgroundColor: BLOCK_FILL,
              border: `1px solid ${BLOCK_BORDER}`,
              borderRadius: blockPixelSize > 10 ? 2 : 0,
              boxSizing: "border-box",
            }}
          />
        );
      }
    }
    return result;
  }, [renderGridSize, blockPixelSize, gap]);

  return (
    <div
      style={{
        position: "absolute",
        left: gridLeft,
        top: gridTop,
        width: gridTotalWidth,
        height: gridTotalHeight,
        opacity: assembleOpacity,
        transform: `scale(${scaleProgress})`,
        transformOrigin: "center center",
      }}
    >
      {blocks}
    </div>
  );
};

export default CodeBlockGrid;
