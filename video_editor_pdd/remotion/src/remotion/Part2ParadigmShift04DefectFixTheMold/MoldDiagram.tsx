import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_STROKE_COLOR,
  MOLD_STROKE_OPACITY,
  MOLD_STROKE_WIDTH,
  MOLD_WALL_FILL,
  MOLD_WALL_FILL_OPACITY,
  MOLD_CAVITY_COLOR,
  MOLD_CAVITY_OPACITY,
  MOLD_DRAW_START,
  MOLD_DRAW_END,
  WALL_ADJUST_START,
  WALL_ADJUST_END,
  ADJUSTMENT_PX,
  ADJUSTMENT_COLOR,
  ADJUSTMENT_WALL_OPACITY_START,
  ADJUSTMENT_WALL_OPACITY_END,
  AMBIENT_GLOW_START,
  AMBIENT_GLOW_CYCLE,
} from "./constants";

interface MoldDiagramProps {
  showAdjustment: boolean;
}

export const MoldDiagram: React.FC<MoldDiagramProps> = ({ showAdjustment }) => {
  const frame = useCurrentFrame();

  // Draw progress — stroke-dasharray based reveal
  const drawProgress = interpolate(
    frame,
    [MOLD_DRAW_START, MOLD_DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Wall adjustment — right wall shifts inward
  const wallShift = showAdjustment
    ? interpolate(
        frame,
        [WALL_ADJUST_START, WALL_ADJUST_END],
        [0, ADJUSTMENT_PX],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
      )
    : 0;

  // Wall highlight opacity during adjustment
  const wallHighlight = showAdjustment
    ? interpolate(
        frame,
        [WALL_ADJUST_START, WALL_ADJUST_END],
        [ADJUSTMENT_WALL_OPACITY_START, ADJUSTMENT_WALL_OPACITY_END],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : MOLD_WALL_FILL_OPACITY;

  // Ambient glow after adjustment is done
  const ambientGlow = frame >= AMBIENT_GLOW_START
    ? (() => {
        const cycleFrame = (frame - AMBIENT_GLOW_START) % AMBIENT_GLOW_CYCLE;
        const phase = cycleFrame / AMBIENT_GLOW_CYCLE;
        const sineVal = Math.sin(phase * Math.PI * 2);
        return interpolate(sineVal, [-1, 1], [0.4, 0.7]);
      })()
    : wallHighlight;

  const finalWallOpacity = frame >= AMBIENT_GLOW_START ? ambientGlow : wallHighlight;

  // Mold outline path length (approx perimeter)
  const outlinePathLength = 2 * (MOLD_WIDTH + MOLD_HEIGHT);
  const visibleLength = drawProgress * outlinePathLength;

  // Coordinates
  const left = MOLD_CENTER_X - MOLD_WIDTH / 2;
  const top = MOLD_CENTER_Y - MOLD_HEIGHT / 2;
  const wallThickness = 40;
  const cavityWidth = MOLD_WIDTH - wallThickness * 2;
  const cavityHeight = MOLD_HEIGHT - wallThickness;

  return (
    <svg
      width={MOLD_WIDTH + 60}
      height={MOLD_HEIGHT + 60}
      viewBox={`${left - 30} ${top - 30} ${MOLD_WIDTH + 60} ${MOLD_HEIGHT + 60}`}
      style={{
        position: "absolute",
        left: left - 30,
        top: top - 30,
      }}
    >
      {/* Outer mold shell */}
      <rect
        x={left}
        y={top}
        width={MOLD_WIDTH}
        height={MOLD_HEIGHT}
        fill="none"
        stroke={MOLD_STROKE_COLOR}
        strokeWidth={MOLD_STROKE_WIDTH}
        strokeOpacity={MOLD_STROKE_OPACITY}
        strokeDasharray={outlinePathLength}
        strokeDashoffset={outlinePathLength - visibleLength}
      />

      {/* Left wall */}
      <rect
        x={left}
        y={top}
        width={wallThickness}
        height={MOLD_HEIGHT}
        fill={MOLD_WALL_FILL}
        fillOpacity={finalWallOpacity}
        opacity={drawProgress}
      />

      {/* Right wall (adjustable) */}
      <rect
        x={left + MOLD_WIDTH - wallThickness - wallShift}
        y={top}
        width={wallThickness}
        height={MOLD_HEIGHT}
        fill={showAdjustment && frame >= WALL_ADJUST_START ? ADJUSTMENT_COLOR : MOLD_WALL_FILL}
        fillOpacity={finalWallOpacity}
        opacity={drawProgress}
      />

      {/* Top wall */}
      <rect
        x={left + wallThickness}
        y={top}
        width={cavityWidth}
        height={wallThickness}
        fill={MOLD_WALL_FILL}
        fillOpacity={finalWallOpacity}
        opacity={drawProgress}
      />

      {/* Cavity (open bottom for ejection) */}
      <rect
        x={left + wallThickness}
        y={top + wallThickness}
        width={cavityWidth - wallShift}
        height={cavityHeight}
        fill={MOLD_CAVITY_COLOR}
        fillOpacity={MOLD_CAVITY_OPACITY}
        opacity={drawProgress}
      />

      {/* Glow trail during adjustment */}
      {showAdjustment && frame >= WALL_ADJUST_START && frame <= WALL_ADJUST_END + 20 && (
        <rect
          x={left + MOLD_WIDTH - wallThickness - wallShift - 6}
          y={top + wallThickness}
          width={12}
          height={cavityHeight}
          fill={ADJUSTMENT_COLOR}
          fillOpacity={interpolate(
            frame,
            [WALL_ADJUST_START, WALL_ADJUST_END, WALL_ADJUST_END + 20],
            [0, 0.4, 0],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          )}
        />
      )}

      {/* Ambient glow outline */}
      {frame >= AMBIENT_GLOW_START && (
        <rect
          x={left - 3}
          y={top - 3}
          width={MOLD_WIDTH + 6}
          height={MOLD_HEIGHT + 6}
          fill="none"
          stroke={ADJUSTMENT_COLOR}
          strokeWidth={2}
          strokeOpacity={ambientGlow * 0.3}
          rx={4}
        />
      )}
    </svg>
  );
};
