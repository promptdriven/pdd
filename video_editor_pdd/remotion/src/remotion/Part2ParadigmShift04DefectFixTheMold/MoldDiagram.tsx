import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_STROKE,
  MOLD_WALL_FILL,
  MOLD_CAVITY,
  MOLD_DRAW_START,
  MOLD_DRAW_END,
  AMBER,
  FIX_START,
  FIX_END,
  HOLD_START,
  TOTAL_FRAMES,
} from "./constants";

/**
 * Animated injection mold diagram drawn center-screen.
 * Draws itself in from frame MOLD_DRAW_START → MOLD_DRAW_END.
 * At FIX_START the right wall highlights amber and shifts 4px inward.
 */
export const MoldDiagram: React.FC = () => {
  const frame = useCurrentFrame();

  // Draw progress (0→1)
  const drawProgress = interpolate(
    frame,
    [MOLD_DRAW_START, MOLD_DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Wall adjustment (amber highlight + 4px shift)
  const wallAdjust = interpolate(
    frame,
    [FIX_START, FIX_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Satisfied amber pulse during hold
  const holdPulse =
    frame >= HOLD_START
      ? 0.3 +
        0.15 *
          Math.sin(
            ((frame - HOLD_START) / 40) * Math.PI * 2
          )
      : 0;

  const left = MOLD_CENTER_X - MOLD_WIDTH / 2;
  const top = MOLD_CENTER_Y - MOLD_HEIGHT / 2;

  // The mold is two halves with a cavity in between
  const wallThickness = 60;
  const cavityW = MOLD_WIDTH - wallThickness * 2;
  const cavityH = MOLD_HEIGHT - 80; // open at bottom
  const cavityX = left + wallThickness;
  const cavityY = top + 40;

  // Right wall shifts inward by up to 4px after fix
  const rightWallShift = wallAdjust * 4;

  // Right wall amber glow opacity
  const rightWallGlow = interpolate(
    frame,
    [FIX_START, FIX_START + 15, FIX_START + 30, FIX_END],
    [0.1, 0.6, 0.5, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const overallOpacity = drawProgress;

  // Outline total perimeter for stroke-dashoffset animation
  const perimeterLength = (MOLD_WIDTH + MOLD_HEIGHT) * 2;
  const dashOffset = perimeterLength * (1 - drawProgress);

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: "100%",
        height: "100%",
        opacity: overallOpacity,
      }}
    >
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", left: 0, top: 0 }}
      >
        {/* Outer mold shell */}
        <rect
          x={left}
          y={top}
          width={MOLD_WIDTH}
          height={MOLD_HEIGHT}
          fill="none"
          stroke={MOLD_STROKE}
          strokeWidth={2}
          strokeOpacity={0.6}
          strokeDasharray={perimeterLength}
          strokeDashoffset={dashOffset}
        />

        {/* Left wall fill */}
        <rect
          x={left}
          y={top}
          width={wallThickness}
          height={MOLD_HEIGHT}
          fill={MOLD_WALL_FILL}
          fillOpacity={0.1 + holdPulse}
        />

        {/* Right wall fill (shifts inward during fix) */}
        <rect
          x={left + MOLD_WIDTH - wallThickness - rightWallShift}
          y={top}
          width={wallThickness + rightWallShift}
          height={MOLD_HEIGHT}
          fill={MOLD_WALL_FILL}
          fillOpacity={frame >= FIX_START ? rightWallGlow + holdPulse : 0.1}
        />

        {/* Right wall amber glow trail during adjustment */}
        {frame >= FIX_START && frame <= FIX_END && (
          <rect
            x={left + MOLD_WIDTH - wallThickness - rightWallShift - 6}
            y={top + 60}
            width={8}
            height={MOLD_HEIGHT - 120}
            fill={AMBER}
            fillOpacity={interpolate(
              frame,
              [FIX_START, FIX_START + 15, FIX_START + 30],
              [0, 0.5, 0],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            )}
            rx={4}
          />
        )}

        {/* Cavity */}
        <rect
          x={cavityX}
          y={cavityY}
          width={cavityW - rightWallShift}
          height={cavityH}
          fill={MOLD_CAVITY}
          fillOpacity={0.3}
        />

        {/* Cavity opening at bottom (nozzle area) */}
        <rect
          x={MOLD_CENTER_X - 30}
          y={top + MOLD_HEIGHT - 10}
          width={60}
          height={20}
          fill={MOLD_CAVITY}
          fillOpacity={0.25}
        />

        {/* Top cap of mold */}
        <rect
          x={left + wallThickness}
          y={top}
          width={cavityW}
          height={40}
          fill={MOLD_WALL_FILL}
          fillOpacity={0.1 + holdPulse}
        />

        {/* Nozzle indicator lines */}
        <line
          x1={MOLD_CENTER_X - 15}
          y1={top - 10}
          x2={MOLD_CENTER_X - 15}
          y2={top + 10}
          stroke={MOLD_STROKE}
          strokeWidth={1.5}
          strokeOpacity={0.4}
        />
        <line
          x1={MOLD_CENTER_X + 15}
          y1={top - 10}
          x2={MOLD_CENTER_X + 15}
          y2={top + 10}
          stroke={MOLD_STROKE}
          strokeWidth={1.5}
          strokeOpacity={0.4}
        />
      </svg>
    </div>
  );
};

export default MoldDiagram;
