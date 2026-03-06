import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_X,
  MOLD_Y,
  MOLD_W,
  MOLD_H,
  MOLD_FILL,
  MOLD_GLOW_COLOR,
  MOLD_CAVITY_W,
  MOLD_CAVITY_H,
  MOLD_CAVITY_FILL,
  MOLD_LABEL_TEXT,
  MOLD_FADE_START,
  MOLD_FADE_END,
  LABEL_FADE_START,
  LABEL_FADE_END,
  ACCENT_ORANGE,
  FADEOUT_START,
  FADEOUT_END,
  FIX_COLOR,
  WRENCH_APPEAR,
  WRENCH_FLASH_DURATION,
} from "./constants";

interface MoldShapeProps {
  showWrench: boolean;
  wrenchScale: number;
}

export const MoldShape: React.FC<MoldShapeProps> = ({
  showWrench,
  wrenchScale,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [MOLD_FADE_START, MOLD_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Pulsing glow on the mold border
  const glowPulse = interpolate(
    Math.sin(frame * 0.08),
    [-1, 1],
    [0.6, 1.0]
  );

  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Border flashes green when wrench appears, then returns to orange
  const isFlashing =
    frame >= WRENCH_APPEAR && frame < WRENCH_APPEAR + WRENCH_FLASH_DURATION;
  const greenFlash = isFlashing
    ? interpolate(
        Math.sin((frame - WRENCH_APPEAR) * 0.4),
        [-1, 1],
        [0.3, 1.0]
      )
    : 0;

  const borderColor = greenFlash > 0.5 ? FIX_COLOR : MOLD_GLOW_COLOR;

  const cavityX = MOLD_X + (MOLD_W - MOLD_CAVITY_W) / 2;
  const cavityY = MOLD_Y + (MOLD_H - MOLD_CAVITY_H) / 2;

  // Exit slot on the right side of the mold
  const exitY = MOLD_Y + MOLD_H / 2;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, opacity }}
    >
      <defs>
        <filter id="moldGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Mold body */}
      <rect
        x={MOLD_X}
        y={MOLD_Y}
        width={MOLD_W}
        height={MOLD_H}
        rx={12}
        ry={12}
        fill={MOLD_FILL}
        stroke={borderColor}
        strokeWidth={4}
        opacity={glowPulse}
        filter="url(#moldGlow)"
      />

      {/* Cavity cutout */}
      <rect
        x={cavityX}
        y={cavityY}
        width={MOLD_CAVITY_W}
        height={MOLD_CAVITY_H}
        rx={8}
        ry={8}
        fill={MOLD_CAVITY_FILL}
        stroke={borderColor}
        strokeWidth={1.5}
        opacity={0.8}
      />

      {/* Exit slot on right side */}
      <rect
        x={MOLD_X + MOLD_W - 4}
        y={exitY - 15}
        width={20}
        height={30}
        rx={4}
        fill={MOLD_FILL}
        stroke={borderColor}
        strokeWidth={2}
        opacity={0.9}
      />

      {/* "MOLD" label */}
      <text
        x={MOLD_X + MOLD_W / 2}
        y={MOLD_Y + MOLD_H + 30}
        textAnchor="middle"
        fill={ACCENT_ORANGE}
        fontSize={20}
        fontFamily="Inter, sans-serif"
        fontWeight={700}
        letterSpacing="0.15em"
        opacity={labelOpacity}
      >
        {MOLD_LABEL_TEXT}
      </text>

      {/* Wrench icon (32x32, appears on mold with spring) */}
      {showWrench && (
        <g
          transform={`translate(${MOLD_X + MOLD_W / 2}, ${MOLD_Y - 10}) scale(${wrenchScale})`}
          opacity={wrenchScale}
        >
          <g transform="translate(-16, -16)">
            {/* Wrench SVG path */}
            <path
              d="M6.3 12.3l10.7 10.7 2-2L8.3 10.3c.3-.9.5-1.8.5-2.8C8.8 3.4 5.4 0 1.3 0L5 3.7 3.7 5 0 1.3c0 4.1 3.4 7.5 7.5 7.5 1-.1 1.9-.2 2.8-.5zM25.7 19.7L15 9l2-2 10.7 10.7c1.2 1.2 1.2 3.1 0 4.2-1.2 1.2-3.1 1.2-4.2 0z"
              fill={FIX_COLOR}
              transform="scale(1.2)"
            />
          </g>
        </g>
      )}
    </svg>
  );
};

export default MoldShape;
