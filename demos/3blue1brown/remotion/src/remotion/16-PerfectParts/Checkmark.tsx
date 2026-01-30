import React from "react";
import { spring, useCurrentFrame, useVideoConfig } from "remotion";

interface CheckmarkProps {
  cx: number;
  cy: number;
  size: number;
  color: string;
  /** Frame at which this checkmark begins animating in */
  appearFrame: number;
}

/**
 * Animated green checkmark that appears with spring easing.
 * Scales from 0 to full size with a bouncy spring (damping ~15).
 */
export const Checkmark: React.FC<CheckmarkProps> = ({
  cx,
  cy,
  size,
  color,
  appearFrame,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const delayedFrame = frame - appearFrame;
  if (delayedFrame < 0) return null;

  // Spring animation for scale
  const scale = spring({
    frame: delayedFrame,
    fps,
    config: {
      damping: 15,
      stiffness: 120,
      mass: 0.8,
    },
  });

  // Draw path for checkmark: a simple polyline stroke
  const halfSize = size / 2;
  // Checkmark points relative to center: left-mid, center-bottom, right-top
  const x1 = cx - halfSize * 0.4;
  const y1 = cy;
  const x2 = cx - halfSize * 0.05;
  const y2 = cy + halfSize * 0.35;
  const x3 = cx + halfSize * 0.45;
  const y3 = cy - halfSize * 0.35;

  // Stroke draw animation
  const strokeProgress = Math.min(delayedFrame / 10, 1);
  const totalLength = 60; // Approximate path length
  const dashOffset = totalLength * (1 - strokeProgress);

  return (
    <g transform={`translate(${cx}, ${cy}) scale(${scale}) translate(${-cx}, ${-cy})`}>
      {/* Soft green glow behind */}
      <circle cx={cx} cy={cy} r={size * 0.5} fill={color} opacity={0.15 * scale} />

      {/* Checkmark stroke */}
      <polyline
        points={`${x1},${y1} ${x2},${y2} ${x3},${y3}`}
        fill="none"
        stroke={color}
        strokeWidth={3.5}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
      />
    </g>
  );
};
