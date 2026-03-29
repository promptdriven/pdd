import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface WavyUnderlineProps {
  centerX: number;
  y: number;
  width: number;
  color: string;
  opacity: number;
  strokeWidth: number;
  startFrame: number;
  duration: number;
}

/**
 * A hand-drawn style wavy underline, drawn via SVG stroke-dashoffset animation.
 */
export const WavyUnderline: React.FC<WavyUnderlineProps> = ({
  centerX,
  y,
  width,
  color,
  opacity,
  strokeWidth,
  startFrame,
  duration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Build a wavy path centered horizontally
  const halfWidth = width / 2;
  const startX = centerX - halfWidth;
  const endX = centerX + halfWidth;
  const waveAmplitude = 3;
  const waveFrequency = 16; // px per wave segment

  let d = `M ${startX} ${y}`;
  for (let x = startX; x < endX; x += waveFrequency) {
    const nextX = Math.min(x + waveFrequency, endX);
    const midX = (x + nextX) / 2;
    // Alternate wave direction
    const dir = Math.floor((x - startX) / waveFrequency) % 2 === 0 ? -1 : 1;
    d += ` Q ${midX} ${y + waveAmplitude * dir}, ${nextX} ${y}`;
  }

  // Approximate path length
  const pathLength = width * 1.1;
  const dashOffset = pathLength * (1 - progress);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <path
        d={d}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        opacity={opacity}
        strokeDasharray={pathLength}
        strokeDashoffset={dashOffset}
      />
    </svg>
  );
};

export default WavyUnderline;
