// WavyUnderline.tsx — hand-drawn wavy underline via SVG path stroke animation
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface WavyUnderlineProps {
  /** Center X of the underline */
  centerX: number;
  /** Y position of the underline */
  y: number;
  /** Approximate width in px */
  width: number;
  color: string;
  opacity: number;
  strokeWidth: number;
  /** Frame at which drawing begins (absolute, not relative to Sequence) */
  startFrame: number;
  /** Duration in frames to draw the line */
  duration: number;
}

/**
 * Builds an SVG cubic-bezier path that has a gentle wave — imitating a
 * hand-drawn underline. The path is revealed left-to-right via
 * stroke-dashoffset.
 */
const WavyUnderline: React.FC<WavyUnderlineProps> = ({
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

  const halfW = width / 2;
  const x0 = centerX - halfW;
  const x1 = centerX + halfW;

  // Build a gently wavy cubic path with 4 segments
  const segW = width / 4;
  const wave = 3; // amplitude in px — subtle
  const d = [
    `M ${x0} ${y}`,
    `C ${x0 + segW * 0.5} ${y - wave}, ${x0 + segW * 0.5} ${y + wave}, ${x0 + segW} ${y + 1}`,
    `C ${x0 + segW * 1.5} ${y - wave}, ${x0 + segW * 1.5} ${y + wave}, ${x0 + segW * 2} ${y - 1}`,
    `C ${x0 + segW * 2.5} ${y + wave}, ${x0 + segW * 2.5} ${y - wave}, ${x0 + segW * 3} ${y + 1}`,
    `C ${x0 + segW * 3.5} ${y - wave}, ${x0 + segW * 3.5} ${y + wave}, ${x1} ${y}`,
  ].join(" ");

  // Total path length (rough overestimate is fine for dasharray)
  const pathLen = width * 1.2;

  const progress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    },
  );

  const dashOffset = pathLen * (1 - progress);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <path
        d={d}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeDasharray={pathLen}
        strokeDashoffset={dashOffset}
        opacity={opacity}
      />
    </svg>
  );
};

export default WavyUnderline;
