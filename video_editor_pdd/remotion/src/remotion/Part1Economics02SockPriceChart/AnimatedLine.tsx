import React, { useMemo } from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  DataPoint,
  xToPixel,
  yToPixel,
  X_MIN,
  X_MAX,
  LINE_DRAW_START,
  LINE_DRAW_END,
  MORPH_START,
  MORPH_END,
  interpolateData,
} from "./constants";

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth: number;
  /** If true, this line fades out during the morph phase (600-720) */
  fadeOutOnMorph?: boolean;
}

/**
 * Renders a smooth SVG path that draws progressively from left to right.
 * Uses fine-grained sampling for smooth curves between data points.
 */
export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  fadeOutOnMorph = false,
}) => {
  const frame = useCurrentFrame();

  // Draw progress: 0→1 over frames 30-600
  // Slow down near crossing (frame ~150), speed up after
  const rawProgress = interpolate(
    frame,
    [LINE_DRAW_START, LINE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Morph fade-out
  const morphOpacity = fadeOutOnMorph
    ? interpolate(frame, [MORPH_START, MORPH_END], [1, 0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.in(Easing.quad),
      })
    : 1;

  // Generate a densely sampled path for the visible portion of the line
  const pathD = useMemo(() => {
    // The current x-value extent based on progress
    const currentMaxX = X_MIN + rawProgress * (X_MAX - X_MIN);

    // Sample at fine intervals for smooth curves
    const SAMPLE_COUNT = 200;
    const points: { px: number; py: number }[] = [];

    for (let i = 0; i <= SAMPLE_COUNT; i++) {
      const x = X_MIN + (i / SAMPLE_COUNT) * (currentMaxX - X_MIN);
      if (x > currentMaxX) break;

      const y = interpolateData(data, x);
      points.push({ px: xToPixel(x), py: yToPixel(y) });
    }

    if (points.length < 2) return "";

    // Build SVG path
    let d = `M ${points[0].px} ${points[0].py}`;
    for (let i = 1; i < points.length; i++) {
      d += ` L ${points[i].px} ${points[i].py}`;
    }
    return d;
  }, [rawProgress, data]);

  if (!pathD) return null;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Glow effect behind the line */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth + 6}
        strokeLinecap="round"
        strokeLinejoin="round"
        opacity={0.15 * morphOpacity}
      />
      {/* Main line */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        opacity={morphOpacity}
      />
    </svg>
  );
};

export default AnimatedLine;
