import React, { useMemo } from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  DataPoint,
  mapX,
  mapY,
} from "./constants";

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth: number;
  startFrame: number;
  drawDuration: number;
  easing?: (t: number) => number;
  dashArray?: string;
  glowRadius?: number;
  glowOpacity?: number;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  startFrame,
  drawDuration,
  easing = Easing.inOut(Easing.cubic),
  dashArray,
  glowRadius = 0,
  glowOpacity = 0,
}) => {
  const frame = useCurrentFrame();

  // Build the SVG path and compute total length
  const { pathD, segments } = useMemo(() => {
    const pts = data.map((pt) => ({ sx: mapX(pt.x), sy: mapY(pt.y) }));
    let d = "";
    const segs: number[] = [];
    let totalLen = 0;
    for (let i = 0; i < pts.length; i++) {
      if (i === 0) {
        d += `M ${pts[i].sx} ${pts[i].sy}`;
        segs.push(0);
      } else {
        d += ` L ${pts[i].sx} ${pts[i].sy}`;
        const dx = pts[i].sx - pts[i - 1].sx;
        const dy = pts[i].sy - pts[i - 1].sy;
        totalLen += Math.sqrt(dx * dx + dy * dy);
        segs.push(totalLen);
      }
    }
    return { pathD: d, segments: segs, totalLength: totalLen };
  }, [data]);

  const totalLength = segments[segments.length - 1] || 1;

  const drawProgress = interpolate(
    frame,
    [startFrame, startFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing,
    }
  );

  const visibleLength = drawProgress * totalLength;
  const hiddenLength = totalLength - visibleLength;

  // Fade in from 0 to full over first 10 frames
  const opacity = interpolate(
    frame,
    [startFrame, Math.min(startFrame + 10, startFrame + drawDuration)],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  if (frame < startFrame) return null;

  const filterId = `glow-${color.replace("#", "")}-${startFrame}`;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {glowRadius > 0 && (
        <defs>
          <filter id={filterId} x="-20%" y="-20%" width="140%" height="140%">
            <feGaussianBlur stdDeviation={glowRadius} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>
      )}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeDasharray={
          dashArray || `${totalLength}`
        }
        strokeDashoffset={dashArray ? undefined : hiddenLength}
        strokeLinecap="round"
        strokeLinejoin="round"
        opacity={opacity}
        style={
          dashArray
            ? {
                clipPath: `inset(0 ${((1 - drawProgress) * 100).toFixed(1)}% 0 0)`,
              }
            : undefined
        }
        filter={
          glowRadius > 0 && glowOpacity > 0
            ? `url(#${filterId})`
            : undefined
        }
      />
    </svg>
  );
};

export default AnimatedLine;
