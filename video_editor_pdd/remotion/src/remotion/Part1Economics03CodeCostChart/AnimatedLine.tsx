import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  DataPoint,
  buildPathD,
} from "./constants";

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth: number;
  startFrame: number;
  drawDuration: number;
  dashArray?: string;
  glowActive?: boolean;
  glowStartFrame?: number;
  glowEndFrame?: number;
  easing?: (t: number) => number;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  startFrame,
  drawDuration,
  dashArray,
  glowActive = false,
  glowStartFrame = 0,
  glowEndFrame = 0,
  easing = Easing.inOut(Easing.cubic),
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(() => buildPathD(data), [data]);

  const drawProgress = interpolate(
    frame - startFrame,
    [0, drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing,
    }
  );

  // Glow effect for the pulse phase
  let glowOpacity = 0;
  if (glowActive && frame >= glowStartFrame && frame <= glowEndFrame) {
    // Pulsing glow: sine wave over 30-frame cycles
    const cycleFrame = (frame - glowStartFrame) % 30;
    glowOpacity = interpolate(cycleFrame, [0, 15, 30], [0, 0.6, 0], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    });
  }

  // Don't render before start
  if (frame < startFrame) return null;

  // Sanitize color for use in SVG ID (remove # and special chars)
  const safeColor = color.replace(/[^a-zA-Z0-9]/g, "");
  const clipId = `clip-${safeColor}-${startFrame}`;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", left: 0, top: 0 }}
      >
        <defs>
          {/* Clip path for the progressive draw */}
          <clipPath id={clipId}>
            <rect
              x={CHART_LEFT}
              y={CHART_TOP - 20}
              width={(CHART_RIGHT - CHART_LEFT) * drawProgress}
              height={CHART_BOTTOM - CHART_TOP + 40}
            />
          </clipPath>
        </defs>

        {/* Glow layer */}
        {glowActive && glowOpacity > 0 && (
          <path
            d={pathD}
            fill="none"
            stroke={color}
            strokeWidth={strokeWidth + 8}
            strokeDasharray={dashArray || "none"}
            opacity={glowOpacity}
            clipPath={`url(#${clipId})`}
            style={{ filter: "blur(6px)" }}
          />
        )}

        {/* Main line */}
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={strokeWidth}
          strokeDasharray={dashArray || "none"}
          strokeLinecap="round"
          strokeLinejoin="round"
          clipPath={`url(#${clipId})`}
        />
      </svg>
    </div>
  );
};

export default AnimatedLine;
