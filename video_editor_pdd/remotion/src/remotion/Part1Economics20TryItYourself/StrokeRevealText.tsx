// StrokeRevealText.tsx — SVG text that "writes" itself via stroke-dashoffset animation
import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface StrokeRevealTextProps {
  text: string;
  fontFamily: string;
  fontSize: number;
  color: string;
  centerX: number;
  centerY: number;
  rotationDeg: number;
  /** Frame at which the stroke animation begins (relative to parent Sequence) */
  startFrame: number;
  /** How many frames the stroke-reveal takes */
  duration: number;
}

/**
 * Renders text that appears to be written by hand using an SVG stroke-dashoffset
 * animation. The text is first invisible, then the stroke draws in left→right,
 * and finally the fill fades in to leave solid text.
 */
const StrokeRevealText: React.FC<StrokeRevealTextProps> = ({
  text,
  fontFamily,
  fontSize,
  color,
  centerX,
  centerY,
  rotationDeg,
  startFrame,
  duration,
}) => {
  const frame = useCurrentFrame();

  // Generous dash length to cover the full text width
  const dashLength = text.length * fontSize * 0.7;

  // Stroke draws in over `duration` frames
  const strokeProgress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    },
  );

  // Fill fades in during the last third of the stroke animation
  const fillFadeStart = startFrame + Math.round(duration * 0.6);
  const fillFadeEnd = startFrame + duration;
  const fillOpacity = interpolate(
    frame,
    [fillFadeStart, fillFadeEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    },
  );

  const dashOffset = dashLength * (1 - strokeProgress);

  const textStyle: React.CSSProperties = useMemo(
    () => ({
      fontFamily,
      fontSize,
      dominantBaseline: "central" as const,
      textAnchor: "middle" as const,
    }),
    [fontFamily, fontSize],
  );

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        overflow: "visible",
      }}
    >
      <g transform={`rotate(${rotationDeg} ${centerX} ${centerY})`}>
        {/* Stroke layer (the "writing" effect) */}
        <text
          x={centerX}
          y={centerY}
          style={textStyle}
          fill="none"
          stroke={color}
          strokeWidth={1.5}
          strokeDasharray={dashLength}
          strokeDashoffset={dashOffset}
        >
          {text}
        </text>

        {/* Fill layer (solid text that fades in after stroke finishes) */}
        <text
          x={centerX}
          y={centerY}
          style={textStyle}
          fill={color}
          fillOpacity={fillOpacity}
          stroke="none"
        >
          {text}
        </text>
      </g>
    </svg>
  );
};

export default StrokeRevealText;
