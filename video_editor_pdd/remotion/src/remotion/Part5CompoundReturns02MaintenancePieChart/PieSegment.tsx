import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

/**
 * Draws a single pie segment as an SVG arc path that fills over time.
 * Uses a conic/arc approach: we draw from startAngle to endAngle
 * (in degrees, 0 = 12 o'clock, clockwise).
 */

interface PieSegmentProps {
  cx: number;
  cy: number;
  radius: number;
  startAngleDeg: number;
  endAngleDeg: number;
  color: string;
  strokeColor: string;
  strokeWidth: number;
  fillStartFrame: number;
  fillDuration: number;
  /** Optional glow color */
  glowColor?: string;
  /** Pulse amplitude 0..1 */
  pulseAmplitude?: number;
  pulseStartFrame?: number;
  pulseEndFrame?: number;
  /** Morph flatten progress 0..1 */
  morphProgress?: number;
}

/** Convert angle in degrees (0=top, clockwise) to SVG coordinates */
function polarToCartesian(
  cx: number,
  cy: number,
  r: number,
  angleDeg: number
): { x: number; y: number } {
  // SVG: 0 deg = right, angles go clockwise after we negate
  // We want 0 deg = top (12 o'clock), clockwise
  const angleRad = ((angleDeg - 90) * Math.PI) / 180;
  return {
    x: cx + r * Math.cos(angleRad),
    y: cy + r * Math.sin(angleRad),
  };
}

function describeArc(
  cx: number,
  cy: number,
  r: number,
  startAngle: number,
  endAngle: number
): string {
  const start = polarToCartesian(cx, cy, r, startAngle);
  const end = polarToCartesian(cx, cy, r, endAngle);
  const diff = endAngle - startAngle;
  const largeArc = diff > 180 ? 1 : 0;

  return [
    `M ${cx} ${cy}`,
    `L ${start.x} ${start.y}`,
    `A ${r} ${r} 0 ${largeArc} 1 ${end.x} ${end.y}`,
    "Z",
  ].join(" ");
}

export const PieSegment: React.FC<PieSegmentProps> = ({
  cx,
  cy,
  radius,
  startAngleDeg,
  endAngleDeg,
  color,
  strokeColor,
  strokeWidth,
  fillStartFrame,
  fillDuration,
  glowColor,
  pulseAmplitude = 0,
  pulseStartFrame = 0,
  pulseEndFrame = 0,
  morphProgress = 0,
}) => {
  const frame = useCurrentFrame();

  // Animated sweep progress
  const fillProgress = interpolate(
    frame,
    [fillStartFrame, fillStartFrame + fillDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  if (fillProgress <= 0) return null;

  const currentEndAngle =
    startAngleDeg + (endAngleDeg - startAngleDeg) * fillProgress;

  // Pulse effect
  let pulseScale = 1;
  if (
    pulseAmplitude > 0 &&
    frame >= pulseStartFrame &&
    frame <= pulseEndFrame
  ) {
    const pulsePhase =
      ((frame - pulseStartFrame) / (pulseEndFrame - pulseStartFrame)) *
      Math.PI *
      6;
    pulseScale = 1 + pulseAmplitude * Math.sin(pulsePhase);
  }

  // Morph: flatten segments into horizontal bar at bottom
  const morphCy = morphProgress > 0 ? cy + morphProgress * 200 : cy;

  // Glow filter
  const glowOpacity = interpolate(
    frame,
    [fillStartFrame, fillStartFrame + fillDuration * 0.5, fillStartFrame + fillDuration],
    [0, 0.6, 0.2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // If morphing, use elliptical scaling instead of arc
  if (morphProgress > 0.01) {
    const scaleY = 1 - morphProgress * 0.85;
    const translateY = morphProgress * 200;
    return (
      <g
        transform={`translate(0, ${translateY}) scale(1, ${scaleY})`}
        style={{ transformOrigin: `${cx}px ${cy}px` }}
      >
        <path
          d={describeArc(cx, cy, radius, startAngleDeg, currentEndAngle)}
          fill={color}
          stroke={strokeColor}
          strokeWidth={strokeWidth}
        />
      </g>
    );
  }

  return (
    <g>
      {/* Glow behind segment */}
      {glowColor && glowOpacity > 0 && (
        <path
          d={describeArc(cx, cy, radius + 8, startAngleDeg, currentEndAngle)}
          fill={glowColor}
          opacity={glowOpacity}
          filter="url(#segmentGlow)"
        />
      )}
      {/* Main segment */}
      <path
        d={describeArc(
          cx,
          morphCy,
          radius * pulseScale,
          startAngleDeg,
          currentEndAngle
        )}
        fill={color}
        stroke={strokeColor}
        strokeWidth={strokeWidth}
      />
    </g>
  );
};

/**
 * Returns the midpoint angle and cartesian position for a segment's label connector.
 */
export function getSegmentMidpoint(
  cx: number,
  cy: number,
  r: number,
  startAngle: number,
  endAngle: number
): { angle: number; x: number; y: number } {
  const midAngle = (startAngle + endAngle) / 2;
  const pos = polarToCartesian(cx, cy, r, midAngle);
  return { angle: midAngle, ...pos };
}
