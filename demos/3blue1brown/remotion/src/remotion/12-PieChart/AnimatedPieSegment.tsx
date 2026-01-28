import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import { CHART_CENTER, CHART_RADIUS, SEGMENT_GAP, STROKE_WIDTH, COLORS } from "./constants";

interface AnimatedPieSegmentProps {
  startAngle: number;        // In degrees, 0 = 12 o'clock
  endAngle: number;          // In degrees
  color: string;
  startFrame: number;
  endFrame: number;
  pulseStartFrame?: number;
  shouldPulse?: boolean;
}

// Convert degrees to radians, adjusting so 0° is at 12 o'clock
const degreesToRadians = (degrees: number) => {
  return ((degrees - 90) * Math.PI) / 180;
};

// Create an arc path for the pie segment
const createArcPath = (
  centerX: number,
  centerY: number,
  radius: number,
  startAngle: number,
  endAngle: number,
  gap: number = 0
): string => {
  // Adjust for gap
  const adjustedStartAngle = startAngle + (gap / radius) * (180 / Math.PI);
  const adjustedEndAngle = endAngle - (gap / radius) * (180 / Math.PI);

  const startRad = degreesToRadians(adjustedStartAngle);
  const endRad = degreesToRadians(adjustedEndAngle);

  const x1 = centerX + radius * Math.cos(startRad);
  const y1 = centerY + radius * Math.sin(startRad);
  const x2 = centerX + radius * Math.cos(endRad);
  const y2 = centerY + radius * Math.sin(endRad);

  // Large arc flag: 1 if angle > 180°
  const largeArcFlag = (adjustedEndAngle - adjustedStartAngle) > 180 ? 1 : 0;

  return `M ${centerX} ${centerY} L ${x1} ${y1} A ${radius} ${radius} 0 ${largeArcFlag} 1 ${x2} ${y2} Z`;
};

export const AnimatedPieSegment: React.FC<AnimatedPieSegmentProps> = ({
  startAngle,
  endAngle,
  color,
  startFrame,
  endFrame,
  pulseStartFrame = 360,
  shouldPulse = false,
}) => {
  const frame = useCurrentFrame();

  // Animate the segment drawing from startAngle to endAngle
  const animatedEndAngle = interpolate(
    frame,
    [startFrame, endFrame],
    [startAngle, endAngle],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Only render if animation has started
  if (frame < startFrame) {
    return null;
  }

  // Pulse animation for maintenance segment
  let scale = 1;
  if (shouldPulse && frame >= pulseStartFrame) {
    const pulseFrame = frame - pulseStartFrame;
    // Sin wave: 1.0 → 1.02 → 1.0 over ~60 frames (2 second period)
    scale = 1 + 0.02 * Math.sin((pulseFrame / 30) * Math.PI);
  }

  // Create the pie slice path
  const path = createArcPath(
    CHART_CENTER.x,
    CHART_CENTER.y,
    CHART_RADIUS * scale,
    startAngle,
    animatedEndAngle,
    SEGMENT_GAP
  );

  // Drop shadow filter
  const shadowId = `shadow-${color.replace("#", "")}`;

  return (
    <svg
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        overflow: "visible",
      }}
    >
      <defs>
        {/* Soft drop shadow */}
        <filter id={shadowId} x="-50%" y="-50%" width="200%" height="200%">
          <feDropShadow
            dx="4"
            dy="6"
            stdDeviation="8"
            floodColor="rgba(0,0,0,0.4)"
          />
        </filter>
        {/* Subtle 3D gradient effect */}
        <linearGradient
          id={`gradient-${color.replace("#", "")}`}
          x1="0%"
          y1="0%"
          x2="100%"
          y2="100%"
        >
          <stop offset="0%" stopColor={color} stopOpacity="1" />
          <stop offset="50%" stopColor={color} stopOpacity="0.95" />
          <stop offset="100%" stopColor={adjustBrightness(color, -20)} stopOpacity="1" />
        </linearGradient>
      </defs>
      <path
        d={path}
        fill={`url(#gradient-${color.replace("#", "")})`}
        stroke={COLORS.STROKE}
        strokeWidth={STROKE_WIDTH}
        filter={`url(#${shadowId})`}
        style={{
          transformOrigin: `${CHART_CENTER.x}px ${CHART_CENTER.y}px`,
        }}
      />
    </svg>
  );
};

// Helper function to adjust color brightness
function adjustBrightness(hex: string, percent: number): string {
  const num = parseInt(hex.replace("#", ""), 16);
  const r = Math.min(255, Math.max(0, (num >> 16) + percent));
  const g = Math.min(255, Math.max(0, ((num >> 8) & 0x00ff) + percent));
  const b = Math.min(255, Math.max(0, (num & 0x0000ff) + percent));
  return `#${((r << 16) | (g << 8) | b).toString(16).padStart(6, "0")}`;
}
