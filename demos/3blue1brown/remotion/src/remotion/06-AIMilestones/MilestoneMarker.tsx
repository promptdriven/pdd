import React from "react";
import { interpolate, spring, useCurrentFrame, useVideoConfig } from "remotion";
import { SPRING_CONFIG, BEATS } from "./constants";

interface MilestoneMarkerProps {
  x: number;
  y: number;
  name: string;
  color: string;
  startFrame: number;
  labelPosition?: "top" | "bottom" | "left" | "right";
  labelOffsetY?: number;
  impactScale?: number;
}

export const MilestoneMarker: React.FC<MilestoneMarkerProps> = ({
  x,
  y,
  name,
  color,
  startFrame,
  labelPosition = "top",
  labelOffsetY = 0,
  impactScale: impactScaleProp = 1.0,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Don't render before start frame
  if (frame < startFrame) {
    return null;
  }

  const localFrame = frame - startFrame;

  // Marker pops in with spring animation
  const markerScale = spring({
    frame: localFrame,
    fps,
    config: SPRING_CONFIG,
  });

  // Impact effect - quick scale up then settle
  const impactScale = spring({
    frame: localFrame,
    fps,
    config: {
      damping: 8,
      stiffness: 300,
    },
    from: 0,
    to: 1,
  });

  // Label fade in slightly after marker
  const labelOpacity = interpolate(
    localFrame,
    [15, 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Subtle continuous pulse during hold phase
  const isHoldPhase = frame >= BEATS.HOLD_START;
  const pulseScale = isHoldPhase
    ? 1 + 0.05 * Math.sin((frame - BEATS.HOLD_START) * 0.15)
    : 1;

  const pulseOpacity = isHoldPhase
    ? 0.3 + 0.15 * Math.sin((frame - BEATS.HOLD_START) * 0.15)
    : 0;

  const markerRadius = 16 * impactScaleProp;

  // Impact ripple effect
  const rippleScale = interpolate(
    localFrame,
    [0, 30],
    [1, 3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const rippleOpacity = interpolate(
    localFrame,
    [0, 30],
    [0.6, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Calculate label position
  const getLabelStyle = (): React.CSSProperties => {
    const baseStyle: React.CSSProperties = {
      position: "absolute",
      fontFamily: "Inter, system-ui, sans-serif",
      fontSize: 22,
      fontWeight: 600,
      color: color,
      opacity: labelOpacity,
      textShadow: `0 0 10px ${color}40, 0 2px 4px rgba(0,0,0,0.8)`,
      whiteSpace: "nowrap",
    };

    switch (labelPosition) {
      case "top":
        return {
          ...baseStyle,
          left: x,
          top: y - markerRadius - 25 + labelOffsetY,
          transform: "translateX(-50%)",
        };
      case "bottom":
        return {
          ...baseStyle,
          left: x,
          top: y + markerRadius + 10 + labelOffsetY,
          transform: "translateX(-50%)",
        };
      case "left":
        return {
          ...baseStyle,
          left: x - markerRadius - 15,
          top: y + labelOffsetY,
          transform: "translate(-100%, -50%)",
        };
      case "right":
        return {
          ...baseStyle,
          left: x + markerRadius + 15,
          top: y + labelOffsetY,
          transform: "translateY(-50%)",
        };
      default:
        return baseStyle;
    }
  };

  return (
    <>
      <svg
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          pointerEvents: "none",
          overflow: "visible",
        }}
      >
        <defs>
          {/* Glow filter for marker */}
          <filter id={`glow-${name}`} x="-100%" y="-100%" width="300%" height="300%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="6" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>

          {/* Radial gradient for pulse */}
          <radialGradient id={`pulse-${name}`} cx="50%" cy="50%" r="50%">
            <stop offset="0%" stopColor={color} stopOpacity="0.6" />
            <stop offset="50%" stopColor={color} stopOpacity="0.2" />
            <stop offset="100%" stopColor={color} stopOpacity="0" />
          </radialGradient>
        </defs>

        {/* Impact ripple */}
        {localFrame < 30 && (
          <circle
            cx={x}
            cy={y}
            r={markerRadius * rippleScale}
            fill="none"
            stroke={color}
            strokeWidth={2}
            opacity={rippleOpacity}
          />
        )}

        {/* Hold phase pulse */}
        {isHoldPhase && (
          <circle
            cx={x}
            cy={y}
            r={markerRadius * 2 * pulseScale}
            fill={`url(#pulse-${name})`}
            opacity={pulseOpacity}
          />
        )}

        {/* Main marker with glow */}
        <circle
          cx={x}
          cy={y}
          r={markerRadius * markerScale * impactScale}
          fill={color}
          filter={`url(#glow-${name})`}
        />

        {/* Inner highlight */}
        <circle
          cx={x}
          cy={y}
          r={(markerRadius - 5) * markerScale * impactScale}
          fill="rgba(255, 255, 255, 0.3)"
        />

        {/* Vertical line connecting to x-axis (drop indicator) */}
        <line
          x1={x}
          y1={y + markerRadius * markerScale}
          x2={x}
          y2={y + 60}
          stroke={color}
          strokeWidth={2}
          strokeDasharray="4,4"
          opacity={labelOpacity * 0.5}
        />
      </svg>

      {/* Label */}
      <div style={getLabelStyle()}>
        {name}
      </div>
    </>
  );
};
