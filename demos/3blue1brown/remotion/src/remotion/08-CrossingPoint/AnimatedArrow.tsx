import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { BEATS, COLORS } from "./constants";

interface AnimatedArrowProps {
  labelX: number;
  labelY: number;
  targetX: number;
  targetY: number;
}

export const AnimatedArrow: React.FC<AnimatedArrowProps> = ({
  labelX,
  labelY,
  targetX,
  targetY,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // Arrow draws in slightly after label starts appearing
  const arrowProgress = interpolate(
    frame,
    [BEATS.LABEL_FADE_START + 20, BEATS.LABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Arrow opacity matches label
  const arrowOpacity = interpolate(
    frame,
    [BEATS.LABEL_FADE_START + 20, BEATS.LABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  if (arrowProgress <= 0) {
    return null;
  }

  // Calculate the direction vector from label to target
  const dx = targetX - labelX;
  const dy = targetY - labelY;
  const distance = Math.sqrt(dx * dx + dy * dy);

  // Normalize direction
  const nx = dx / distance;
  const ny = dy / distance;

  // Start point (from label, offset slightly)
  const startX = labelX + nx * 60;  // Start 60px from label center
  const startY = labelY + ny * 30;

  // End point (to marker, offset by marker radius)
  const endX = targetX - nx * 35;   // Stop before marker
  const endY = targetY - ny * 35;

  // Current end point based on progress
  const currentEndX = startX + (endX - startX) * arrowProgress;
  const currentEndY = startY + (endY - startY) * arrowProgress;

  // Arrowhead size
  const arrowHeadLength = 15;
  const arrowHeadAngle = Math.PI / 6; // 30 degrees

  // Calculate arrowhead points
  const angle = Math.atan2(currentEndY - startY, currentEndX - startX);

  const arrowHead1X =
    currentEndX - arrowHeadLength * Math.cos(angle - arrowHeadAngle);
  const arrowHead1Y =
    currentEndY - arrowHeadLength * Math.sin(angle - arrowHeadAngle);
  const arrowHead2X =
    currentEndX - arrowHeadLength * Math.cos(angle + arrowHeadAngle);
  const arrowHead2Y =
    currentEndY - arrowHeadLength * Math.sin(angle + arrowHeadAngle);

  // Only show arrowhead when line is mostly drawn
  const showArrowhead = arrowProgress > 0.7;
  const arrowheadOpacity = interpolate(
    arrowProgress,
    [0.7, 1],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        {/* Glow filter for arrow */}
        <filter id="arrowGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="3" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Arrow line */}
      <line
        x1={startX}
        y1={startY}
        x2={currentEndX}
        y2={currentEndY}
        stroke={COLORS.MARKER}
        strokeWidth={3}
        opacity={arrowOpacity}
        filter="url(#arrowGlow)"
        strokeLinecap="round"
      />

      {/* Arrowhead */}
      {showArrowhead && (
        <polygon
          points={`${currentEndX},${currentEndY} ${arrowHead1X},${arrowHead1Y} ${arrowHead2X},${arrowHead2Y}`}
          fill={COLORS.MARKER}
          opacity={arrowOpacity * arrowheadOpacity}
          filter="url(#arrowGlow)"
        />
      )}
    </svg>
  );
};
