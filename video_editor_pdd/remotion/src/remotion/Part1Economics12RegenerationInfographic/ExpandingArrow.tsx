import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface ExpandingArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  startWidth: number;
  endWidth: number;
  drawStart: number;
  drawEnd: number;
  labelAppearStart: number;
  labelAppearEnd: number;
}

export const ExpandingArrow: React.FC<ExpandingArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  startWidth,
  endWidth,
  drawStart,
  drawEnd,
  labelAppearStart,
  labelAppearEnd,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [drawStart, drawEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.quad),
  });

  const labelOpacity = interpolate(
    frame,
    [labelAppearStart, labelAppearEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (frame < drawStart) return null;

  const arrowLength = toX - fromX;
  const currentEndX = fromX + arrowLength * progress;
  const arrowHeadSize = 16;

  // Build expanding arrow polygon
  const topStartY = fromY - startWidth / 2;
  const bottomStartY = fromY + startWidth / 2;

  // Current thickness at the drawn end
  const currentEndWidth = startWidth + (endWidth - startWidth) * progress;
  const topEndY = fromY - currentEndWidth / 2;
  const bottomEndY = fromY + currentEndWidth / 2;

  // Arrow shaft polygon (trapezoid shape)
  const shaftEndX = Math.max(fromX, currentEndX - arrowHeadSize);

  // Interpolate the width at shaftEndX
  const shaftProgress =
    arrowLength > 0 ? (shaftEndX - fromX) / arrowLength : 0;
  const shaftEndWidth = startWidth + (endWidth - startWidth) * shaftProgress;
  const shaftTopEndY = fromY - shaftEndWidth / 2;
  const shaftBottomEndY = fromY + shaftEndWidth / 2;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <linearGradient
          id="arrowGradient"
          x1={fromX}
          y1={fromY}
          x2={toX}
          y2={fromY}
          gradientUnits="userSpaceOnUse"
        >
          <stop offset="0%" stopColor="#3B82F6" />
          <stop offset="100%" stopColor="#22C55E" />
        </linearGradient>
      </defs>

      {/* Arrow shaft — expanding trapezoid */}
      <polygon
        points={`
          ${fromX},${topStartY}
          ${shaftEndX},${shaftTopEndY}
          ${shaftEndX},${shaftBottomEndY}
          ${fromX},${bottomStartY}
        `}
        fill="url(#arrowGradient)"
        opacity={0.9}
      />

      {/* Arrow head */}
      {progress > 0.1 && (
        <polygon
          points={`
            ${shaftEndX},${shaftTopEndY - 6}
            ${currentEndX},${fromY}
            ${shaftEndX},${shaftBottomEndY + 6}
          `}
          fill="url(#arrowGradient)"
          opacity={0.9}
        />
      )}

      {/* Label above arrow */}
      <text
        x={(fromX + currentEndX) / 2}
        y={fromY - endWidth / 2 - 24}
        fill="#FFFFFF"
        fontSize={28}
        fontFamily="Inter, sans-serif"
        fontWeight={700}
        textAnchor="middle"
        opacity={labelOpacity}
      >
        5-10x expansion
      </text>
    </svg>
  );
};

export default ExpandingArrow;
