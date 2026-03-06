import React from "react";
import { BLUE, GREEN, WHITE, FONT_FAMILY } from "./constants";

interface ExpandingArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  progress: number;
  opacity: number;
  labelOpacity: number;
}

export const ExpandingArrow: React.FC<ExpandingArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  progress,
  opacity,
  labelOpacity,
}) => {
  const currentEndX = fromX + (toX - fromX) * progress;
  const arrowLength = toX - fromX;
  const midY = fromY;

  // Arrow thickness grows from 4px to 24px along its length
  const startWidth = 4;
  const endWidth = 24;
  const currentEndWidth = startWidth + (endWidth - startWidth) * progress;

  // Build a tapered polygon for the arrow body
  const halfStart = startWidth / 2;
  const halfEnd = currentEndWidth / 2;

  // Arrowhead dimensions
  const arrowHeadLength = 30 * progress;
  const arrowHeadWidth = 36 * progress;
  const bodyEndX = currentEndX - arrowHeadLength;

  return (
    <>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0, opacity }}
      >
        <defs>
          <linearGradient id="arrowGrad" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor={BLUE} />
            <stop offset="100%" stopColor={GREEN} />
          </linearGradient>
          <filter id="arrowGlow">
            <feGaussianBlur stdDeviation="6" />
          </filter>
        </defs>

        {/* Glow layer */}
        <polygon
          points={`
            ${fromX},${midY - halfStart}
            ${bodyEndX},${midY - halfEnd}
            ${bodyEndX},${midY - arrowHeadWidth / 2}
            ${currentEndX},${midY}
            ${bodyEndX},${midY + arrowHeadWidth / 2}
            ${bodyEndX},${midY + halfEnd}
            ${fromX},${midY + halfStart}
          `}
          fill="url(#arrowGrad)"
          opacity={0.2}
          filter="url(#arrowGlow)"
        />

        {/* Main arrow body (tapered) + arrowhead */}
        <polygon
          points={`
            ${fromX},${midY - halfStart}
            ${bodyEndX},${midY - halfEnd}
            ${bodyEndX},${midY - arrowHeadWidth / 2}
            ${currentEndX},${midY}
            ${bodyEndX},${midY + arrowHeadWidth / 2}
            ${bodyEndX},${midY + halfEnd}
            ${fromX},${midY + halfStart}
          `}
          fill="url(#arrowGrad)"
          opacity={0.9}
        />
      </svg>

      {/* Label above arrow: "5-10x expansion" */}
      <div
        style={{
          position: "absolute",
          left: fromX,
          top: midY - 55,
          width: arrowLength,
          textAlign: "center",
          opacity: labelOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 700,
          fontSize: 28,
          color: WHITE,
          textShadow: "0 2px 12px rgba(0,0,0,0.5)",
        }}
      >
        5-10x expansion
      </div>
    </>
  );
};
