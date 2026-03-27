import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface DrawLineProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  color: string;
  strokeWidth: number;
  drawStartFrame: number;
  drawDuration: number;
}

export const DrawLine: React.FC<DrawLineProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  color,
  strokeWidth,
  drawStartFrame,
  drawDuration,
}) => {
  const frame = useCurrentFrame();

  const dx = toX - fromX;
  const dy = toY - fromY;
  const lineLength = Math.sqrt(dx * dx + dy * dy);

  const progress = interpolate(
    frame,
    [drawStartFrame, drawStartFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <line
        x1={fromX}
        y1={fromY}
        x2={fromX + dx * progress}
        y2={fromY + dy * progress}
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
      />
      {/* Small glow effect */}
      <line
        x1={fromX}
        y1={fromY}
        x2={fromX + dx * progress}
        y2={fromY + dy * progress}
        stroke={color}
        strokeWidth={strokeWidth + 4}
        strokeLinecap="round"
        opacity={0.15}
        filter="url(#lineGlow)"
      />
      <defs>
        <filter id="lineGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
    </svg>
  );
};

interface DrawArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  color: string;
  strokeWidth: number;
  drawStartFrame: number;
  drawDuration: number;
  arrowOpacity?: number;
}

export const DrawArrow: React.FC<DrawArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  color,
  strokeWidth,
  drawStartFrame,
  drawDuration,
  arrowOpacity = 0.3,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [drawStartFrame, drawStartFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const opacity = interpolate(
    frame,
    [drawStartFrame, drawStartFrame + drawDuration],
    [0, arrowOpacity],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const dx = toX - fromX;
  const dy = toY - fromY;

  const currentX = fromX + dx * progress;
  const currentY = fromY + dy * progress;

  // Arrowhead
  const angle = Math.atan2(dy, dx);
  const arrowLen = 10;
  const arrowAngle = Math.PI / 6;
  const ax1 = currentX - arrowLen * Math.cos(angle - arrowAngle);
  const ay1 = currentY - arrowLen * Math.sin(angle - arrowAngle);
  const ax2 = currentX - arrowLen * Math.cos(angle + arrowAngle);
  const ay2 = currentY - arrowLen * Math.sin(angle + arrowAngle);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <line
        x1={fromX}
        y1={fromY}
        x2={currentX}
        y2={currentY}
        stroke={color}
        strokeWidth={strokeWidth}
        strokeDasharray="6 4"
        opacity={opacity}
      />
      {progress > 0.8 && (
        <polygon
          points={`${currentX},${currentY} ${ax1},${ay1} ${ax2},${ay2}`}
          fill={color}
          opacity={opacity}
        />
      )}
    </svg>
  );
};
