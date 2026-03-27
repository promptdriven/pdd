import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface MiniMoldAddWallProps {
  x: number;
  y: number;
  color: string;
  animStartFrame: number;
  animDuration: number;
}

export const MiniMoldAddWall: React.FC<MiniMoldAddWallProps> = ({
  x,
  y,
  color,
  animStartFrame,
  animDuration,
}) => {
  const frame = useCurrentFrame();

  const containerOpacity = interpolate(
    frame,
    [animStartFrame, animStartFrame + 10],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Wall slides in from left
  const wallProgress = interpolate(
    frame,
    [animStartFrame + 5, animStartFrame + animDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.4)),
    }
  );

  // Liquid fills after wall is placed
  const liquidProgress = interpolate(
    frame,
    [animStartFrame + animDuration, animStartFrame + animDuration + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const moldWidth = 120;
  const moldHeight = 80;
  const left = x - moldWidth / 2;
  const top = y - moldHeight / 2;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width: moldWidth,
        height: moldHeight,
        opacity: containerOpacity,
      }}
    >
      <svg width={moldWidth} height={moldHeight}>
        {/* Mold outline */}
        <rect
          x={4}
          y={4}
          width={moldWidth - 8}
          height={moldHeight - 8}
          fill="none"
          stroke={color}
          strokeWidth={2}
          rx={4}
          opacity={0.5}
        />
        {/* Existing walls */}
        <line
          x1={30}
          y1={10}
          x2={30}
          y2={moldHeight - 10}
          stroke={color}
          strokeWidth={2}
          opacity={0.4}
        />
        <line
          x1={moldWidth - 30}
          y1={10}
          x2={moldWidth - 30}
          y2={moldHeight - 10}
          stroke={color}
          strokeWidth={2}
          opacity={0.4}
        />
        {/* New wall sliding in */}
        <line
          x1={60}
          y1={10 + (1 - wallProgress) * 30}
          x2={60}
          y2={moldHeight - 10}
          stroke={color}
          strokeWidth={3}
          opacity={wallProgress}
          strokeLinecap="round"
        />
        {/* Wall glow when appearing */}
        {wallProgress > 0.5 && (
          <line
            x1={60}
            y1={10}
            x2={60}
            y2={moldHeight - 10}
            stroke={color}
            strokeWidth={8}
            opacity={0.15 * wallProgress}
            filter="url(#wallGlow)"
          />
        )}
        {/* Liquid filling the compartments */}
        {liquidProgress > 0 && (
          <>
            <rect
              x={32}
              y={moldHeight - 10 - liquidProgress * (moldHeight - 24)}
              width={26}
              height={liquidProgress * (moldHeight - 24)}
              fill={color}
              opacity={0.2}
              rx={2}
            />
            <rect
              x={62}
              y={moldHeight - 10 - liquidProgress * (moldHeight - 24)}
              width={moldWidth - 92}
              height={liquidProgress * (moldHeight - 24)}
              fill={color}
              opacity={0.2}
              rx={2}
            />
          </>
        )}
        <defs>
          <filter
            id="wallGlow"
            x="-100%"
            y="-50%"
            width="300%"
            height="200%"
          >
            <feGaussianBlur stdDeviation="4" />
          </filter>
        </defs>
      </svg>
      {/* Label */}
      <div
        style={{
          position: "absolute",
          bottom: -22,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 11,
          color,
          opacity: wallProgress * 0.7,
          letterSpacing: "0.5px",
        }}
      >
        + wall
      </div>
    </div>
  );
};

interface MiniMoldReshapeProps {
  x: number;
  y: number;
  color: string;
  animStartFrame: number;
  animDuration: number;
}

export const MiniMoldReshape: React.FC<MiniMoldReshapeProps> = ({
  x,
  y,
  color,
  animStartFrame,
  animDuration,
}) => {
  const frame = useCurrentFrame();

  const containerOpacity = interpolate(
    frame,
    [animStartFrame, animStartFrame + 10],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Morph progress for the nozzle reshaping
  const morphProgress = interpolate(
    frame,
    [animStartFrame + 5, animStartFrame + animDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.4)),
    }
  );

  // Glow pulse after reshape
  const glowPulse = interpolate(
    frame,
    [
      animStartFrame + animDuration,
      animStartFrame + animDuration + 15,
      animStartFrame + animDuration + 30,
    ],
    [0, 0.4, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const moldWidth = 120;
  const moldHeight = 80;
  const left = x - moldWidth / 2;
  const top = y - moldHeight / 2;

  // Nozzle shape morphs: original is narrow, reshaped is wider
  const nozzleTopWidth = 16 + morphProgress * 12; // 16 -> 28
  const nozzleBottomWidth = 30 + morphProgress * 10; // 30 -> 40
  const nozzleHeight = 25 + morphProgress * 5; // 25 -> 30

  const cx = moldWidth / 2;
  const nozzleTop = 8;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width: moldWidth,
        height: moldHeight,
        opacity: containerOpacity,
      }}
    >
      <svg width={moldWidth} height={moldHeight}>
        {/* Mold outline */}
        <rect
          x={4}
          y={4}
          width={moldWidth - 8}
          height={moldHeight - 8}
          fill="none"
          stroke={color}
          strokeWidth={2}
          rx={4}
          opacity={0.5}
        />
        {/* Nozzle / prompt region — morphing trapezoid */}
        <path
          d={`
            M ${cx - nozzleTopWidth / 2} ${nozzleTop}
            L ${cx + nozzleTopWidth / 2} ${nozzleTop}
            L ${cx + nozzleBottomWidth / 2} ${nozzleTop + nozzleHeight}
            L ${cx - nozzleBottomWidth / 2} ${nozzleTop + nozzleHeight}
            Z
          `}
          fill={color}
          opacity={0.3 + morphProgress * 0.15}
          stroke={color}
          strokeWidth={1.5}
        />
        {/* Cavity below nozzle */}
        <rect
          x={cx - 25}
          y={nozzleTop + nozzleHeight + 2}
          width={50}
          height={moldHeight - nozzleTop - nozzleHeight - 14}
          fill={color}
          opacity={0.12}
          rx={2}
        />
        {/* Morph glow */}
        {glowPulse > 0 && (
          <rect
            x={4}
            y={4}
            width={moldWidth - 8}
            height={moldHeight - 8}
            fill="none"
            stroke={color}
            strokeWidth={4}
            rx={4}
            opacity={glowPulse}
            filter="url(#reshapeGlow)"
          />
        )}
        <defs>
          <filter
            id="reshapeGlow"
            x="-50%"
            y="-50%"
            width="200%"
            height="200%"
          >
            <feGaussianBlur stdDeviation="6" />
          </filter>
        </defs>
      </svg>
      {/* Label */}
      <div
        style={{
          position: "absolute",
          bottom: -22,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 11,
          color,
          opacity: morphProgress * 0.7,
          letterSpacing: "0.5px",
        }}
      >
        reshape
      </div>
    </div>
  );
};
