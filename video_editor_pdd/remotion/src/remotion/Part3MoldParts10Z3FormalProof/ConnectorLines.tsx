import React from "react";
import { interpolate } from "remotion";

const PURPLE_ACCENT = "#A78BFA";

interface ConnectorTarget {
  /** X center of the proven wall */
  wallX: number;
  /** Y center of the proven wall */
  wallY: number;
}

interface ConnectorLinesProps {
  /** 0..1 progress for drawing connectors */
  drawProgress: number;
  /** Origin X (left edge of annotation panel) */
  originX: number;
  /** Origin Y (vertical center of panel) */
  originY: number;
  /** Target wall midpoints */
  targets: ConnectorTarget[];
}

const ConnectorLines: React.FC<ConnectorLinesProps> = ({
  drawProgress,
  originX,
  originY,
  targets,
}) => {
  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        <filter id="connectorGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feFlood floodColor={PURPLE_ACCENT} floodOpacity="0.3" result="color" />
          <feComposite in="color" in2="blur" operator="in" result="glow" />
          <feMerge>
            <feMergeNode in="glow" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {targets.map((target, i) => {
        // Stagger each connector slightly
        const staggerDelay = i * 0.15;
        const localProgress = interpolate(
          drawProgress,
          [staggerDelay, Math.min(staggerDelay + 0.7, 1)],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        );

        // Calculate a curved path from origin to wall
        const startX = originX;
        const startY = originY + i * 60 - 30;
        const endX = target.wallX;
        const endY = target.wallY;

        // Control points for a nice curve
        const cpX = (startX + endX) / 2;
        const cpY1 = startY;
        const cpY2 = endY;

        // Build the path
        const path = `M ${startX} ${startY} C ${cpX} ${cpY1}, ${cpX} ${cpY2}, ${endX} ${endY}`;

        // Approximate path length for dasharray animation
        const dx = endX - startX;
        const dy = endY - startY;
        const approxLen = Math.sqrt(dx * dx + dy * dy) * 1.3;

        const dashOffset = interpolate(localProgress, [0, 1], [approxLen, 0], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        });

        // Small circle at endpoint
        const circleOpacity = interpolate(localProgress, [0.6, 1], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        });

        return (
          <g key={i}>
            <path
              d={path}
              fill="none"
              stroke={PURPLE_ACCENT}
              strokeWidth={2}
              strokeDasharray={`6 4`}
              strokeDashoffset={dashOffset}
              opacity={0.4 * localProgress}
              filter="url(#connectorGlow)"
            />
            {/* Endpoint dot */}
            <circle
              cx={endX}
              cy={endY}
              r={5}
              fill={PURPLE_ACCENT}
              opacity={circleOpacity * 0.6}
            />
          </g>
        );
      })}
    </svg>
  );
};

export default ConnectorLines;
