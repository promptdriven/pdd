import React from "react";
import { INITIAL_SOCK, STITCH_COLOR } from "./constants";

/**
 * The single darned sock visible before zoom-out begins.
 * Represents the "one careful mend" from the previous shot.
 */
export const InitialSock: React.FC = () => {
  const { width, height, color, darnColor } = INITIAL_SOCK;
  const centerX = (958 - width) / 2;
  const centerY = (1080 - height) / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX,
        top: centerY,
        width,
        height,
      }}
    >
      {/* Sock shape */}
      <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`}>
        {/* Sock body */}
        <path
          d={`
            M ${width * 0.2} 0
            L ${width * 0.8} 0
            L ${width * 0.8} ${height * 0.55}
            Q ${width * 0.8} ${height * 0.75} ${width} ${height * 0.85}
            Q ${width} ${height} ${width * 0.7} ${height}
            L ${width * 0.2} ${height * 0.85}
            Q 0 ${height * 0.75} ${width * 0.2} ${height * 0.55}
            Z
          `}
          fill={color}
          stroke="#6B5B4F"
          strokeWidth={1.5}
        />

        {/* Darning patch area */}
        <ellipse
          cx={width * 0.5}
          cy={height * 0.4}
          rx={width * 0.22}
          ry={height * 0.15}
          fill={darnColor}
          opacity={0.25}
        />

        {/* Crosshatch darning stitches */}
        {Array.from({ length: 8 }, (_, i) => {
          const x1 = width * 0.32 + i * (width * 0.045);
          return (
            <line
              key={`dv${i}`}
              x1={x1}
              y1={height * 0.28}
              x2={x1 + 2}
              y2={height * 0.52}
              stroke={STITCH_COLOR}
              strokeWidth={1}
              opacity={0.6}
            />
          );
        })}
        {Array.from({ length: 6 }, (_, i) => {
          const y1 = height * 0.3 + i * (height * 0.04);
          return (
            <line
              key={`dh${i}`}
              x1={width * 0.3}
              y1={y1}
              x2={width * 0.7}
              y2={y1 + 1}
              stroke={STITCH_COLOR}
              strokeWidth={1}
              opacity={0.5}
            />
          );
        })}
      </svg>
    </div>
  );
};
