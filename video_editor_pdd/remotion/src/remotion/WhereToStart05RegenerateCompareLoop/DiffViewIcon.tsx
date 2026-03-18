import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

export const DiffViewIcon: React.FC<{
  startFrame: number;
}> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  const scale = localFrame < 0
    ? 0
    : interpolate(localFrame, [0, 12], [0, 1], {
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      });

  const opacity = localFrame < 0
    ? 0
    : interpolate(localFrame, [0, 8], [0, 1], {
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      });

  // Checkmark pop with overshoot (easeOut back approximation)
  const checkDelay = 8;
  const cf = localFrame - checkDelay;
  const checkScale = cf < 0
    ? 0
    : interpolate(cf, [0, 4, 8], [0, 1.2, 1], {
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      });
  const checkOpacity = cf < 0
    ? 0
    : interpolate(cf, [0, 4], [0, 0.5], {
        extrapolateRight: "clamp",
      });

  return (
    <div
      style={{
        width: 60,
        height: 65,
        transform: `scale(${scale})`,
        opacity,
        position: "relative",
      }}
    >
      <svg width={60} height={65} viewBox="0 0 60 65">
        {/* Diff view container */}
        <rect
          x={0}
          y={5}
          width={60}
          height={45}
          rx={3}
          fill="#0F172A"
          stroke="#334155"
          strokeWidth={1}
        />
        {/* Divider */}
        <line
          x1={30}
          y1={5}
          x2={30}
          y2={50}
          stroke="#334155"
          strokeWidth={1}
        />

        {/* Left side — original (gray lines) */}
        {[0, 1, 2, 3].map((i) => (
          <rect
            key={`l${i}`}
            x={4}
            y={14 + i * 8}
            width={20 - (i === 2 ? 6 : 0)}
            height={2}
            rx={1}
            fill="#64748B"
            fillOpacity={0.35}
          />
        ))}

        {/* Right side — regenerated (blue lines) */}
        {[0, 1, 2, 3].map((i) => (
          <rect
            key={`r${i}`}
            x={34}
            y={14 + i * 8}
            width={20 - (i === 3 ? 8 : 0)}
            height={2}
            rx={1}
            fill="#4A90D9"
            fillOpacity={0.35}
          />
        ))}

        {/* Left checkmark */}
        <g
          transform={`translate(15, 52) scale(${checkScale})`}
          opacity={checkOpacity}
        >
          <path
            d="M-5 0 L-2 3 L5 -4"
            stroke="#5AAA6E"
            strokeWidth={2.5}
            fill="none"
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </g>

        {/* Right checkmark */}
        <g
          transform={`translate(45, 52) scale(${checkScale})`}
          opacity={checkOpacity}
        >
          <path
            d="M-5 0 L-2 3 L5 -4"
            stroke="#5AAA6E"
            strokeWidth={2.5}
            fill="none"
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </g>
      </svg>
    </div>
  );
};
