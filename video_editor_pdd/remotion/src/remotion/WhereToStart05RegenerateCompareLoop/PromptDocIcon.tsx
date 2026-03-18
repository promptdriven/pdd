import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

export const PromptDocIcon: React.FC<{
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

  return (
    <div
      style={{
        width: 50,
        height: 65,
        transform: `scale(${scale})`,
        opacity,
        position: "relative",
      }}
    >
      {/* Document body */}
      <svg width={50} height={65} viewBox="0 0 50 65">
        {/* Doc shape with folded corner */}
        <path
          d="M5 0 H38 L50 12 V60 Q50 65 45 65 H5 Q0 65 0 60 V5 Q0 0 5 0 Z"
          fill="#0F172A"
          stroke="#4A90D9"
          strokeWidth={1.5}
          strokeOpacity={0.4}
        />
        {/* Folded corner */}
        <path
          d="M38 0 L38 12 L50 12"
          fill="none"
          stroke="#4A90D9"
          strokeWidth={1}
          strokeOpacity={0.3}
        />
        {/* Text lines (natural language) */}
        {[0, 1, 2, 3].map((i) => (
          <rect
            key={i}
            x={8}
            y={22 + i * 9}
            width={28 - (i === 3 ? 10 : i === 1 ? 4 : 0)}
            height={2.5}
            rx={1.25}
            fill="#CBD5E1"
            fillOpacity={0.3}
          />
        ))}
      </svg>
    </div>
  );
};
