import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

export const WallIcons: React.FC<{
  startFrame: number;
}> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  return (
    <div
      style={{
        display: "flex",
        gap: 5,
        alignItems: "flex-end",
        height: 40,
        justifyContent: "center",
      }}
    >
      {[0, 1, 2].map((i) => {
        const delay = i * 4;
        const f = localFrame - delay;
        const scale = f < 0
          ? 0
          : interpolate(f, [0, 10], [0, 1], {
              extrapolateRight: "clamp",
              easing: Easing.out(Easing.cubic),
            });
        const opacity = f < 0
          ? 0
          : interpolate(f, [0, 6], [0, 0.5], {
              extrapolateRight: "clamp",
            });

        return (
          <div
            key={i}
            style={{
              width: 12,
              height: 36,
              backgroundColor: "#D9944A",
              opacity,
              transform: `scaleY(${scale})`,
              transformOrigin: "bottom",
              borderRadius: 2,
              border: "1px solid rgba(217, 148, 74, 0.3)",
            }}
          />
        );
      })}
    </div>
  );
};
