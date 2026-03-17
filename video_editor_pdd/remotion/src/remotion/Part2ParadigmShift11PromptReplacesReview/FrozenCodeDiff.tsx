import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CODE_DIFF_FADE_START,
  CODE_DIFF_FADE_END,
  DIFF_LINES,
  CODE_MUTED,
} from "./constants";

export const FrozenCodeDiff: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [CODE_DIFF_FADE_START, CODE_DIFF_FADE_END],
    [0, 0.15],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 20,
        top: 80,
        right: 20,
        bottom: 230,
        overflow: "hidden",
        opacity,
      }}
    >
      {DIFF_LINES.map((line, i) => {
        const isAdd = line.startsWith("+");
        const isDel = line.startsWith("-");
        let color = CODE_MUTED;
        if (isAdd) color = "#4ADE80";
        if (isDel) color = "#F87171";

        return (
          <div
            key={i}
            style={{
              fontFamily: "JetBrains Mono, monospace",
              fontSize: 10,
              lineHeight: "15px",
              color,
              whiteSpace: "pre",
              opacity: 0.8,
            }}
          >
            {line || "\u00A0"}
          </div>
        );
      })}
    </div>
  );
};
