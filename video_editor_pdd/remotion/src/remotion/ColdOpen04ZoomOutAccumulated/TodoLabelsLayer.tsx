import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { TODO_LABELS, TODO_LABEL_COLOR, LAYER3_START } from "./constants";

const TodoLabelsLayer: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {TODO_LABELS.map((label, i) => {
        const startFrame = LAYER3_START + i * 5;
        const opacity = interpolate(
          frame,
          [startFrame, startFrame + 10],
          [0, 0.5],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        );

        const translateY = interpolate(
          frame,
          [startFrame, startFrame + 10],
          [8, 0],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        );

        return (
          <div
            key={i}
            style={{
              position: "absolute",
              left: label.x,
              top: label.y,
              opacity,
              transform: `rotate(${label.rotation}deg) translateY(${translateY}px)`,
              fontFamily: "Inter, sans-serif",
              fontSize: 10,
              color: TODO_LABEL_COLOR,
              whiteSpace: "nowrap",
              pointerEvents: "none",
              backgroundColor: "rgba(231, 76, 60, 0.08)",
              padding: "2px 6px",
              borderRadius: 3,
              border: `1px solid rgba(231, 76, 60, 0.15)`,
            }}
          >
            {label.text}
          </div>
        );
      })}
    </>
  );
};

export default TodoLabelsLayer;
