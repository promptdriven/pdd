import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { DIFF_MARKERS, LAYER2_START } from "./constants";

const DiffMarkersLayer: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {DIFF_MARKERS.map((marker, i) => {
        const startFrame = LAYER2_START + 8 + i * 3;
        const opacity = interpolate(
          frame,
          [startFrame, startFrame + 10],
          [0, 0.7],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        );

        const scale = interpolate(
          frame,
          [startFrame, startFrame + 8],
          [0.3, 1],
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
              left: marker.x,
              top: marker.y,
              opacity,
              transform: `scale(${scale})`,
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 14,
              fontWeight: 700,
              color: marker.color,
              pointerEvents: "none",
            }}
          >
            {marker.symbol}
          </div>
        );
      })}
    </>
  );
};

export default DiffMarkersLayer;
