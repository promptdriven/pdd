import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface NeutralQuadrantsProps {
  gridLeft: number;
  gridTop: number;
  cellSize: number;
  fillColor: string;
  fillOpacity: number;
  fadeStart: number;
  fadeEnd: number;
}

export const NeutralQuadrants: React.FC<NeutralQuadrantsProps> = ({
  gridLeft,
  gridTop,
  cellSize,
  fillColor,
  fillOpacity,
  fadeStart,
  fadeEnd,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, fillOpacity], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <>
      {/* Top-right (greenfield × out-of-distribution — actually brownfield × in-distribution) */}
      <div
        style={{
          position: "absolute",
          left: gridLeft + cellSize,
          top: gridTop,
          width: cellSize,
          height: cellSize,
          backgroundColor: fillColor,
          opacity,
        }}
      />
      {/* Bottom-left */}
      <div
        style={{
          position: "absolute",
          left: gridLeft,
          top: gridTop + cellSize,
          width: cellSize,
          height: cellSize,
          backgroundColor: fillColor,
          opacity,
        }}
      />
    </>
  );
};

export default NeutralQuadrants;
