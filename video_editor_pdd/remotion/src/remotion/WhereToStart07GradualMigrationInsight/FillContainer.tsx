import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CONTAINER_WIDTH,
  CONTAINER_HEIGHT,
  CONTAINER_BORDER_RADIUS,
  CONTAINER_BORDER_WIDTH,
  FADE_IN_DURATION,
  FLOW_START_FRAME,
  FLOW_DURATION,
} from "./constants";

interface FillContainerProps {
  x: number;
  y: number;
  borderColor: string;
  fillColor: string;
  fillOpacity: number;
  startLevel: number;
  endLevel: number;
  label: string;
  labelColor: string;
  labelY: number;
  labelFontSize: number;
  labelFontWeight: number;
}

export const FillContainer: React.FC<FillContainerProps> = ({
  x,
  y,
  borderColor,
  fillColor,
  fillOpacity,
  startLevel,
  endLevel,
  label,
  labelColor,
  labelY,
  labelFontSize,
  labelFontWeight,
}) => {
  const frame = useCurrentFrame();

  // Fade in over first 20 frames
  const opacity = interpolate(frame, [0, FADE_IN_DURATION], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Fill level animates from startLevel to endLevel during flow phase
  const fillLevel = interpolate(
    frame,
    [FLOW_START_FRAME, FLOW_START_FRAME + FLOW_DURATION],
    [startLevel, endLevel],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Fill height grows from bottom
  const fillHeight = CONTAINER_HEIGHT * fillLevel;
  const fillY = CONTAINER_HEIGHT - fillHeight;

  // Center the container around x
  const containerLeft = x - CONTAINER_WIDTH / 2;

  return (
    <div style={{ opacity, position: "absolute", top: 0, left: 0, width: 0, height: 0 }}>
      {/* Label above container */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: labelY,
          transform: "translateX(-50%)",
          fontFamily: "Inter, sans-serif",
          fontSize: labelFontSize,
          fontWeight: labelFontWeight,
          color: labelColor,
          whiteSpace: "nowrap",
        }}
      >
        {label}
      </div>

      {/* Container with fill */}
      <div
        style={{
          position: "absolute",
          left: containerLeft,
          top: y,
          width: CONTAINER_WIDTH,
          height: CONTAINER_HEIGHT,
          borderRadius: CONTAINER_BORDER_RADIUS,
          border: `${CONTAINER_BORDER_WIDTH}px solid ${borderColor}`,
          overflow: "hidden",
          boxSizing: "border-box",
        }}
      >
        {/* Fill rectangle */}
        <div
          style={{
            position: "absolute",
            left: 0,
            top: fillY,
            width: "100%",
            height: fillHeight,
            backgroundColor: fillColor,
            opacity: fillOpacity,
          }}
        />
      </div>
    </div>
  );
};
