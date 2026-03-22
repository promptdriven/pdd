import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import { ACCENT_BLUE, ACCENT_GREEN, ACCENT_PURPLE } from "./constants";

interface ConnectorLinesProps {
  revealFrame: number;
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  color: string;
}

export const ConnectorLine: React.FC<ConnectorLinesProps> = ({
  revealFrame,
  fromX,
  fromY,
  toX,
  toY,
  color,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [revealFrame, revealFrame + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  const opacity = interpolate(
    frame,
    [revealFrame, revealFrame + 15],
    [0, 0.7],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const dx = toX - fromX;
  const dy = toY - fromY;
  const length = Math.sqrt(dx * dx + dy * dy);
  const angle = Math.atan2(dy, dx) * (180 / Math.PI);

  return (
    <div
      style={{
        position: "absolute",
        left: fromX,
        top: fromY,
        width: length * progress,
        height: 2,
        backgroundColor: color,
        opacity,
        transform: `rotate(${angle}deg)`,
        transformOrigin: "0 50%",
        boxShadow: `0 0 8px ${color}50`,
        borderRadius: 1,
      }}
    />
  );
};

/** Draws animated connection lines between three layers */
export const ConnectorLinesGroup: React.FC<{
  zoomScale: number;
  panY: number;
}> = ({ zoomScale, panY }) => {
  const frame = useCurrentFrame();

  // Lines reveal as zoom progresses
  const line1Opacity = interpolate(frame, [55, 75], [0, 0.65], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const line2Opacity = interpolate(frame, [105, 125], [0, 0.65], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Small pulsating dots at connection points
  const dotPulse = interpolate(
    frame,
    [0, 15, 30],
    [0.6, 1, 0.6],
    { extrapolateRight: "extend" }
  );

  return (
    <>
      {/* Line from inner to mid */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          width: 2,
          height: 80,
          marginLeft: -1,
          marginTop: 150,
          backgroundColor: ACCENT_BLUE,
          opacity: line1Opacity,
          transformOrigin: "top center",
          boxShadow: `0 0 10px ${ACCENT_BLUE}40`,
        }}
      />
      {/* Dot at connection */}
      {line1Opacity > 0.1 && (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: "50%",
            width: 8,
            height: 8,
            marginLeft: -4,
            marginTop: 146,
            borderRadius: "50%",
            backgroundColor: ACCENT_BLUE,
            opacity: line1Opacity,
            transform: `scale(${dotPulse})`,
            boxShadow: `0 0 12px ${ACCENT_BLUE}80`,
          }}
        />
      )}

      {/* Line from mid to outer */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          width: 2,
          height: 80,
          marginLeft: -1,
          marginTop: 390,
          backgroundColor: ACCENT_GREEN,
          opacity: line2Opacity,
          transformOrigin: "top center",
          boxShadow: `0 0 10px ${ACCENT_GREEN}40`,
        }}
      />
      {line2Opacity > 0.1 && (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: "50%",
            width: 8,
            height: 8,
            marginLeft: -4,
            marginTop: 386,
            borderRadius: "50%",
            backgroundColor: ACCENT_GREEN,
            opacity: line2Opacity,
            transform: `scale(${dotPulse})`,
            boxShadow: `0 0 12px ${ACCENT_GREEN}80`,
          }}
        />
      )}
    </>
  );
};

export default ConnectorLine;
