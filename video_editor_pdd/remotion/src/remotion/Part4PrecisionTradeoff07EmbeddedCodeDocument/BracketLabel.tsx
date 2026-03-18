import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { FONT_SANS } from "./constants";

interface BracketLabelProps {
  text: string;
  color: string;
  opacity: number;
  yTop: number;
  yBottom: number;
  x: number;
  appearFrame: number;
  drawDuration?: number;
  pulseStart?: number;
  pulseEnd?: number;
}

export const BracketLabel: React.FC<BracketLabelProps> = ({
  text,
  color,
  opacity,
  yTop,
  yBottom,
  x,
  appearFrame,
  drawDuration = 20,
  pulseStart,
  pulseEnd,
}) => {
  const frame = useCurrentFrame();

  const bracketHeight = yBottom - yTop;
  const midY = yTop + bracketHeight / 2;

  // Draw progress
  const drawProgress = interpolate(
    frame,
    [appearFrame, appearFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Text fade in
  const textOpacity = interpolate(
    frame,
    [appearFrame + drawDuration * 0.5, appearFrame + drawDuration],
    [0, opacity],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse animation
  let pulseOpacityMod = 1;
  if (pulseStart !== undefined && pulseEnd !== undefined) {
    const pulseCycle = interpolate(
      frame,
      [pulseStart, (pulseStart + pulseEnd) / 2, pulseEnd],
      [1, 1.3, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.sin),
      }
    );
    if (frame >= pulseStart && frame <= pulseEnd) {
      pulseOpacityMod = pulseCycle;
    }
  }

  if (drawProgress <= 0) return null;

  const bracketWidth = 8;
  const drawnHeight = bracketHeight * drawProgress;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: yTop,
        width: 200,
        height: bracketHeight,
        opacity: opacity * pulseOpacityMod,
      }}
    >
      {/* Bracket - top horizontal */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: bracketWidth * drawProgress,
          height: 1.5,
          backgroundColor: color,
        }}
      />
      {/* Bracket - vertical line */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: 1.5,
          height: drawnHeight,
          backgroundColor: color,
        }}
      />
      {/* Bracket - bottom horizontal */}
      {drawProgress > 0.8 && (
        <div
          style={{
            position: "absolute",
            left: 0,
            bottom: 0,
            width: bracketWidth * Math.min(1, (drawProgress - 0.8) / 0.2),
            height: 1.5,
            backgroundColor: color,
          }}
        />
      )}
      {/* Label text */}
      <div
        style={{
          position: "absolute",
          left: bracketWidth + 8,
          top: bracketHeight / 2 - 8,
          fontFamily: FONT_SANS,
          fontSize: 11,
          color: color,
          opacity: textOpacity / opacity, // normalize since parent already has opacity
          whiteSpace: "nowrap",
        }}
      >
        {text}
      </div>
    </div>
  );
};
