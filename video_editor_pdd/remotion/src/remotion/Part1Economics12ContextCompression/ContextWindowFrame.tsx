import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";

/**
 * ContextWindowFrame — the fixed-size rectangle representing the context window.
 * Draws in from frame 0-60 with a border reveal animation.
 */

interface ContextWindowFrameProps {
  windowLeft: number;
  windowTop: number;
  windowWidth: number;
  windowHeight: number;
  borderColor: string;
  borderWidth: number;
  borderRadius: number;
  glowOpacity: number;
  glowBlur: number;
  drawStart: number;
  drawEnd: number;
}

export const ContextWindowFrame: React.FC<ContextWindowFrameProps> = ({
  windowLeft,
  windowTop,
  windowWidth,
  windowHeight,
  borderColor,
  borderWidth,
  borderRadius,
  glowOpacity,
  glowBlur,
  drawStart,
  drawEnd,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(frame, [drawStart, drawEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const opacity = interpolate(frame, [drawStart, drawStart + 15], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Perimeter of the rectangle for dash-offset animation
  const perimeter = 2 * (windowWidth + windowHeight);
  const dashOffset = perimeter * (1 - drawProgress);

  // Label fade
  const labelOpacity = interpolate(frame, [drawEnd - 10, drawEnd + 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill>
      {/* Glow behind the frame */}
      <div
        style={{
          position: "absolute",
          left: windowLeft - glowBlur,
          top: windowTop - glowBlur,
          width: windowWidth + glowBlur * 2,
          height: windowHeight + glowBlur * 2,
          borderRadius: borderRadius + glowBlur,
          boxShadow: `0 0 ${glowBlur * 2}px ${glowBlur}px ${borderColor}`,
          opacity: glowOpacity * drawProgress,
        }}
      />

      {/* SVG border with dash-offset reveal */}
      <svg
        style={{
          position: "absolute",
          left: windowLeft - borderWidth,
          top: windowTop - borderWidth,
          width: windowWidth + borderWidth * 2,
          height: windowHeight + borderWidth * 2,
          opacity,
          overflow: "visible",
        }}
      >
        <rect
          x={borderWidth}
          y={borderWidth}
          width={windowWidth}
          height={windowHeight}
          rx={borderRadius}
          ry={borderRadius}
          fill="none"
          stroke={borderColor}
          strokeWidth={borderWidth}
          strokeDasharray={perimeter}
          strokeDashoffset={dashOffset}
        />
      </svg>

      {/* "Context Window" label above */}
      <div
        style={{
          position: "absolute",
          left: windowLeft,
          top: windowTop - 38,
          width: windowWidth,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 600,
          color: borderColor,
          opacity: labelOpacity,
          letterSpacing: "0.05em",
          textTransform: "uppercase",
        }}
      >
        Context Window
      </div>
    </AbsoluteFill>
  );
};
