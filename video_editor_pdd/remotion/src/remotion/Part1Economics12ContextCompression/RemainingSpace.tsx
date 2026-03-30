import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";

/**
 * RemainingSpace — Green shaded area at the bottom of the context window
 * that appears after all prompt blocks fit, with "Room to spare" label.
 */

interface RemainingSpaceProps {
  windowLeft: number;
  windowTop: number;
  windowWidth: number;
  windowHeight: number;
  usedHeight: number;
  fillColor: string;
  appearFrame: number;
}

export const RemainingSpace: React.FC<RemainingSpaceProps> = ({
  windowLeft,
  windowTop,
  windowWidth,
  windowHeight,
  usedHeight,
  fillColor,
  appearFrame,
}) => {
  const frame = useCurrentFrame();

  const revealProgress = interpolate(
    frame,
    [appearFrame, appearFrame + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const remainingHeight = windowHeight - usedHeight - 20; // 20px padding
  const spaceTop = windowTop + usedHeight + 10;

  if (remainingHeight <= 0) return null;

  return (
    <AbsoluteFill style={{ opacity: revealProgress }}>
      {/* Green fill area */}
      <div
        style={{
          position: "absolute",
          left: windowLeft + 10,
          top: spaceTop,
          width: windowWidth - 20,
          height: remainingHeight * revealProgress,
          backgroundColor: fillColor,
          opacity: 0.05,
          borderRadius: 4,
        }}
      />

      {/* Dashed border for the space */}
      <svg
        style={{
          position: "absolute",
          left: windowLeft + 10,
          top: spaceTop,
          width: windowWidth - 20,
          height: remainingHeight * revealProgress,
          overflow: "visible",
        }}
      >
        <rect
          x={0.5}
          y={0.5}
          width={windowWidth - 21}
          height={Math.max(0, remainingHeight * revealProgress - 1)}
          rx={4}
          ry={4}
          fill="none"
          stroke={fillColor}
          strokeWidth={1}
          strokeDasharray="4 3"
          opacity={0.3}
        />
      </svg>

      {/* "Room to spare" label */}
      <div
        style={{
          position: "absolute",
          left: windowLeft,
          top: spaceTop + (remainingHeight * revealProgress) / 2 - 8,
          width: windowWidth,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          fontStyle: "italic",
          fontWeight: 400,
          color: fillColor,
          opacity: 0.5,
        }}
      >
        Room to spare
      </div>
    </AbsoluteFill>
  );
};
