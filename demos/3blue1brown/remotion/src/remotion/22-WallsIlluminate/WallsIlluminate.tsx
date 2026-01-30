import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, TEST_LABELS, WallsIlluminatePropsType } from "./constants";

export const WallsIlluminate: React.FC<WallsIlluminatePropsType> = ({
  showLabels = true,
}) => {
  const frame = useCurrentFrame();

  // Mold visibility
  const moldOpacity = interpolate(
    frame,
    [BEATS.MOLD_VISIBLE_START, BEATS.MOLD_VISIBLE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Walls glow intensity
  const wallsGlow = interpolate(
    frame,
    [BEATS.WALLS_GLOW_START, BEATS.WALLS_GLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Mold dimensions
  const moldConfig = {
    centerX: 960,
    centerY: 540,
    width: 700,
    height: 500,
    wallThickness: 60,
  };

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <svg width="100%" height="100%" viewBox="0 0 1920 1080" style={{ opacity: moldOpacity }}>
        {/* Mold outline */}
        <rect
          x={moldConfig.centerX - moldConfig.width / 2}
          y={moldConfig.centerY - moldConfig.height / 2}
          width={moldConfig.width}
          height={moldConfig.height}
          fill="none"
          stroke={COLORS.OUTLINE_GRAY}
          strokeWidth={2}
          rx={8}
        />

        {/* Left wall with glow */}
        <rect
          x={moldConfig.centerX - moldConfig.width / 2}
          y={moldConfig.centerY - moldConfig.height / 2}
          width={moldConfig.wallThickness}
          height={moldConfig.height}
          fill={`rgba(217, 148, 74, ${0.2 + 0.5 * wallsGlow})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: `drop-shadow(0 0 ${30 * wallsGlow}px ${COLORS.WALLS_AMBER})`,
          }}
        />

        {/* Right wall with glow */}
        <rect
          x={moldConfig.centerX + moldConfig.width / 2 - moldConfig.wallThickness}
          y={moldConfig.centerY - moldConfig.height / 2}
          width={moldConfig.wallThickness}
          height={moldConfig.height}
          fill={`rgba(217, 148, 74, ${0.2 + 0.5 * wallsGlow})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: `drop-shadow(0 0 ${30 * wallsGlow}px ${COLORS.WALLS_AMBER})`,
          }}
        />

        {/* Bottom wall with glow */}
        <rect
          x={moldConfig.centerX - moldConfig.width / 2 + moldConfig.wallThickness}
          y={moldConfig.centerY + moldConfig.height / 2 - moldConfig.wallThickness}
          width={moldConfig.width - 2 * moldConfig.wallThickness}
          height={moldConfig.wallThickness}
          fill={`rgba(217, 148, 74, ${0.2 + 0.5 * wallsGlow})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: `drop-shadow(0 0 ${30 * wallsGlow}px ${COLORS.WALLS_AMBER})`,
          }}
        />
      </svg>

      {/* Test labels on walls */}
      {showLabels && (
        <div style={{ opacity: moldOpacity }}>
          {/* Left wall labels */}
          {TEST_LABELS.slice(0, 3).map((label, i) => {
            const labelOpacity = interpolate(
              frame,
              [BEATS.LABELS_START + i * BEATS.LABELS_STAGGER, BEATS.LABELS_START + i * BEATS.LABELS_STAGGER + 20],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            );
            return (
              <div
                key={`left-${i}`}
                style={{
                  position: "absolute",
                  left: moldConfig.centerX - moldConfig.width / 2 + 10,
                  top: moldConfig.centerY - moldConfig.height / 2 + 60 + i * 80,
                  fontSize: 14,
                  fontFamily: "JetBrains Mono, monospace",
                  color: COLORS.WALLS_AMBER,
                  opacity: labelOpacity,
                  textShadow: `0 0 10px ${COLORS.WALLS_AMBER}`,
                }}
              >
                {label}
              </div>
            );
          })}

          {/* Right wall labels */}
          {TEST_LABELS.slice(3).map((label, i) => {
            const labelOpacity = interpolate(
              frame,
              [BEATS.LABELS_START + (i + 3) * BEATS.LABELS_STAGGER, BEATS.LABELS_START + (i + 3) * BEATS.LABELS_STAGGER + 20],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            );
            return (
              <div
                key={`right-${i}`}
                style={{
                  position: "absolute",
                  right: 960 - moldConfig.width / 2 + 70,
                  top: moldConfig.centerY - moldConfig.height / 2 + 60 + i * 80,
                  fontSize: 14,
                  fontFamily: "JetBrains Mono, monospace",
                  color: COLORS.WALLS_AMBER,
                  opacity: labelOpacity,
                  textShadow: `0 0 10px ${COLORS.WALLS_AMBER}`,
                }}
              >
                {label}
              </div>
            );
          })}
        </div>
      )}

      {/* Section title */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: moldOpacity,
        }}
      >
        <span
          style={{
            fontSize: 24,
            fontFamily: "sans-serif",
            color: COLORS.WALLS_AMBER,
            fontWeight: "bold",
          }}
        >
          First: tests
        </span>
        <div
          style={{
            fontSize: 16,
            color: COLORS.LABEL_GRAY,
            marginTop: 8,
          }}
        >
          The Constraints
        </div>
      </div>

      {/* Caption */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          fontSize: 20,
          color: COLORS.LABEL_WHITE,
          fontFamily: "sans-serif",
          opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
        }}
      >
        Tests define the boundaries. Code must fit within them.
      </div>
    </AbsoluteFill>
  );
};
