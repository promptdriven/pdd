import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, MOLD, CrossSectionIntroPropsType } from "./constants";

export const CrossSectionIntro: React.FC<CrossSectionIntroPropsType> = ({
  showLabels = true,
}) => {
  const frame = useCurrentFrame();

  // Animation progress values
  const outlineOpacity = interpolate(
    frame,
    [BEATS.OUTLINE_START, BEATS.OUTLINE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const wallsGlow = interpolate(
    frame,
    [BEATS.WALLS_START, BEATS.WALLS_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const nozzleGlow = interpolate(
    frame,
    [BEATS.NOZZLE_START, BEATS.NOZZLE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const materialGlow = interpolate(
    frame,
    [BEATS.MATERIAL_START, BEATS.MATERIAL_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const labelsOpacity = showLabels
    ? interpolate(
        frame,
        [BEATS.LABELS_START, BEATS.LABELS_END],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <svg width="100%" height="100%" viewBox="0 0 1920 1080">
        {/* Outer mold outline */}
        <g opacity={outlineOpacity}>
          <rect
            x={MOLD.centerX - MOLD.outerWidth / 2}
            y={MOLD.centerY - MOLD.outerHeight / 2}
            width={MOLD.outerWidth}
            height={MOLD.outerHeight}
            fill="none"
            stroke={COLORS.OUTLINE_GRAY}
            strokeWidth={3}
            rx={12}
          />
        </g>

        {/* Test walls (amber) */}
        <g opacity={outlineOpacity}>
          {/* Left wall */}
          <rect
            x={MOLD.centerX - MOLD.outerWidth / 2}
            y={MOLD.centerY - MOLD.outerHeight / 2}
            width={MOLD.wallThickness}
            height={MOLD.outerHeight}
            fill={`rgba(217, 148, 74, ${0.3 + 0.4 * wallsGlow})`}
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
            style={{
              filter: wallsGlow > 0 ? `drop-shadow(0 0 ${20 * wallsGlow}px ${COLORS.WALLS_AMBER})` : "none",
            }}
          />
          {/* Right wall */}
          <rect
            x={MOLD.centerX + MOLD.outerWidth / 2 - MOLD.wallThickness}
            y={MOLD.centerY - MOLD.outerHeight / 2}
            width={MOLD.wallThickness}
            height={MOLD.outerHeight}
            fill={`rgba(217, 148, 74, ${0.3 + 0.4 * wallsGlow})`}
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
            style={{
              filter: wallsGlow > 0 ? `drop-shadow(0 0 ${20 * wallsGlow}px ${COLORS.WALLS_AMBER})` : "none",
            }}
          />
          {/* Bottom wall */}
          <rect
            x={MOLD.centerX - MOLD.outerWidth / 2 + MOLD.wallThickness}
            y={MOLD.centerY + MOLD.outerHeight / 2 - MOLD.wallThickness}
            width={MOLD.outerWidth - 2 * MOLD.wallThickness}
            height={MOLD.wallThickness}
            fill={`rgba(217, 148, 74, ${0.3 + 0.4 * wallsGlow})`}
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
            style={{
              filter: wallsGlow > 0 ? `drop-shadow(0 0 ${20 * wallsGlow}px ${COLORS.WALLS_AMBER})` : "none",
            }}
          />
        </g>

        {/* Nozzle (blue) */}
        <g opacity={outlineOpacity}>
          <rect
            x={MOLD.centerX - MOLD.nozzleWidth / 2}
            y={MOLD.centerY - MOLD.outerHeight / 2 - MOLD.nozzleHeight}
            width={MOLD.nozzleWidth}
            height={MOLD.nozzleHeight + 10}
            fill={`rgba(74, 144, 217, ${0.3 + 0.4 * nozzleGlow})`}
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth={2}
            rx={8}
            style={{
              filter: nozzleGlow > 0 ? `drop-shadow(0 0 ${20 * nozzleGlow}px ${COLORS.NOZZLE_BLUE})` : "none",
            }}
          />
        </g>

        {/* Interior/Material space (green) */}
        <g opacity={outlineOpacity}>
          <rect
            x={MOLD.centerX - MOLD.outerWidth / 2 + MOLD.wallThickness + 10}
            y={MOLD.centerY - MOLD.outerHeight / 2 + 10}
            width={MOLD.outerWidth - 2 * MOLD.wallThickness - 20}
            height={MOLD.outerHeight - MOLD.wallThickness - 20}
            fill={`rgba(90, 170, 110, ${0.1 + 0.2 * materialGlow})`}
            stroke={COLORS.MATERIAL_GREEN}
            strokeWidth={1}
            strokeDasharray="8 4"
            rx={4}
            style={{
              filter: materialGlow > 0 ? `drop-shadow(0 0 ${15 * materialGlow}px ${COLORS.MATERIAL_GREEN})` : "none",
            }}
          />
        </g>
      </svg>

      {/* Labels */}
      {labelsOpacity > 0 && (
        <div style={{ opacity: labelsOpacity }}>
          {/* Walls label */}
          <div
            style={{
              position: "absolute",
              left: MOLD.centerX - MOLD.outerWidth / 2 - 150,
              top: MOLD.centerY - 20,
              fontSize: 18,
              fontWeight: "bold",
              color: COLORS.WALLS_AMBER,
              fontFamily: "sans-serif",
            }}
          >
            TESTS
            <div style={{ fontSize: 14, color: COLORS.LABEL_GRAY, fontWeight: "normal" }}>
              (Constraints)
            </div>
          </div>

          {/* Nozzle label */}
          <div
            style={{
              position: "absolute",
              left: MOLD.centerX + MOLD.nozzleWidth / 2 + 20,
              top: MOLD.centerY - MOLD.outerHeight / 2 - MOLD.nozzleHeight / 2 - 10,
              fontSize: 18,
              fontWeight: "bold",
              color: COLORS.NOZZLE_BLUE,
              fontFamily: "sans-serif",
            }}
          >
            PROMPT
            <div style={{ fontSize: 14, color: COLORS.LABEL_GRAY, fontWeight: "normal" }}>
              (Intent)
            </div>
          </div>

          {/* Material label */}
          <div
            style={{
              position: "absolute",
              left: MOLD.centerX + MOLD.outerWidth / 2 + 20,
              top: MOLD.centerY - 20,
              fontSize: 18,
              fontWeight: "bold",
              color: COLORS.MATERIAL_GREEN,
              fontFamily: "sans-serif",
            }}
          >
            GROUNDING
            <div style={{ fontSize: 14, color: COLORS.LABEL_GRAY, fontWeight: "normal" }}>
              (Style)
            </div>
          </div>
        </div>
      )}

      {/* Title */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          fontSize: 28,
          color: COLORS.LABEL_WHITE,
          fontFamily: "sans-serif",
          opacity: outlineOpacity,
        }}
      >
        The Mold Has Three Parts
      </div>
    </AbsoluteFill>
  );
};
