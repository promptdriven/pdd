import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, MOLD, GENERATED_CODE, LiquidInjectionPropsType } from "./constants";

export const LiquidInjection: React.FC<LiquidInjectionPropsType> = ({
  showCode = true,
}) => {
  const frame = useCurrentFrame();

  // Mold fade in
  const moldOpacity = interpolate(
    frame,
    [BEATS.MOLD_START, BEATS.MOLD_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Fill progress (0 to 1)
  const fillProgress = interpolate(
    frame,
    [BEATS.INJECTION_START, BEATS.FILL_PROGRESS],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Wall contact glow
  const wallContactGlow = interpolate(
    frame,
    [BEATS.WALL_CONTACT_START, BEATS.WALL_CONTACT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Code appearance
  const codeOpacity = showCode
    ? interpolate(
        frame,
        [BEATS.CODE_START, BEATS.CODE_COMPLETE],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  // Checkmark
  const checkmarkOpacity = interpolate(
    frame,
    [BEATS.CHECKMARK_START, BEATS.CHECKMARK_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Calculate fill dimensions
  const interiorWidth = MOLD.width - 2 * MOLD.wallThickness - 20;
  const interiorHeight = MOLD.height - MOLD.wallThickness - 20;
  const fillHeight = interiorHeight * fillProgress;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <svg width="100%" height="100%" viewBox="0 0 1920 1080" style={{ opacity: moldOpacity }}>
        {/* Mold outline */}
        <rect
          x={MOLD.centerX - MOLD.width / 2}
          y={MOLD.centerY - MOLD.height / 2}
          width={MOLD.width}
          height={MOLD.height}
          fill="none"
          stroke={COLORS.OUTLINE_GRAY}
          strokeWidth={2}
          rx={8}
        />

        {/* Test walls (amber) */}
        <rect
          x={MOLD.centerX - MOLD.width / 2}
          y={MOLD.centerY - MOLD.height / 2}
          width={MOLD.wallThickness}
          height={MOLD.height}
          fill={`rgba(217, 148, 74, ${0.3 + 0.3 * wallContactGlow})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: wallContactGlow > 0 ? `drop-shadow(0 0 ${15 * wallContactGlow}px ${COLORS.WALLS_AMBER})` : "none",
          }}
        />
        <rect
          x={MOLD.centerX + MOLD.width / 2 - MOLD.wallThickness}
          y={MOLD.centerY - MOLD.height / 2}
          width={MOLD.wallThickness}
          height={MOLD.height}
          fill={`rgba(217, 148, 74, ${0.3 + 0.3 * wallContactGlow})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: wallContactGlow > 0 ? `drop-shadow(0 0 ${15 * wallContactGlow}px ${COLORS.WALLS_AMBER})` : "none",
          }}
        />
        <rect
          x={MOLD.centerX - MOLD.width / 2 + MOLD.wallThickness}
          y={MOLD.centerY + MOLD.height / 2 - MOLD.wallThickness}
          width={MOLD.width - 2 * MOLD.wallThickness}
          height={MOLD.wallThickness}
          fill={`rgba(217, 148, 74, ${0.3 + 0.3 * wallContactGlow})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: wallContactGlow > 0 ? `drop-shadow(0 0 ${15 * wallContactGlow}px ${COLORS.WALLS_AMBER})` : "none",
          }}
        />

        {/* Nozzle (blue) */}
        <rect
          x={MOLD.centerX - MOLD.nozzleWidth / 2}
          y={MOLD.centerY - MOLD.height / 2 - MOLD.nozzleHeight}
          width={MOLD.nozzleWidth}
          height={MOLD.nozzleHeight + 10}
          fill="rgba(74, 144, 217, 0.4)"
          stroke={COLORS.NOZZLE_BLUE}
          strokeWidth={2}
          rx={6}
          style={{
            filter: frame >= BEATS.INJECTION_START ? `drop-shadow(0 0 15px ${COLORS.NOZZLE_BLUE})` : "none",
          }}
        />

        {/* Liquid flow from nozzle */}
        {frame >= BEATS.INJECTION_START && fillProgress < 1 && (
          <rect
            x={MOLD.centerX - 10}
            y={MOLD.centerY - MOLD.height / 2}
            width={20}
            height={MOLD.height - MOLD.wallThickness - fillHeight}
            fill={COLORS.CODE_GRAY}
            opacity={0.6}
          />
        )}

        {/* Filling liquid (code material) */}
        {fillProgress > 0 && (
          <rect
            x={MOLD.centerX - MOLD.width / 2 + MOLD.wallThickness + 10}
            y={MOLD.centerY + MOLD.height / 2 - MOLD.wallThickness - fillHeight - 10}
            width={interiorWidth}
            height={fillHeight}
            fill={`rgba(138, 156, 175, ${0.4 + 0.3 * fillProgress})`}
            rx={4}
            style={{
              filter: `drop-shadow(0 0 ${10 * fillProgress}px ${COLORS.CODE_GRAY})`,
            }}
          />
        )}
      </svg>

      {/* Generated code panel */}
      {codeOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 140,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: codeOpacity,
          }}
        >
          <div
            style={{
              background: "#1E1E2E",
              padding: 20,
              borderRadius: 8,
              border: "1px solid #333",
              boxShadow: `0 0 ${20 * codeOpacity}px rgba(138, 156, 175, 0.3)`,
            }}
          >
            <pre
              style={{
                fontSize: 14,
                fontFamily: "JetBrains Mono, monospace",
                color: COLORS.CODE_GRAY,
                margin: 0,
                lineHeight: 1.5,
              }}
            >
              {GENERATED_CODE}
            </pre>
          </div>
        </div>
      )}

      {/* Checkmark */}
      {checkmarkOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: MOLD.centerY - 30,
            left: "50%",
            transform: "translateX(-50%)",
            fontSize: 48,
            color: COLORS.SUCCESS_GREEN,
            opacity: checkmarkOpacity,
            textShadow: `0 0 20px ${COLORS.SUCCESS_GREEN}`,
          }}
        >
          ✓
        </div>
      )}

      {/* Caption */}
      <div
        style={{
          position: "absolute",
          bottom: 40,
          left: 0,
          right: 0,
          textAlign: "center",
          fontSize: 18,
          color: COLORS.LABEL_WHITE,
          fontFamily: "sans-serif",
          opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
        }}
      >
        Code flows in through the prompt, shaped by the test walls.
      </div>
    </AbsoluteFill>
  );
};
