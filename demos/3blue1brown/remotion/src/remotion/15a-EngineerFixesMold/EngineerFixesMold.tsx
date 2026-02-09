import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, MOLD, TOOL, EngineerFixesMoldPropsType } from "./constants";

export const EngineerFixesMold: React.FC<EngineerFixesMoldPropsType> = ({
  showOverlay = true,
}) => {
  const frame = useCurrentFrame();

  // Mold visibility
  const moldOpacity = interpolate(
    frame,
    [BEATS.MOLD_APPEAR, BEATS.MOLD_VISIBLE],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Tool position
  const toolX = interpolate(
    frame,
    [BEATS.TOOL_APPROACH, BEATS.TOOL_CONTACT],
    [TOOL.START_X, TOOL.CONTACT_X],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  const toolY = interpolate(
    frame,
    [BEATS.TOOL_APPROACH, BEATS.TOOL_CONTACT],
    [TOOL.START_Y, TOOL.CONTACT_Y],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  // Tool visibility
  const toolOpacity = interpolate(
    frame,
    [BEATS.TOOL_APPROACH, BEATS.TOOL_APPROACH + 30],
    [0, 1],
    { extrapolateRight: "clamp" }
  );

  // Sparks during adjustment
  const sparksActive = frame >= BEATS.SPARKS_START && frame <= BEATS.SPARKS_END;
  const sparksIntensity = sparksActive
    ? interpolate(
        frame,
        [BEATS.SPARKS_START, BEATS.SPARKS_START + 30, BEATS.SPARKS_END - 30, BEATS.SPARKS_END],
        [0, 1, 1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  // Mold shape change at defect point
  const shapeChange = interpolate(
    frame,
    [BEATS.SHAPE_CHANGE, BEATS.SHAPE_COMPLETE],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // "Mold Updated" label
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_APPEAR, BEATS.LABEL_APPEAR + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Defect area glow during fix
  const defectGlow = frame >= BEATS.ADJUSTMENT_START && frame <= BEATS.ADJUSTMENT_END
    ? Math.sin((frame - BEATS.ADJUSTMENT_START) * 0.2) * 0.5 + 0.5
    : 0;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Section header */}
      {showOverlay && (
        <div
          style={{
            position: "absolute",
            top: 40,
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
              color: COLORS.LABEL_WHITE,
              fontWeight: "bold",
            }}
          >
            Engineer Fixes the Mold
          </span>
        </div>
      )}

      {/* Mold structure */}
      <div
        style={{
          position: "absolute",
          left: MOLD.X - MOLD.WIDTH / 2,
          top: MOLD.Y - MOLD.HEIGHT / 2,
          width: MOLD.WIDTH,
          height: MOLD.HEIGHT,
          opacity: moldOpacity,
        }}
      >
        {/* Main mold body */}
        <div
          style={{
            width: "100%",
            height: "100%",
            background: `linear-gradient(135deg, ${COLORS.MOLD_GRAY}, ${COLORS.MOLD_HIGHLIGHT})`,
            borderRadius: 8,
            border: `2px solid ${COLORS.MOLD_HIGHLIGHT}`,
            boxShadow: "0 8px 24px rgba(0, 0, 0, 0.4)",
            position: "relative",
          }}
        >
          {/* Mold cavity (inner shape) */}
          <div
            style={{
              position: "absolute",
              top: "25%",
              left: "20%",
              width: "60%",
              height: "50%",
              background: "rgba(0, 0, 0, 0.3)",
              borderRadius: 4,
              border: "1px solid rgba(255, 255, 255, 0.2)",
            }}
          />

          {/* Defect point indicator (before fix) */}
          {shapeChange < 0.5 && (
            <div
              style={{
                position: "absolute",
                left: MOLD.DEFECT_X - (MOLD.X - MOLD.WIDTH / 2),
                top: MOLD.DEFECT_Y - (MOLD.Y - MOLD.HEIGHT / 2),
                width: 20,
                height: 20,
                background: COLORS.FIX_POINT_AMBER,
                borderRadius: "50%",
                boxShadow: `0 0 ${20 * (1 + defectGlow)}px ${COLORS.FIX_POINT_AMBER}`,
                opacity: 0.6,
              }}
            />
          )}
        </div>
      </div>

      {/* Tool (file/polishing instrument) */}
      {toolOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: toolX - 30,
            top: toolY - 60,
            opacity: toolOpacity,
          }}
        >
          {/* Tool handle */}
          <div
            style={{
              width: 8,
              height: 80,
              background: `linear-gradient(to bottom, ${COLORS.TOOL_METAL}, #7a8795)`,
              borderRadius: 4,
              boxShadow: "0 2px 8px rgba(0, 0, 0, 0.3)",
            }}
          />
          {/* Tool tip */}
          <div
            style={{
              position: "absolute",
              bottom: -10,
              left: -4,
              width: 16,
              height: 16,
              background: COLORS.TOOL_METAL,
              clipPath: "polygon(50% 100%, 0 0, 100% 0)",
              boxShadow: "0 2px 4px rgba(0, 0, 0, 0.4)",
            }}
          />
        </div>
      )}

      {/* Sparks effect during adjustment */}
      {sparksIntensity > 0 && (
        <div
          style={{
            position: "absolute",
            left: TOOL.CONTACT_X,
            top: TOOL.CONTACT_Y,
            opacity: sparksIntensity,
          }}
        >
          {[...Array(6)].map((_, i) => {
            const angle = (i / 6) * Math.PI * 2;
            const distance = 20 + Math.random() * 20;
            const sparkX = Math.cos(angle) * distance;
            const sparkY = Math.sin(angle) * distance;
            const sparkSize = 3 + Math.random() * 4;
            const sparkColor = i % 2 === 0 ? COLORS.SPARK_YELLOW : COLORS.SPARK_ORANGE;

            return (
              <div
                key={i}
                style={{
                  position: "absolute",
                  left: sparkX,
                  top: sparkY,
                  width: sparkSize,
                  height: sparkSize,
                  background: sparkColor,
                  borderRadius: "50%",
                  boxShadow: `0 0 ${sparkSize * 2}px ${sparkColor}`,
                  opacity: Math.random() * 0.8 + 0.2,
                }}
              />
            );
          })}
        </div>
      )}

      {/* Shape change indicator (updated cavity) */}
      {shapeChange > 0 && (
        <div
          style={{
            position: "absolute",
            left: MOLD.DEFECT_X - 15,
            top: MOLD.DEFECT_Y - 15,
            width: 30,
            height: 30,
            border: `3px solid ${COLORS.FIX_POINT_AMBER}`,
            borderRadius: "50%",
            boxShadow: `0 0 ${20 * shapeChange}px ${COLORS.FIX_POINT_AMBER}`,
            opacity: shapeChange,
          }}
        />
      )}

      {/* "Mold Updated" label */}
      {labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: MOLD.DEFECT_X + 40,
            top: MOLD.DEFECT_Y - 20,
            opacity: labelOpacity,
          }}
        >
          <div
            style={{
              background: "rgba(217, 148, 74, 0.2)",
              border: `2px solid ${COLORS.FIX_POINT_AMBER}`,
              borderRadius: 8,
              padding: "8px 16px",
              fontSize: 18,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
              fontWeight: "bold",
              boxShadow: `0 0 12px rgba(217, 148, 74, 0.4)`,
            }}
          >
            Mold Updated
          </div>
        </div>
      )}

      {/* Narration hint (bottom) */}
      {showOverlay && labelOpacity > 0.5 && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: labelOpacity,
          }}
        >
          <div
            style={{
              fontSize: 20,
              color: COLORS.LABEL_GRAY,
              fontFamily: "sans-serif",
            }}
          >
            Fix the specification, not the output
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
