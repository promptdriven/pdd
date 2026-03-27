import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  LARGE_CODEBASE_COLOR,
  CONTEXT_LABEL_COLOR,
  FONT_FAMILY,
  PHASE_CONTEXT_LABEL_START,
  PHASE_METR_ANNOTATION_START,
  PHASE_PERCEPTION_ANNOTATION_START,
  FADE_DURATION,
} from "./constants";
import { xToPixel, yToPixel } from "./ChartAxes";

const Annotations: React.FC = () => {
  const frame = useCurrentFrame();

  // ── "Same tools. Different codebase sizes." context label ──
  const contextOpacity = interpolate(
    frame,
    [PHASE_CONTEXT_LABEL_START, PHASE_CONTEXT_LABEL_START + FADE_DURATION],
    [0, 0.85],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // ── METR annotation ───────────────────────────────────
  const metrOpacity = interpolate(
    frame,
    [PHASE_METR_ANNOTATION_START, PHASE_METR_ANNOTATION_START + FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // ── "Developers believed..." annotation ───────────────
  const perceptionOpacity = interpolate(
    frame,
    [PHASE_PERCEPTION_ANNOTATION_START, PHASE_PERCEPTION_ANNOTATION_START + FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Annotation positions — near the upper (large codebase) fork
  const annotationX = xToPixel(2023);
  const annotationBaseY = yToPixel(0.45) - 50;

  return (
    <div style={{ position: "absolute", inset: 0, pointerEvents: "none" }}>
      {/* ── Context label near fork point ──────────── */}
      {frame >= PHASE_CONTEXT_LABEL_START && (
        <div
          style={{
            position: "absolute",
            left: xToPixel(2020) - 80,
            top: yToPixel(0.48) + 30,
            opacity: contextOpacity,
            fontFamily: FONT_FAMILY,
            fontSize: 18,
            fontWeight: 400,
            color: CONTEXT_LABEL_COLOR,
            whiteSpace: "nowrap",
          }}
        >
          Same tools. Different codebase sizes.
        </div>
      )}

      {/* ── METR annotation callout ────────────────── */}
      {frame >= PHASE_METR_ANNOTATION_START && (
        <div
          style={{
            position: "absolute",
            left: annotationX,
            top: annotationBaseY,
            opacity: metrOpacity,
            maxWidth: 460,
          }}
        >
          {/* Callout line */}
          <svg
            width={460}
            height={60}
            style={{ position: "absolute", top: -10, left: -30 }}
          >
            <line
              x1={0}
              y1={50}
              x2={30}
              y2={30}
              stroke={LARGE_CODEBASE_COLOR}
              strokeWidth={1.5}
              opacity={0.5}
            />
          </svg>
          <div
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: 18,
              fontWeight: 500,
              color: LARGE_CODEBASE_COLOR,
              lineHeight: 1.4,
              textShadow: "0 1px 4px rgba(0,0,0,0.6)",
            }}
          >
            METR, 2025: experienced devs 19% slower on mature repos
          </div>
        </div>
      )}

      {/* ── Perception gap annotation ─────────────── */}
      {frame >= PHASE_PERCEPTION_ANNOTATION_START && (
        <div
          style={{
            position: "absolute",
            left: annotationX,
            top: annotationBaseY + 36,
            opacity: perceptionOpacity,
            maxWidth: 460,
          }}
        >
          <div
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: 18,
              fontWeight: 500,
              fontStyle: "italic",
              color: LARGE_CODEBASE_COLOR,
              lineHeight: 1.4,
              textShadow: "0 1px 4px rgba(0,0,0,0.6)",
            }}
          >
            Developers believed AI saved 20%. It cost 19%.
          </div>
        </div>
      )}
    </div>
  );
};

export default Annotations;
