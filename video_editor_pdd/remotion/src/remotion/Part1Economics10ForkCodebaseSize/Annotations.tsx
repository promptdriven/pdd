import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  LARGE_CODEBASE_COLOR,
  CONTEXT_LABEL_COLOR,
  CONTEXT_LABEL_APPEAR,
  METR_ANNOTATION_START,
  BELIEF_ANNOTATION_START,
  FORK_POINT,
  mapX,
  mapY,
} from "./constants";

export const Annotations: React.FC = () => {
  const frame = useCurrentFrame();

  // "Same tools. Different codebase sizes." — appears at fork point
  const contextOpacity = interpolate(
    frame,
    [CONTEXT_LABEL_APPEAR, CONTEXT_LABEL_APPEAR + 20],
    [0, 0.85],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // METR annotation
  const metrOpacity = interpolate(
    frame,
    [METR_ANNOTATION_START, METR_ANNOTATION_START + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const metrSlideY = interpolate(
    frame,
    [METR_ANNOTATION_START, METR_ANNOTATION_START + 20],
    [8, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // "Developers believed AI saved 20%..." annotation
  const beliefOpacity = interpolate(
    frame,
    [BELIEF_ANNOTATION_START, BELIEF_ANNOTATION_START + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const beliefSlideY = interpolate(
    frame,
    [BELIEF_ANNOTATION_START, BELIEF_ANNOTATION_START + 20],
    [8, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Position annotations near the upper fork (large codebase)
  const annotationX = mapX(2022.5);
  const annotationY = mapY(0.46) - 60;

  return (
    <>
      {/* Context label near fork point */}
      {frame >= CONTEXT_LABEL_APPEAR && (
        <div
          style={{
            position: "absolute",
            left: mapX(FORK_POINT.x) - 130,
            top: mapY(FORK_POINT.y) + 30,
            opacity: contextOpacity,
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 400,
            color: CONTEXT_LABEL_COLOR,
            whiteSpace: "nowrap",
          }}
        >
          Same tools. Different codebase sizes.
        </div>
      )}

      {/* METR annotation */}
      {frame >= METR_ANNOTATION_START && (
        <div
          style={{
            position: "absolute",
            left: annotationX,
            top: annotationY + metrSlideY,
            opacity: metrOpacity,
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 400,
            color: LARGE_CODEBASE_COLOR,
            whiteSpace: "nowrap",
            lineHeight: 1.4,
          }}
        >
          METR, 2025: experienced devs 19% slower on mature repos
        </div>
      )}

      {/* Devastating belief annotation */}
      {frame >= BELIEF_ANNOTATION_START && (
        <div
          style={{
            position: "absolute",
            left: annotationX,
            top: annotationY + 26 + beliefSlideY,
            opacity: beliefOpacity,
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 400,
            fontStyle: "italic",
            color: LARGE_CODEBASE_COLOR,
            whiteSpace: "nowrap",
            lineHeight: 1.4,
          }}
        >
          Developers believed AI saved 20%. It cost 19%.
        </div>
      )}

      {/* Callout line from METR annotation to large codebase line */}
      {frame >= METR_ANNOTATION_START && (
        <svg
          width={1920}
          height={1080}
          style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
        >
          <line
            x1={annotationX - 8}
            y1={annotationY + 10}
            x2={mapX(2024)}
            y2={mapY(0.46)}
            stroke={LARGE_CODEBASE_COLOR}
            strokeWidth={1}
            strokeDasharray="3 3"
            opacity={metrOpacity * 0.5}
          />
        </svg>
      )}
    </>
  );
};

export default Annotations;
