import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BACKGROUND_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  ARROW_COLOR,
  ARROW_OPACITY,
  MOLD_GLOW_START,
  MOLD_GLOW_END,
} from "./constants";
import { MoldCrossSection } from "./MoldCrossSection";
import { CodeBlock } from "./CodeBlock";

export const defaultPart3MoldParts18CodeOutputFinaleProps = {};

/**
 * Section 3.18 — Code Is Output: The Mold Continues to Glow
 *
 * 90 frames @ 30fps (3s).
 * A code block materializes below the mold, glows briefly,
 * then dims. Meanwhile the mold's glow intensifies.
 * The mold is permanent; the code is disposable.
 */
export const Part3MoldParts18CodeOutputFinale: React.FC = () => {
  const frame = useCurrentFrame();

  // Arrow fades in with the code block
  const arrowOpacity = interpolate(frame, [0, 15], [0, ARROW_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Arrow head size
  const arrowHeadSize = 8;

  // Mold scale pulse: subtle scale-up as glow intensifies
  const moldScale = interpolate(
    frame,
    [MOLD_GLOW_START, MOLD_GLOW_END],
    [0.7, 0.72],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* ── Mold Cross Section (upper region, centered) ── */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 150,
          transform: `translateX(-50%) scale(${moldScale})`,
          transformOrigin: "center top",
          width: 800,
          height: 350,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        <MoldCrossSection />
      </div>

      {/* ── Hierarchy Arrow (mold → code) ── */}
      <svg
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: CANVAS_WIDTH,
          height: CANVAS_HEIGHT,
          pointerEvents: "none",
        }}
      >
        <defs>
          <marker
            id="arrowHead"
            markerWidth={arrowHeadSize}
            markerHeight={arrowHeadSize}
            refX={arrowHeadSize / 2}
            refY={arrowHeadSize / 2}
            orient="auto"
          >
            <polygon
              points={`0,0 ${arrowHeadSize},${arrowHeadSize / 2} 0,${arrowHeadSize}`}
              fill={ARROW_COLOR}
              opacity={1}
            />
          </marker>
        </defs>
        <line
          x1={960}
          y1={530}
          x2={960}
          y2={640}
          stroke={ARROW_COLOR}
          strokeWidth={1.5}
          opacity={arrowOpacity}
          markerEnd="url(#arrowHead)"
        />
      </svg>

      {/* ── Code Output Block (lower region) ── */}
      <CodeBlock />
    </AbsoluteFill>
  );
};

export default Part3MoldParts18CodeOutputFinale;
