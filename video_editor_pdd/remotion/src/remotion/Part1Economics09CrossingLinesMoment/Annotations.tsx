import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  SLATE_ANNOTATION,
  RED_LARGE,
  BLUE_GENERATE,
  xToPixel,
  yToPixel,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
  PHASE_ANNOTATION,
  PHASE_METR,
  PHASE_PROMPT_NOTE,
} from "./constants";

/**
 * Text annotations:
 * 1. "Same tools. Different codebase sizes." — between forks
 * 2. METR annotations — near upper fork
 * 3. Terminal breadcrumb — bottom-right
 */
export const Annotations: React.FC = () => {
  const frame = useCurrentFrame();

  // "Same tools" annotation
  const sameToolsOpacity = interpolate(
    frame,
    [PHASE_ANNOTATION.start, PHASE_ANNOTATION.start + 15],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // METR annotation
  const metrOpacity1 = interpolate(
    frame,
    [PHASE_METR.start, PHASE_METR.start + 15],
    [0, 0.45],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const metrOpacity2 = interpolate(
    frame,
    [PHASE_METR.start + 30, PHASE_METR.start + 45],
    [0, 0.35],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Terminal breadcrumb
  const terminalOpacity = interpolate(
    frame,
    [PHASE_PROMPT_NOTE.start, PHASE_PROMPT_NOTE.start + 15],
    [0, 0.12],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Position: between forks, around 2022-2023 area
  const midYear = 2022.5;
  const lowerY2022 = 4; // approx small codebase at 2022
  const upperY2022 = 10; // approx large codebase at 2022
  const annoX = xToPixel(midYear);
  const annoY = yToPixel((lowerY2022 + upperY2022) / 2);

  // METR position — near upper fork end
  const upperEnd = LARGE_CODEBASE_DATA[LARGE_CODEBASE_DATA.length - 1];
  const metrX = xToPixel(upperEnd.x) - 180;
  const metrY = yToPixel(upperEnd.y) - 40;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* "Same tools" annotation */}
      {frame >= PHASE_ANNOTATION.start && (
        <g opacity={sameToolsOpacity}>
          <text
            x={annoX}
            y={annoY}
            fill={SLATE_ANNOTATION}
            fontSize={12}
            fontFamily="Inter, sans-serif"
            textAnchor="middle"
          >
            Same tools. Different codebase sizes.
          </text>

          {/* Thin dashed lines pointing to both forks */}
          <line
            x1={annoX}
            y1={annoY + 6}
            x2={annoX}
            y2={yToPixel(lowerY2022) - 6}
            stroke={SLATE_ANNOTATION}
            strokeWidth={1}
            strokeDasharray="3 3"
            opacity={0.15}
          />
          <line
            x1={annoX}
            y1={annoY - 14}
            x2={annoX}
            y2={yToPixel(upperY2022) + 6}
            stroke={SLATE_ANNOTATION}
            strokeWidth={1}
            strokeDasharray="3 3"
            opacity={0.15}
          />
        </g>
      )}

      {/* METR annotations */}
      {frame >= PHASE_METR.start && (
        <g>
          <text
            x={metrX}
            y={metrY}
            fill={RED_LARGE}
            fontSize={9}
            fontFamily="Inter, sans-serif"
            opacity={metrOpacity1}
          >
            METR, 2025: experienced devs 19% slower
          </text>
          <text
            x={metrX}
            y={metrY + 16}
            fill={RED_LARGE}
            fontSize={9}
            fontFamily="Inter, sans-serif"
            opacity={metrOpacity2}
          >
            {"Developers believed +20%. Reality: \u221219%."}
          </text>
        </g>
      )}

      {/* Terminal breadcrumb */}
      {frame >= PHASE_PROMPT_NOTE.start && (
        <text
          x={1800}
          y={1040}
          fill={BLUE_GENERATE}
          fontSize={10}
          fontFamily="'JetBrains Mono', monospace"
          textAnchor="end"
          opacity={terminalOpacity}
        >
          pdd generate
        </text>
      )}
    </svg>
  );
};

export default Annotations;
