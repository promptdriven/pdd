import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { BEATS, COLORS, CHART_MARGINS, YEAR_RANGE, HOURS_RANGE } from "./constants";

interface DebtLayerSeparationProps {
  opacity?: number;
}

export const DebtLayerSeparation: React.FC<DebtLayerSeparationProps> = ({
  opacity = 1,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  // Position helpers
  const getXPosition = (year: number) => {
    return (
      CHART_MARGINS.left +
      ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth
    );
  };

  const getYPosition = (hours: number) => {
    return (
      CHART_MARGINS.top +
      chartHeight -
      (hours / HOURS_RANGE.max) * chartHeight
    );
  };

  // Layer separation animation progress
  const separationProgress = interpolate(
    frame,
    [BEATS.LAYER_SEPARATION_START, BEATS.LAYER_SEPARATION_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Zoom progress for the zoom-in effect
  const zoomProgress = interpolate(
    frame,
    [BEATS.ZOOM_INTO_DEBT_START, BEATS.ZOOM_INTO_DEBT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Background fade during zoom
  const backgroundOpacity = interpolate(
    frame,
    [BEATS.ZOOM_INTO_DEBT_START, BEATS.ZOOM_INTO_DEBT_END],
    [1, 0.2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // The debt region coordinates (the shaded area between Cost to Patch and Cost to Generate)
  const crossingYear = 2023.5;
  const debtStartX = getXPosition(crossingYear);
  const debtEndX = getXPosition(YEAR_RANGE.max);

  // Simplified debt region path (trapezoid-ish shape)
  const patchLineY = getYPosition(0.8); // Cost to patch stays relatively flat
  const generateStartY = getYPosition(0.8); // Starts at crossing point
  const generateEndY = getYPosition(0.05); // Drops to near zero

  // Layer separation offset (how far apart the layers move)
  const maxSeparation = 40;
  const separation = separationProgress * maxSeparation;

  // Build paths for the two layers
  const buildDebtPath = (yOffset: number) => {
    return `
      M ${debtStartX} ${generateStartY + yOffset}
      L ${debtEndX} ${generateEndY + yOffset}
      L ${debtEndX} ${patchLineY + yOffset}
      L ${debtStartX} ${generateStartY + yOffset}
      Z
    `;
  };

  // Noise pattern seed for context rot layer
  const noiseId = "contextRotNoise";

  // Label fade in after separation
  const labelOpacity = interpolate(
    frame,
    [BEATS.LAYER_SEPARATION_END, BEATS.LAYER_SEPARATION_END + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Calculate label positions
  const labelX = (debtStartX + debtEndX) / 2;
  const codeComplexityLabelY = (patchLineY + generateStartY) / 2 + separation / 2 + 10;
  const contextRotLabelY = (patchLineY + generateStartY) / 2 - separation / 2 - 10;

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        opacity: opacity,
        transform: `scale(${1 + zoomProgress * 0.3})`,
        transformOrigin: `${(debtStartX + debtEndX) / 2}px ${(patchLineY + generateEndY) / 2}px`,
      }}
    >
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          {/* Noise pattern for context rot layer */}
          <filter id={noiseId}>
            <feTurbulence
              type="fractalNoise"
              baseFrequency="0.9"
              numOctaves="4"
              seed={42}
              result="noise"
            />
            <feDisplacementMap
              in="SourceGraphic"
              in2="noise"
              scale={8 * separationProgress}
              xChannelSelector="R"
              yChannelSelector="G"
            />
          </filter>

          {/* Animated noise for context rot texture */}
          <filter id="animatedNoise">
            <feTurbulence
              type="fractalNoise"
              baseFrequency="0.05"
              numOctaves="3"
              seed={Math.floor(frame / 3)}
              result="noise"
            />
            <feColorMatrix
              type="matrix"
              values="0 0 0 0 0
                      0 0 0 0 0
                      0 0 0 0 0
                      0 0 0 0.15 0"
            />
            <feBlend in="SourceGraphic" mode="overlay" />
          </filter>

          {/* Glow effect for layers */}
          <filter id="layerGlow" x="-20%" y="-20%" width="140%" height="140%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="4" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Faded background grid lines */}
        <g opacity={backgroundOpacity}>
          {/* Vertical grid lines */}
          {[2016, 2018, 2020, 2022, 2024, 2026, 2028, 2030].map((year) => (
            <line
              key={`v-grid-${year}`}
              x1={getXPosition(year)}
              y1={CHART_MARGINS.top}
              x2={getXPosition(year)}
              y2={height - CHART_MARGINS.bottom}
              stroke={COLORS.GRID}
              strokeWidth={1}
              strokeDasharray="5,5"
              opacity={0.5}
            />
          ))}
        </g>

        {/* Bottom layer: Code Complexity */}
        <path
          d={buildDebtPath(separation)}
          fill={COLORS.CODE_COMPLEXITY}
          fillOpacity={0.4}
          filter="url(#layerGlow)"
        />
        <path
          d={buildDebtPath(separation)}
          fill="none"
          stroke={COLORS.CODE_COMPLEXITY}
          strokeWidth={2}
          strokeDasharray="8,4"
          opacity={0.6}
        />

        {/* Top layer: Context Rot with noise texture */}
        <g filter="url(#animatedNoise)">
          <path
            d={buildDebtPath(-separation)}
            fill={COLORS.CONTEXT_ROT}
            fillOpacity={0.5}
          />
        </g>
        <path
          d={buildDebtPath(-separation)}
          fill="none"
          stroke={COLORS.CONTEXT_ROT}
          strokeWidth={2}
          opacity={0.7}
        />
      </svg>

      {/* Labels for the layers */}
      {labelOpacity > 0 && (
        <>
          {/* Code Complexity label */}
          <div
            style={{
              position: "absolute",
              left: labelX,
              top: codeComplexityLabelY,
              transform: "translate(-50%, -50%)",
              opacity: labelOpacity,
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 22,
              fontWeight: 600,
              color: COLORS.CODE_COMPLEXITY,
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              whiteSpace: "nowrap",
              padding: "8px 16px",
              backgroundColor: "rgba(26, 26, 46, 0.85)",
              borderRadius: 6,
              border: `1px solid ${COLORS.CODE_COMPLEXITY}`,
            }}
          >
            Code Complexity
          </div>

          {/* Context Rot label */}
          <div
            style={{
              position: "absolute",
              left: labelX,
              top: contextRotLabelY,
              transform: "translate(-50%, -50%)",
              opacity: labelOpacity,
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 22,
              fontWeight: 600,
              color: COLORS.CONTEXT_ROT,
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              whiteSpace: "nowrap",
              padding: "8px 16px",
              backgroundColor: "rgba(26, 26, 46, 0.85)",
              borderRadius: 6,
              border: `1px solid ${COLORS.CONTEXT_ROT}`,
            }}
          >
            Context Rot
          </div>
        </>
      )}
    </div>
  );
};
