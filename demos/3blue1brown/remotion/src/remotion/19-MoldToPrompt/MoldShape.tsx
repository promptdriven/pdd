import React from "react";
import { useCurrentFrame, interpolate, Easing, interpolateColors } from "remotion";
import { BEATS, COLORS, MOLD_SHAPE } from "./constants";

/**
 * Renders the mold shape that morphs into the prompt document shape.
 * During setup (frame 0-90): metallic mold, wider/shorter aspect.
 * During morph (frame 90-240): interpolates to white document, taller/narrower.
 * After morph: static document shape.
 */
export const MoldShape: React.FC = () => {
  const frame = useCurrentFrame();

  // Morph progress: 0 at MORPH_START, 1 at MORPH_END
  const morphProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Interpolate shape dimensions
  const x = interpolate(morphProgress, [0, 1], [MOLD_SHAPE.initialX, MOLD_SHAPE.finalX]);
  const y = interpolate(morphProgress, [0, 1], [MOLD_SHAPE.initialY, MOLD_SHAPE.finalY]);
  const width = interpolate(morphProgress, [0, 1], [MOLD_SHAPE.initialWidth, MOLD_SHAPE.finalWidth]);
  const height = interpolate(morphProgress, [0, 1], [MOLD_SHAPE.initialHeight, MOLD_SHAPE.finalHeight]);
  const rx = interpolate(morphProgress, [0, 1], [MOLD_SHAPE.initialRx, MOLD_SHAPE.finalRx]);

  // Color transition: metallic gradient -> white (easeOutQuad)
  const colorProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const fillColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.MOLD_METALLIC_MID, COLORS.DOC_WHITE]
  );

  const strokeColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.MOLD_EDGE, COLORS.DOC_BORDER]
  );

  const strokeWidth = interpolate(colorProgress, [0, 1], [2, 1]);

  // Blue glow appears during labels phase (frame 240-360)
  const glowOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Shadow transition: dark metallic shadow -> softer doc shadow + blue glow
  const shadowBlur = interpolate(colorProgress, [0, 1], [4, 2]);
  const shadowOpacity = interpolate(colorProgress, [0, 1], [0.5, 0.2]);

  // Metallic gradient stops transition toward white
  const gradLightColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.MOLD_METALLIC_LIGHT, "#FFFFFF"]
  );
  const gradMidColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.MOLD_METALLIC_MID, "#FFFFFF"]
  );
  const gradDarkColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.MOLD_METALLIC_DARK, "#F8F8FA"]
  );

  // Cavity visibility fades out during morph
  const cavityOpacity = interpolate(
    morphProgress,
    [0, 0.4],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Document divider line (appears as morph completes)
  const dividerOpacity = interpolate(
    morphProgress,
    [0.7, 1],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <>
      <defs>
        <linearGradient id="moldToDocGrad" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={gradLightColor} />
          <stop offset="50%" stopColor={gradMidColor} />
          <stop offset="100%" stopColor={gradDarkColor} />
        </linearGradient>
        <filter id="moldShadow" x="-20%" y="-20%" width="140%" height="140%">
          <feDropShadow
            dx="2"
            dy="3"
            stdDeviation={shadowBlur}
            floodColor="#000"
            floodOpacity={shadowOpacity}
          />
        </filter>
        <filter id="promptGlow" x="-30%" y="-30%" width="160%" height="160%">
          <feGaussianBlur stdDeviation="10" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Blue glow layer (behind the document) */}
      {glowOpacity > 0 && (
        <rect
          x={x - 12}
          y={y - 12}
          width={width + 24}
          height={height + 24}
          rx={rx + 6}
          fill="none"
          stroke={COLORS.PROMPT_GLOW}
          strokeWidth={4}
          opacity={glowOpacity * 0.7}
          filter="url(#promptGlow)"
        />
      )}

      {/* Main mold/document shape */}
      <rect
        x={x}
        y={y}
        width={width}
        height={height}
        rx={rx}
        fill={colorProgress < 0.95 ? "url(#moldToDocGrad)" : fillColor}
        stroke={strokeColor}
        strokeWidth={strokeWidth}
        filter="url(#moldShadow)"
      />

      {/* Mold cavity detail (fades during morph) */}
      {cavityOpacity > 0 && (
        <rect
          x={MOLD_SHAPE.initialX + MOLD_SHAPE.initialWidth / 2 - 60 + morphProgress * (MOLD_SHAPE.finalX + MOLD_SHAPE.finalWidth / 2 - (MOLD_SHAPE.initialX + MOLD_SHAPE.initialWidth / 2))}
          y={MOLD_SHAPE.initialY + MOLD_SHAPE.initialHeight / 2 - 15 + morphProgress * 40}
          width={120}
          height={30}
          rx={4}
          fill={COLORS.MOLD_CAVITY}
          opacity={cavityOpacity}
        />
      )}

      {/* Document divider line (below title area) */}
      {dividerOpacity > 0 && (
        <line
          x1={x + 20}
          y1={y + 60}
          x2={x + width - 20}
          y2={y + 60}
          stroke={COLORS.DOC_BORDER}
          strokeWidth={1}
          opacity={dividerOpacity}
        />
      )}
    </>
  );
};
