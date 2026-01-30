import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { COLORS, BEATS, MOLD, PART_SHAPE } from "./constants";

/**
 * Renders the pulsing red highlight circle around the defective part
 * and the "DEFECT" label that fades in at frame 150.
 *
 * Appears during PAUSE_HIGHLIGHT phase (frames 120-180) and persists through zoom.
 */
export const DefectHighlight: React.FC = () => {
  const frame = useCurrentFrame();

  // Only show after pause begins
  if (frame < BEATS.PAUSE_HIGHLIGHT_START) return null;

  // Defective part resting position (must match MoldScene)
  const moldBottom = MOLD.centerY + MOLD.halfHeight;
  const defectCenterX = MOLD.centerX;
  const defectCenterY = moldBottom + 80;

  // Highlight circle fade-in
  const highlightOpacity = interpolate(
    frame,
    [BEATS.PAUSE_HIGHLIGHT_START, BEATS.PAUSE_HIGHLIGHT_START + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Pulsing effect: radius oscillates
  const pulsePhase = (frame - BEATS.PAUSE_HIGHLIGHT_START) * 0.12;
  const pulseScale = 1 + Math.sin(pulsePhase) * 0.12;
  const baseRadius = 55;
  const currentRadius = baseRadius * pulseScale;

  // Pulsing opacity for the ring
  const pulseOpacity = 0.6 + Math.sin(pulsePhase) * 0.25;

  // "DEFECT" label fade-in at frame 150
  const labelOpacity =
    frame >= BEATS.LABEL_APPEAR
      ? interpolate(frame, [BEATS.LABEL_APPEAR, BEATS.LABEL_APPEAR + 20], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        })
      : 0;

  // Label slight upward slide
  const labelSlide =
    frame >= BEATS.LABEL_APPEAR
      ? interpolate(frame, [BEATS.LABEL_APPEAR, BEATS.LABEL_APPEAR + 20], [12, 0], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        })
      : 12;

  return (
    <>
      {/* SVG pulsing circle */}
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          <filter id="defectGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="8" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Outer glow ring */}
        <circle
          cx={defectCenterX}
          cy={defectCenterY}
          r={currentRadius + 6}
          fill="none"
          stroke={COLORS.DEFECT_RED}
          strokeWidth={3}
          opacity={highlightOpacity * pulseOpacity * 0.4}
          filter="url(#defectGlow)"
        />

        {/* Main highlight ring */}
        <circle
          cx={defectCenterX}
          cy={defectCenterY}
          r={currentRadius}
          fill="none"
          stroke={COLORS.DEFECT_RED}
          strokeWidth={3}
          opacity={highlightOpacity * pulseOpacity}
          filter="url(#defectGlow)"
        />
      </svg>

      {/* "DEFECT" label */}
      {labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: defectCenterX - 80,
            top: defectCenterY + PART_SHAPE.height / 2 + 50 + labelSlide,
            width: 160,
            textAlign: "center",
            opacity: labelOpacity,
          }}
        >
          <div
            style={{
              display: "inline-block",
              padding: "6px 24px",
              backgroundColor: COLORS.DEFECT_RED_BG,
              borderRadius: 6,
              fontSize: 22,
              fontFamily: "sans-serif",
              fontWeight: 700,
              color: COLORS.LABEL_WHITE,
              letterSpacing: 3,
              textTransform: "uppercase" as const,
            }}
          >
            Defect
          </div>
        </div>
      )}
    </>
  );
};
