import React from "react";
import { interpolate, spring, useCurrentFrame, useVideoConfig } from "remotion";
import { BEATS, COLORS, PULSE_CONFIG } from "./constants";

interface WeAreHereMarkerProps {
  x: number;
  y: number;
}

export const WeAreHereMarker: React.FC<WeAreHereMarkerProps> = ({ x, y }) => {
  const frame = useCurrentFrame();
  const { fps, width, height } = useVideoConfig();

  // Marker appears with radial burst starting at MARKER_APPEAR_START
  const markerFrame = Math.max(0, frame - BEATS.MARKER_APPEAR_START);
  const markerScale = spring({
    frame: markerFrame,
    fps,
    config: {
      damping: 12,
      stiffness: 120,
    },
  });

  // Initial burst effect when marker appears
  const burstOpacity = interpolate(
    frame,
    [BEATS.MARKER_APPEAR_START, BEATS.MARKER_APPEAR_START + 10, BEATS.MARKER_APPEAR_END],
    [0, 0.8, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const burstScale = interpolate(
    frame,
    [BEATS.MARKER_APPEAR_START, BEATS.MARKER_APPEAR_END],
    [0.5, 3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Concentric ring pulse helper - staggered rings for more dramatic effect
  const getRingPulse = (ringIndex: number, pulseStartFrame: number, pulseDuration: number) => {
    const ringStartFrame = pulseStartFrame + ringIndex * PULSE_CONFIG.RING_STAGGER;
    const ringEndFrame = ringStartFrame + pulseDuration;

    if (frame < ringStartFrame || frame > ringEndFrame + 20) {
      return { opacity: 0, scale: 0 };
    }

    const opacity = interpolate(
      frame,
      [ringStartFrame, ringStartFrame + 10, ringEndFrame],
      [0, 0.7 - ringIndex * 0.1, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );

    const scale = interpolate(
      frame,
      [ringStartFrame, ringEndFrame],
      [1, PULSE_CONFIG.MAX_SCALE],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );

    return { opacity, scale };
  };

  // First strong pulse (5 rings)
  const pulse1Rings = Array.from({ length: PULSE_CONFIG.NUM_RINGS }, (_, i) =>
    getRingPulse(i, BEATS.PULSE_1_START, 50)
  );

  // Continuous pulsing during hold phase
  const getHoldPulseRings = () => {
    if (frame < BEATS.HOLD_START) return [];

    const holdFrame = frame - BEATS.HOLD_START;
    const pulseInterval = 45; // frames between pulse cycles
    const currentPulseStart = Math.floor(holdFrame / pulseInterval) * pulseInterval;

    return Array.from({ length: 3 }, (_, i) => {
      const ringStartFrame = BEATS.HOLD_START + currentPulseStart + i * 10;
      const ringEndFrame = ringStartFrame + 40;

      if (frame < ringStartFrame || frame > ringEndFrame) {
        return { opacity: 0, scale: 0 };
      }

      const opacity = interpolate(
        frame,
        [ringStartFrame, ringStartFrame + 8, ringEndFrame],
        [0, 0.4 - i * 0.1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );

      const scale = interpolate(
        frame,
        [ringStartFrame, ringEndFrame],
        [1, 3],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );

      return { opacity, scale };
    });
  };

  const holdPulseRings = getHoldPulseRings();

  // Subtle glow pulsation on the marker itself
  const glowIntensity =
    frame >= BEATS.MARKER_APPEAR_END
      ? 8 + 4 * Math.sin((frame - BEATS.MARKER_APPEAR_END) * 0.15)
      : 8;

  const markerRadius = PULSE_CONFIG.MARKER_RADIUS;

  // Don't render before marker appears
  if (frame < BEATS.MARKER_APPEAR_START) {
    return null;
  }

  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        {/* Blue radial gradient for pulse rings */}
        <radialGradient id="crossingPulseGradient" cx="50%" cy="50%" r="50%">
          <stop offset="0%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.9" />
          <stop offset="40%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.4" />
          <stop offset="100%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0" />
        </radialGradient>

        {/* Strong blue glow filter for marker */}
        <filter id="crossingMarkerGlow" x="-200%" y="-200%" width="500%" height="500%">
          <feGaussianBlur in="SourceGraphic" stdDeviation={glowIntensity} result="blur" />
          <feColorMatrix
            in="blur"
            type="matrix"
            values="0.29 0 0 0 0
                    0.56 0 0 0 0
                    0.85 0 0 0 0
                    0 0 0 1 0"
            result="blueBlur"
          />
          <feMerge>
            <feMergeNode in="blueBlur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>

        {/* Radial burst gradient */}
        <radialGradient id="burstGradient" cx="50%" cy="50%" r="50%">
          <stop offset="0%" stopColor={COLORS.PULSE_GLOW} stopOpacity="1" />
          <stop offset="60%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.3" />
          <stop offset="100%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0" />
        </radialGradient>
      </defs>

      {/* Initial radial burst */}
      {burstOpacity > 0 && (
        <circle
          cx={x}
          cy={y}
          r={markerRadius * burstScale * 2}
          fill="url(#burstGradient)"
          opacity={burstOpacity}
        />
      )}

      {/* Pulse wave rings - first strong pulse */}
      {pulse1Rings.map((ring, i) =>
        ring.opacity > 0 ? (
          <circle
            key={`pulse1-ring-${i}`}
            cx={x}
            cy={y}
            r={markerRadius * ring.scale}
            fill="none"
            stroke={COLORS.PULSE_GLOW}
            strokeWidth={3 - i * 0.4}
            opacity={ring.opacity}
          />
        ) : null
      )}

      {/* Continuous hold pulse rings */}
      {holdPulseRings.map((ring, i) =>
        ring.opacity > 0 ? (
          <circle
            key={`hold-ring-${i}`}
            cx={x}
            cy={y}
            r={markerRadius * ring.scale}
            fill="none"
            stroke={COLORS.PULSE_GLOW}
            strokeWidth={2}
            opacity={ring.opacity}
          />
        ) : null
      )}

      {/* Outer glow ring */}
      <circle
        cx={x}
        cy={y}
        r={markerRadius * markerScale * 1.3}
        fill="none"
        stroke={COLORS.MARKER_GLOW}
        strokeWidth={4}
        opacity={0.4 * markerScale}
      />

      {/* Main white marker with blue glow */}
      <circle
        cx={x}
        cy={y}
        r={markerRadius * markerScale}
        fill={COLORS.MARKER}
        filter="url(#crossingMarkerGlow)"
        style={{
          transformOrigin: `${x}px ${y}px`,
        }}
      />

      {/* Inner blue accent */}
      <circle
        cx={x}
        cy={y}
        r={(markerRadius - 8) * markerScale}
        fill={COLORS.MARKER_GLOW}
        opacity={0.5}
      />
    </svg>
  );
};
