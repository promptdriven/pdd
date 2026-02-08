import React from "react";
import { interpolate, spring, useCurrentFrame, useVideoConfig } from "remotion";
import { BEATS, COLORS, FIRST_CROSSING_PULSE_CONFIG } from "./constants";

interface FirstCrossingMarkerProps {
  x: number;
  y: number;
}

/**
 * Modest crossing marker for the first crossing point where the generate line
 * crosses below the dashed "total cost" line. Uses fewer/smaller pulse rings
 * and a smaller marker compared to the dramatic second crossing.
 */
export const FirstCrossingMarker: React.FC<FirstCrossingMarkerProps> = ({ x, y }) => {
  const frame = useCurrentFrame();
  const { fps, width, height } = useVideoConfig();

  const config = FIRST_CROSSING_PULSE_CONFIG;

  // Marker appears with spring animation at FIRST_CROSSING_START
  const markerFrame = Math.max(0, frame - BEATS.FIRST_CROSSING_START);
  const markerScale = spring({
    frame: markerFrame,
    fps,
    config: {
      damping: 15,
      stiffness: 100,
    },
  });

  // Brief burst effect
  const burstOpacity = interpolate(
    frame,
    [BEATS.FIRST_CROSSING_START, BEATS.FIRST_CROSSING_START + 8, BEATS.FIRST_CROSSING_END],
    [0, 0.5, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const burstScale = interpolate(
    frame,
    [BEATS.FIRST_CROSSING_START, BEATS.FIRST_CROSSING_END],
    [0.5, 2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Concentric ring pulse helper - modest version
  const getRingPulse = (ringIndex: number) => {
    const ringStartFrame = BEATS.FIRST_CROSSING_START + ringIndex * config.RING_STAGGER;
    const ringEndFrame = ringStartFrame + 25;

    if (frame < ringStartFrame || frame > ringEndFrame + 10) {
      return { opacity: 0, scale: 0 };
    }

    const opacity = interpolate(
      frame,
      [ringStartFrame, ringStartFrame + 8, ringEndFrame],
      [0, 0.4 - ringIndex * 0.1, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );

    const scale = interpolate(
      frame,
      [ringStartFrame, ringEndFrame],
      [1, config.MAX_SCALE],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );

    return { opacity, scale };
  };

  // Pulse rings
  const pulseRings = Array.from({ length: config.NUM_RINGS }, (_, i) =>
    getRingPulse(i)
  );

  // Subtle glow
  const glowIntensity =
    frame >= BEATS.FIRST_CROSSING_END
      ? 4 + 2 * Math.sin((frame - BEATS.FIRST_CROSSING_END) * 0.12)
      : 4;

  const markerRadius = config.MARKER_RADIUS;

  // Don't render before first crossing
  if (frame < BEATS.FIRST_CROSSING_START) {
    return null;
  }

  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        <radialGradient id="firstCrossingBurstGradient" cx="50%" cy="50%" r="50%">
          <stop offset="0%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.7" />
          <stop offset="60%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.2" />
          <stop offset="100%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0" />
        </radialGradient>

        <filter id="firstCrossingGlow" x="-200%" y="-200%" width="500%" height="500%">
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
      </defs>

      {/* Initial burst - modest */}
      {burstOpacity > 0 && (
        <circle
          cx={x}
          cy={y}
          r={markerRadius * burstScale * 1.5}
          fill="url(#firstCrossingBurstGradient)"
          opacity={burstOpacity}
        />
      )}

      {/* Pulse rings - fewer and smaller */}
      {pulseRings.map((ring, i) =>
        ring.opacity > 0 ? (
          <circle
            key={`first-crossing-ring-${i}`}
            cx={x}
            cy={y}
            r={markerRadius * ring.scale}
            fill="none"
            stroke={COLORS.PULSE_GLOW}
            strokeWidth={2 - i * 0.3}
            opacity={ring.opacity}
          />
        ) : null
      )}

      {/* Outer glow ring */}
      <circle
        cx={x}
        cy={y}
        r={markerRadius * markerScale * 1.2}
        fill="none"
        stroke={COLORS.MARKER_GLOW}
        strokeWidth={2}
        opacity={0.3 * markerScale}
      />

      {/* Main white marker with blue glow - smaller than second crossing */}
      <circle
        cx={x}
        cy={y}
        r={markerRadius * markerScale}
        fill={COLORS.MARKER}
        filter="url(#firstCrossingGlow)"
        style={{
          transformOrigin: `${x}px ${y}px`,
        }}
      />

      {/* Inner blue accent */}
      <circle
        cx={x}
        cy={y}
        r={(markerRadius - 6) * markerScale}
        fill={COLORS.MARKER_GLOW}
        opacity={0.4}
      />
    </svg>
  );
};
