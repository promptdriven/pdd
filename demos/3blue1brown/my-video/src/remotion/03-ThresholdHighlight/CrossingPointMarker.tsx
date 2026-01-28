import React from "react";
import { interpolate, spring, useCurrentFrame, useVideoConfig } from "remotion";
import { BEATS, COLORS } from "./constants";

interface CrossingPointMarkerProps {
  x: number;
  y: number;
}

export const CrossingPointMarker: React.FC<CrossingPointMarkerProps> = ({
  x,
  y,
}) => {
  const frame = useCurrentFrame();
  const { fps, width, height } = useVideoConfig();

  // Circle grows in with spring animation
  const markerScale = spring({
    frame,
    fps,
    config: {
      damping: 15,
      stiffness: 100,
    },
  });

  // Pulse wave animation helper
  const getPulseOpacity = (startFrame: number, endFrame: number) => {
    if (frame < startFrame || frame > endFrame + 30) return 0;
    return interpolate(
      frame,
      [startFrame, startFrame + 15, endFrame],
      [0, 0.6, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
  };

  const getPulseScale = (startFrame: number, endFrame: number) => {
    if (frame < startFrame) return 0;
    return interpolate(
      frame,
      [startFrame, endFrame],
      [1, 4],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
  };

  // Three distinct pulses
  const pulse1Opacity = getPulseOpacity(BEATS.PULSE_1_START, BEATS.PULSE_1_END);
  const pulse1Scale = getPulseScale(BEATS.PULSE_1_START, BEATS.PULSE_1_END);

  const pulse2Opacity = getPulseOpacity(BEATS.PULSE_2_START, BEATS.PULSE_2_END);
  const pulse2Scale = getPulseScale(BEATS.PULSE_2_START, BEATS.PULSE_2_END);

  const pulse3Opacity = getPulseOpacity(BEATS.PULSE_3_START, BEATS.PULSE_3_END);
  const pulse3Scale = getPulseScale(BEATS.PULSE_3_START, BEATS.PULSE_3_END);

  // Subtle continuous pulse during hold phase
  const holdPulseOpacity =
    frame >= BEATS.HOLD_START
      ? 0.2 + 0.1 * Math.sin((frame - BEATS.HOLD_START) * 0.1)
      : 0;

  const markerRadius = 20;

  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        {/* Radial gradient for pulse effect */}
        <radialGradient id="pulseGradient" cx="50%" cy="50%" r="50%">
          <stop offset="0%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.8" />
          <stop offset="50%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.3" />
          <stop offset="100%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0" />
        </radialGradient>

        {/* Glow filter for marker */}
        <filter id="markerGlow" x="-100%" y="-100%" width="300%" height="300%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="8" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Pulse wave 1 */}
      {pulse1Opacity > 0 && (
        <circle
          cx={x}
          cy={y}
          r={markerRadius * pulse1Scale}
          fill="url(#pulseGradient)"
          opacity={pulse1Opacity}
        />
      )}

      {/* Pulse wave 2 */}
      {pulse2Opacity > 0 && (
        <circle
          cx={x}
          cy={y}
          r={markerRadius * pulse2Scale}
          fill="url(#pulseGradient)"
          opacity={pulse2Opacity}
        />
      )}

      {/* Pulse wave 3 */}
      {pulse3Opacity > 0 && (
        <circle
          cx={x}
          cy={y}
          r={markerRadius * pulse3Scale}
          fill="url(#pulseGradient)"
          opacity={pulse3Opacity}
        />
      )}

      {/* Subtle hold pulse */}
      {frame >= BEATS.HOLD_START && (
        <circle
          cx={x}
          cy={y}
          r={markerRadius * 2}
          fill="url(#pulseGradient)"
          opacity={holdPulseOpacity}
        />
      )}

      {/* Main marker with glow */}
      <circle
        cx={x}
        cy={y}
        r={markerRadius * markerScale}
        fill={COLORS.MARKER}
        filter="url(#markerGlow)"
        style={{
          transformOrigin: `${x}px ${y}px`,
        }}
      />

      {/* Inner accent */}
      <circle
        cx={x}
        cy={y}
        r={(markerRadius - 6) * markerScale}
        fill={COLORS.PULSE_GLOW}
        opacity={0.6}
      />
    </svg>
  );
};
