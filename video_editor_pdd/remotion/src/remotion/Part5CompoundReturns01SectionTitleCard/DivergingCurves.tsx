import React from 'react';
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from 'remotion';
import { CANVAS, COLORS, CURVES, TIMING } from './constants';

/**
 * Two ghost curves diverging from a shared origin:
 * - Amber curve sweeps exponentially upward (debt growth)
 * - Blue curve stays relatively flat (PDD)
 * Both drawn with stroke-dashoffset animation and subtle glow.
 */
export const DivergingCurves: React.FC = () => {
  const frame = useCurrentFrame();

  // Draw progress: easeInOut(cubic) over 60 frames
  const drawProgress = interpolate(frame, [0, TIMING.curvesDrawDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  // Pulse effect for the divergence gap (starts at frame 90 relative to component mount,
  // but since this component mounts at frame 15, the pulse starts at local frame 75)
  const pulseLocalStart = TIMING.holdStart - TIMING.curvesDrawStart; // 75
  const pulsePhase =
    frame >= pulseLocalStart
      ? interpolate(
          (frame - pulseLocalStart) % TIMING.pulseCycleFrames,
          [0, TIMING.pulseCycleFrames],
          [0, Math.PI * 2],
          { extrapolateRight: 'clamp' }
        )
      : 0;
  const pulseScale = frame >= pulseLocalStart ? 1 + 0.15 * Math.sin(pulsePhase) : 1;

  const { origin, amberEnd, blueEnd } = CURVES;

  // Amber exponential curve path (quadratic bezier with control point creating upward sweep)
  const amberCP = {
    x: origin.x + (amberEnd.x - origin.x) * 0.6,
    y: origin.y - (origin.y - amberEnd.y) * 0.15,
  };
  const amberPath = `M ${origin.x} ${origin.y} Q ${amberCP.x} ${amberCP.y} ${amberEnd.x} ${amberEnd.y}`;

  // Blue flat/declining curve path
  const blueCP = {
    x: origin.x + (blueEnd.x - origin.x) * 0.5,
    y: origin.y + (blueEnd.y - origin.y) * 0.3,
  };
  const bluePath = `M ${origin.x} ${origin.y} Q ${blueCP.x} ${blueCP.y} ${blueEnd.x} ${blueEnd.y}`;

  // Approximate path lengths for dash animation
  const amberLength = 500;
  const blueLength = 400;

  return (
    <AbsoluteFill>
      <svg
        width={CANVAS.width}
        height={CANVAS.height}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <filter id="amberGlow">
            <feGaussianBlur stdDeviation={CURVES.glowBlur} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          <filter id="blueGlow">
            <feGaussianBlur stdDeviation={CURVES.glowBlur} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Amber glow layer */}
        <path
          d={amberPath}
          fill="none"
          stroke={COLORS.amberCurve}
          strokeWidth={CURVES.strokeWidth + 4}
          opacity={CURVES.glowOpacity * pulseScale}
          strokeDasharray={amberLength}
          strokeDashoffset={amberLength * (1 - drawProgress)}
          filter="url(#amberGlow)"
        />

        {/* Amber main stroke */}
        <path
          d={amberPath}
          fill="none"
          stroke={COLORS.amberCurve}
          strokeWidth={CURVES.strokeWidth}
          opacity={CURVES.opacity * pulseScale}
          strokeDasharray={amberLength}
          strokeDashoffset={amberLength * (1 - drawProgress)}
        />

        {/* Blue glow layer */}
        <path
          d={bluePath}
          fill="none"
          stroke={COLORS.blueCurve}
          strokeWidth={CURVES.strokeWidth + 4}
          opacity={CURVES.glowOpacity * pulseScale}
          strokeDasharray={blueLength}
          strokeDashoffset={blueLength * (1 - drawProgress)}
          filter="url(#blueGlow)"
        />

        {/* Blue main stroke */}
        <path
          d={bluePath}
          fill="none"
          stroke={COLORS.blueCurve}
          strokeWidth={CURVES.strokeWidth}
          opacity={CURVES.opacity * pulseScale}
          strokeDasharray={blueLength}
          strokeDashoffset={blueLength * (1 - drawProgress)}
        />

        {/* Shared origin dot */}
        <circle
          cx={origin.x}
          cy={origin.y}
          r={CURVES.originDotRadius}
          fill={COLORS.originDot}
          opacity={CURVES.originDotOpacity * drawProgress}
        />
      </svg>
    </AbsoluteFill>
  );
};
