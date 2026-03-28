import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface PulsingGlowProps {
  cx: number;
  cy: number;
  radius: number;
  color: string;
  minOpacity: number;
  maxOpacity: number;
  cycleFrames: number;
  startFrame: number;
}

export const PulsingGlow: React.FC<PulsingGlowProps> = ({
  cx,
  cy,
  radius,
  color,
  minOpacity,
  maxOpacity,
  cycleFrames,
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const elapsed = frame - startFrame;

  if (elapsed < 0) return null;

  // Determine pulse intensity: second pulse (frame 90-150 relative to pulse start)
  // is brighter per spec
  const isSecondPulsePhase = elapsed >= 60 && elapsed < 120;
  const effectiveMax = isSecondPulsePhase ? maxOpacity * 1.5 : maxOpacity;

  // Sine-based pulse on cycleFrames period
  const cycleProgress = (elapsed % cycleFrames) / cycleFrames;
  const pulseOpacity = interpolate(
    cycleProgress,
    [0, 0.5, 1],
    [minOpacity, effectiveMax, minOpacity],
    {
      easing: Easing.inOut(Easing.sin),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: cx - radius * 2,
        top: cy - radius * 2,
        width: radius * 4,
        height: radius * 4,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${color} 0%, transparent 70%)`,
        opacity: pulseOpacity,
        pointerEvents: 'none',
      }}
    />
  );
};

export default PulsingGlow;
