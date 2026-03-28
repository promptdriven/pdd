import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface GlowPulseProps {
  text: string;
  fontSize: number;
  fontWeight: number;
  glowColor: string;
  glowOpacity: number;
  glowBlur: number;
  pulseStart: number;
  pulseDuration: number;
  y: number;
}

export const GlowPulse: React.FC<GlowPulseProps> = ({
  text,
  fontSize,
  fontWeight,
  glowColor,
  glowOpacity,
  glowBlur,
  pulseStart,
  pulseDuration,
  y,
}) => {
  const frame = useCurrentFrame();

  // Pulse rises then falls over the duration
  const halfDuration = pulseDuration / 2;
  const pulseIntensity = interpolate(
    frame,
    [
      pulseStart,
      pulseStart + halfDuration,
      pulseStart + pulseDuration,
    ],
    [0, 1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  const currentOpacity = glowOpacity * pulseIntensity;

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 0,
        width: '100%',
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        transform: 'translateY(-50%)',
        pointerEvents: 'none',
      }}
    >
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize,
          fontWeight,
          color: 'transparent',
          textShadow: `0 0 ${glowBlur}px ${glowColor}`,
          opacity: currentOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        {text}
      </span>
    </div>
  );
};

export default GlowPulse;
