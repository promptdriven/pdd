import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  PROMPT_COLOR,
  PROMPT_X,
  PROMPT_Y,
  PROMPT_WIDTH,
  PROMPT_HEIGHT,
  PROMPT_FADE_IN_END,
  PROMPT_PULSE_CYCLE,
} from './constants';

/**
 * Glowing document labeled "PROMPT" at center-top.
 * Fades in over first 30 frames, then pulses on a 45-frame cycle.
 */
export const PulsingDocument: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: 0→1 over 30 frames (easeOut cubic)
  const opacity = interpolate(frame, [0, PROMPT_FADE_IN_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Pulse glow: sinusoidal on 45-frame cycle (only after fade-in)
  const pulsePhase = ((frame % PROMPT_PULSE_CYCLE) / PROMPT_PULSE_CYCLE) * Math.PI * 2;
  const pulseIntensity = 0.5 + 0.5 * Math.sin(pulsePhase); // 0..1
  const glowBlur = 20 + pulseIntensity * 20; // 20..40px
  const glowOpacity = 0.15 + pulseIntensity * 0.15; // 0.15..0.30

  return (
    <div
      style={{
        position: 'absolute',
        left: PROMPT_X - PROMPT_WIDTH / 2,
        top: PROMPT_Y,
        width: PROMPT_WIDTH,
        height: PROMPT_HEIGHT,
        opacity,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
      }}
    >
      {/* Outer glow */}
      <div
        style={{
          position: 'absolute',
          inset: -10,
          borderRadius: 16,
          background: PROMPT_COLOR,
          opacity: glowOpacity,
          filter: `blur(${glowBlur}px)`,
        }}
      />

      {/* Document body */}
      <div
        style={{
          position: 'relative',
          width: '100%',
          height: '100%',
          borderRadius: 12,
          border: `2px solid ${PROMPT_COLOR}`,
          backgroundColor: `${PROMPT_COLOR}1A`, // ~0.1 alpha
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
        }}
      >
        {/* Document icon lines (decorative) */}
        <div
          style={{
            position: 'absolute',
            top: 14,
            left: 20,
            display: 'flex',
            flexDirection: 'column',
            gap: 4,
          }}
        >
          {[40, 30, 35].map((w, i) => (
            <div
              key={i}
              style={{
                width: w,
                height: 2,
                borderRadius: 1,
                backgroundColor: PROMPT_COLOR,
                opacity: 0.3,
              }}
            />
          ))}
        </div>

        {/* Label */}
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 16,
            fontWeight: 700,
            color: PROMPT_COLOR,
            letterSpacing: 2,
            zIndex: 1,
          }}
        >
          PROMPT
        </span>
      </div>
    </div>
  );
};

export default PulsingDocument;
