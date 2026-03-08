import React from 'react';
import { interpolate, useCurrentFrame, spring, useVideoConfig, Easing } from 'remotion';
import { LAYOUT, COLORS, TYPOGRAPHY } from './constants';

interface SavingsCalloutProps {
  x: number;
  y: number;
  text: string;
  pulseStart: number;
}

export const SavingsCallout: React.FC<SavingsCalloutProps> = ({
  x,
  y,
  text,
  pulseStart,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Spring animation for entrance
  const springValue = spring({
    frame,
    fps,
    config: {
      damping: 12,
      stiffness: 150,
    },
  });

  const offsetY = interpolate(springValue, [0, 1], [200, 0]);
  const opacity = interpolate(springValue, [0, 1], [0, 1]);

  // Pulse animation after entrance
  const pulseFrame = Math.max(0, frame - pulseStart);
  const pulseProgress = (pulseFrame % (fps * 0.5)) / (fps * 0.5);
  const pulseScale = interpolate(
    pulseProgress,
    [0, 0.5, 1],
    [1.0, 1.05, 1.0],
    {
      easing: Easing.inOut(Easing.sin),
    }
  );

  const scale = frame >= pulseStart ? pulseScale : 1.0;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - LAYOUT.savingsCallout.width / 2,
        top: y + offsetY,
        width: LAYOUT.savingsCallout.width,
        height: LAYOUT.savingsCallout.height,
        background: `radial-gradient(circle, ${COLORS.savingsGradient.start} 0%, ${COLORS.savingsGradient.end} 100%)`,
        border: `${LAYOUT.savingsCallout.borderWidth}px solid ${COLORS.white}`,
        borderRadius: 16,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'center',
        opacity,
        transform: `scale(${scale})`,
        boxShadow: '0 8px 32px rgba(16, 185, 129, 0.5)',
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.savings.family,
          fontWeight: TYPOGRAPHY.savings.weight,
          fontSize: TYPOGRAPHY.savings.size,
          color: COLORS.white,
          textShadow: '0 2px 8px rgba(0,0,0,0.3)',
        }}
      >
        {text}
      </span>
      <span
        style={{
          fontFamily: TYPOGRAPHY.descriptor.family,
          fontWeight: TYPOGRAPHY.descriptor.weight,
          fontSize: TYPOGRAPHY.descriptor.size,
          color: COLORS.descriptor,
          marginTop: 4,
        }}
      >
        vs. Traditional Video
      </span>
    </div>
  );
};
