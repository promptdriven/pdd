import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, ANIM } from './constants';

export const SummaryLine: React.FC = () => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - ANIM.summary.start;

  // Slide up from y+20 over 25 frames
  const slideY = interpolate(
    relativeFrame,
    [0, ANIM.summary.slideDuration],
    [20, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const opacity = interpolate(
    relativeFrame,
    [0, ANIM.summary.slideDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  if (relativeFrame < 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: 700,
        left: 0,
        right: 0,
        display: 'flex',
        justifyContent: 'center',
        transform: `translateY(${slideY}px)`,
        opacity,
      }}
    >
      <div
        style={{
          backgroundColor: `rgba(30, 41, 59, 0.25)`,
          borderRadius: 10,
          padding: '16px 32px',
          display: 'inline-flex',
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 20,
            fontWeight: 600,
            lineHeight: 1.4,
          }}
        >
          <span style={{ color: COLORS.text }}>One side compounds </span>
          <span style={{ color: COLORS.patching }}>against you</span>
          <span style={{ color: COLORS.text }}>. The other compounds </span>
          <span style={{ color: COLORS.pdd }}>for you</span>
          <span style={{ color: COLORS.text }}>.</span>
        </span>
      </div>
    </div>
  );
};

export default SummaryLine;
