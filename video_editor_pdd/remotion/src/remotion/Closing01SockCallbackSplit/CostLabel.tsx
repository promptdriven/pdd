import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { TIMING, COLORS } from './constants';

interface CostLabelProps {
  cost: string;
  subLabel: string;
  color: string;
  centerX: number;
}

export const CostLabel: React.FC<CostLabelProps> = ({
  cost,
  subLabel,
  color,
  centerX,
}) => {
  const frame = useCurrentFrame();

  const costOpacity = interpolate(
    frame,
    [TIMING.COST_LABEL_START, TIMING.COST_LABEL_START + TIMING.COST_LABEL_DURATION],
    [0, 0.7],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const subStart = TIMING.COST_LABEL_START + TIMING.SUB_LABEL_DELAY;
  const subOpacity = interpolate(
    frame,
    [subStart, subStart + TIMING.SUB_LABEL_DURATION],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <>
      <div
        style={{
          position: 'absolute',
          left: centerX - 100,
          top: 960,
          width: 200,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 28,
          fontWeight: 700,
          color,
          opacity: costOpacity,
          zIndex: 10,
        }}
      >
        {cost}
      </div>
      <div
        style={{
          position: 'absolute',
          left: centerX - 100,
          top: 990,
          width: 200,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          color: COLORS.SUBTITLE,
          opacity: subOpacity,
          zIndex: 10,
        }}
      >
        {subLabel}
      </div>
    </>
  );
};
