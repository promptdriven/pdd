import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { TIMING, COLORS } from './constants';

/**
 * Converts a hex color string (#RRGGBB) to an rgba() string at the given alpha.
 */
const hexToRgba = (hex: string, alpha: number): string => {
  const r = parseInt(hex.slice(1, 3), 16);
  const g = parseInt(hex.slice(3, 5), 16);
  const b = parseInt(hex.slice(5, 7), 16);
  return `rgba(${r},${g},${b},${alpha})`;
};

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
    [0, 0.9],
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
    [0, 0.6],
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
          color: hexToRgba(color, costOpacity),
          textShadow: `0 0 12px ${hexToRgba(color, costOpacity * 0.4)}, 0 2px 6px rgba(0,0,0,${Math.min(costOpacity * 1.2, 0.85)})`,
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
          color: hexToRgba(COLORS.SUBTITLE, subOpacity),
          textShadow: `0 1px 4px rgba(0,0,0,${Math.min(subOpacity * 2, 0.9)})`,
          zIndex: 10,
        }}
      >
        {subLabel}
      </div>
    </>
  );
};
