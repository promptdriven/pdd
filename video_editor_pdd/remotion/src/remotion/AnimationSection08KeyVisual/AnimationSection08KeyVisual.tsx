import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, BARS, DIMENSIONS, TIMING, TYPOGRAPHY } from './constants';
import { AnimatedBar } from './AnimatedBar';
import { useVisualContractData } from '../_shared/visual-runtime';

type KeyVisualContract = {
  bars?: Array<{ height?: number; color?: string }>;
  barWidth?: number;
  barGap?: number;
  maxHeight?: number;
};

export const defaultAnimationSection08KeyVisualProps = {};

export const AnimationSection08KeyVisual: React.FC = () => {
  const contract = useVisualContractData<KeyVisualContract>();
  const bars = Array.isArray(contract?.bars) && contract?.bars.length
    ? contract.bars.map((bar, index) => ({
        maxHeight: typeof bar?.height === 'number' ? bar.height : BARS[index]?.maxHeight ?? 0,
        color: typeof bar?.color === 'string' ? bar.color : BARS[index]?.color ?? COLORS.cyan,
      }))
    : BARS;
  const barGap = typeof contract?.barGap === 'number' ? contract.barGap : DIMENSIONS.barGap;
  const maxHeight = typeof contract?.maxHeight === 'number' ? contract.maxHeight : 500;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        justifyContent: 'flex-end',
        alignItems: 'center',
      }}
    >
      {/* Heading */}
      <div
        style={{
          position: 'absolute',
          top: TYPOGRAPHY.headingY,
          left: TYPOGRAPHY.headingX,
          color: COLORS.heading,
          fontSize: TYPOGRAPHY.headingSize,
          fontWeight: TYPOGRAPHY.headingWeight,
          fontFamily: TYPOGRAPHY.fontFamily,
        }}
      >
        Key Visual
      </div>

      {/* Bar chart container */}
      <div
        style={{
          position: 'absolute',
          left: '50%',
          bottom: 200,
          transform: 'translateX(-50%)',
          display: 'flex',
          gap: barGap,
          alignItems: 'flex-end',
          height: maxHeight,
        }}
      >
        {bars.map((bar, index) => (
          <AnimatedBar
            key={index}
            targetHeight={bar.maxHeight}
            delay={index * TIMING.barStaggerDelay}
            color={bar.color}
          />
        ))}
      </div>
    </AbsoluteFill>
  );
};

export default AnimationSection08KeyVisual;
