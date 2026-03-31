import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface ShimmerEffectProps {
  width: number;
  height: number;
  color: string;
  peakOpacity: number;
  durationFrames: number;
  startFrame: number;
}

/**
 * A horizontal wave of color that sweeps top-to-bottom over the code editor
 * during the regeneration phase.
 */
export const ShimmerEffect: React.FC<ShimmerEffectProps> = ({
  width,
  height,
  color,
  peakOpacity,
  durationFrames,
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - startFrame;

  if (relativeFrame < 0 || relativeFrame > durationFrames) {
    return null;
  }

  // Sweep progress 0..1
  const progress = interpolate(relativeFrame, [0, durationFrames], [0, 1], {
    easing: Easing.inOut(Easing.sin),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // The shimmer band is ~20% of the height
  const bandHeight = height * 0.2;
  const bandY = progress * (height + bandHeight) - bandHeight;

  // Overall fade: fade in at start and out near end
  const overallOpacity = interpolate(
    relativeFrame,
    [0, 8, durationFrames - 8, durationFrames],
    [0, 1, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width,
        height,
        overflow: 'hidden',
        pointerEvents: 'none',
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: bandY,
          left: 0,
          width,
          height: bandHeight,
          background: `linear-gradient(180deg, transparent 0%, ${color} 50%, transparent 100%)`,
          opacity: peakOpacity * overallOpacity,
        }}
      />
    </div>
  );
};

export default ShimmerEffect;
