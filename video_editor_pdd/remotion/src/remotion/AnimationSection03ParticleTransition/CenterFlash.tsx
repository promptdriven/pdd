import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, FLASH } from './constants';

export const CenterFlash: React.FC = () => {
  const frame = useCurrentFrame();

  // Flash ramps up then rapidly decays
  const opacity = frame <= FLASH.peakFrame
    ? interpolate(
        frame,
        [FLASH.startFrame, FLASH.peakFrame],
        [0, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : interpolate(
        frame,
        [FLASH.peakFrame, FLASH.endFrame],
        [1, 0],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.exp),
        }
      );

  const radius = interpolate(
    frame,
    [FLASH.startFrame, FLASH.peakFrame],
    [4, FLASH.maxRadius],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (frame < FLASH.startFrame || frame > FLASH.endFrame) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - radius,
        top: CANVAS.centerY - radius,
        width: radius * 2,
        height: radius * 2,
        borderRadius: '50%',
        backgroundColor: COLORS.flashColor,
        opacity,
        boxShadow: `0 0 ${radius * 3}px ${radius}px rgba(255,255,255,0.8)`,
      }}
    />
  );
};
