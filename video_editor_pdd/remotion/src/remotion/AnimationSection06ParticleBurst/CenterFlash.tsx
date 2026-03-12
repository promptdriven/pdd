import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FLASH_CONFIG, TIMING, CANVAS } from './constants';

export const CenterFlash: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, TIMING.flashEnd],
    [FLASH_CONFIG.opacity, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.exp),
    }
  );

  const scale = interpolate(
    frame,
    [0, TIMING.flashEnd],
    [1, 2.5],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.exp),
    }
  );

  if (frame > TIMING.flashEnd + 2) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.width / 2 - FLASH_CONFIG.size / 2,
        top: CANVAS.height / 2 - FLASH_CONFIG.size / 2,
        width: FLASH_CONFIG.size,
        height: FLASH_CONFIG.size,
        borderRadius: '50%',
        backgroundColor: COLORS.flash,
        opacity,
        transform: `scale(${scale})`,
        boxShadow: `0 0 ${FLASH_CONFIG.size}px ${FLASH_CONFIG.size / 2}px rgba(255,255,255,${opacity * 0.5})`,
      }}
    />
  );
};
