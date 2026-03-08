import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { CANVAS, CENTRAL_DOT } from './constants';

export const PulsingDot: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in over first 15 frames
  const opacity = interpolate(frame, [0, CENTRAL_DOT.fadeInEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Heartbeat pulse: looping scale between minScale and maxScale
  // Use a sine-based loop for smooth heartbeat rhythm
  const pulsePhase = (frame % 30) / 30; // 1-second loop at 30fps
  const pulseT = interpolate(
    Math.sin(pulsePhase * 2 * Math.PI),
    [-1, 1],
    [CENTRAL_DOT.minScale, CENTRAL_DOT.maxScale]
  );

  const diameter = CENTRAL_DOT.baseRadius * 2 * pulseT;
  const glowSize = CENTRAL_DOT.glowRadius * pulseT;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - diameter / 2,
        top: CANVAS.centerY - diameter / 2,
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        backgroundColor: CENTRAL_DOT.color,
        opacity,
        boxShadow: `0 0 ${glowSize}px ${glowSize / 2}px ${CENTRAL_DOT.color}`,
      }}
    />
  );
};
